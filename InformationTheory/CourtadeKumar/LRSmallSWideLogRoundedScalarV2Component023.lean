import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch6
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

private noncomputable def leaf960Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (1/16), chiHi := (9/128) }

private noncomputable def leaf960Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217827/134217728) }, vSqrt := { lower := (32765/32768), upper := (33554496/33554063) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (155155103/134217728) }, upper := { exponent := 0, mantissa := (2417/2048) } }, logOuter := sk89LogOuterCertificate, logK := sk89LogKCertificate, logChi := chi125LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (67108559/67108126) } }, logDArg := sk89LogDArgCertificate }

private noncomputable def leaf960InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf960LocalValidity :
    LeafFacts leaf960Box leaf960Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf960Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (33554496/33554063) }) = true
      norm_num [leaf960Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf960CertificateValid :
    WideCertificateValid leaf960Box leaf960Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk89ValidityFacts chi125ValidityFacts
    leaf960LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf960CoverageChecked :
    coverageCheck (innerAD leaf960Box) leaf960InnerLog = true := by
  rfl'

private theorem leaf960InnerLogValid :
    leaf960InnerLog.Valid 8 (innerAD leaf960Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf960CoverageChecked

private noncomputable def leaf960InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629189/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf960InputLogOnePlusV_eq :
    leaf960InputLogOnePlusV = outerEnclosure 24
      (leaf960Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf960RoundedFacts : LeafRoundedFacts 8
    leaf960Certificate.logOnePlusV leaf960InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf960InputLogOnePlusV_eq }

private noncomputable def leaf960Inputs : Inputs :=
  inputsOfCaches globalInput sk89RoundedInputs
    chi125InputQChi innerPair2Input
    leaf960InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf960LowerChecked :
    lowerCheck 24 leaf960Box leaf960Inputs = true := by
  rfl'

private theorem leaf960CoversExact : CoversExact 8
    leaf960Box leaf960Certificate leaf960InnerLog leaf960Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk89RoundedFacts chi125RoundedFacts
    innerPair2RoundedFacts leaf960RoundedFacts (by rfl)

private theorem leaf960FlatSound : Sound leaf960Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf960CertificateValid
    leaf960InnerLogValid leaf960CoversExact leaf960LowerChecked

private noncomputable def leaf961Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (1/16), chiHi := (9/128) }

private noncomputable def leaf961Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217829/134217728) }, vSqrt := { lower := (32765/32768), upper := (16777248/16777027) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (155679357/134217728) }, upper := { exponent := 0, mantissa := (1213/1024) } }, logOuter := sk90LogOuterCertificate, logK := sk90LogKCertificate, logChi := chi125LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (33554275/33554054) } }, logDArg := sk90LogDArgCertificate }

private noncomputable def leaf961InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf961LocalValidity :
    LeafFacts leaf961Box leaf961Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf961Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (16777248/16777027) }) = true
      norm_num [leaf961Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf961CertificateValid :
    WideCertificateValid leaf961Box leaf961Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk90ValidityFacts chi125ValidityFacts
    leaf961LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf961CoverageChecked :
    coverageCheck (innerAD leaf961Box) leaf961InnerLog = true := by
  rfl'

private theorem leaf961InnerLogValid :
    leaf961InnerLog.Valid 8 (innerAD leaf961Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf961CoverageChecked

private noncomputable def leaf961InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629191/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf961InputLogOnePlusV_eq :
    leaf961InputLogOnePlusV = outerEnclosure 24
      (leaf961Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf961RoundedFacts : LeafRoundedFacts 8
    leaf961Certificate.logOnePlusV leaf961InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf961InputLogOnePlusV_eq }

private noncomputable def leaf961Inputs : Inputs :=
  inputsOfCaches globalInput sk90RoundedInputs
    chi125InputQChi innerPair2Input
    leaf961InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf961LowerChecked :
    lowerCheck 24 leaf961Box leaf961Inputs = true := by
  rfl'

private theorem leaf961CoversExact : CoversExact 8
    leaf961Box leaf961Certificate leaf961InnerLog leaf961Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk90RoundedFacts chi125RoundedFacts
    innerPair2RoundedFacts leaf961RoundedFacts (by rfl)

private theorem leaf961FlatSound : Sound leaf961Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf961CertificateValid
    leaf961InnerLogValid leaf961CoversExact leaf961LowerChecked

private noncomputable def leaf962Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (9/128), chiHi := (5/64) }

private noncomputable def leaf962Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217829/134217728) }, vSqrt := { lower := (32765/32768), upper := (5592416/5592337) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (157776381/134217728) }, upper := { exponent := 0, mantissa := (1229/1024) } }, logOuter := sk89LogOuterCertificate, logK := sk89LogKCertificate, logChi := chi126LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (11184753/11184674) } }, logDArg := sk89LogDArgCertificate }

private noncomputable def leaf962InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf962LocalValidity :
    LeafFacts leaf962Box leaf962Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf962Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (5592416/5592337) }) = true
      norm_num [leaf962Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf962CertificateValid :
    WideCertificateValid leaf962Box leaf962Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk89ValidityFacts chi126ValidityFacts
    leaf962LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf962CoverageChecked :
    coverageCheck (innerAD leaf962Box) leaf962InnerLog = true := by
  rfl'

private theorem leaf962InnerLogValid :
    leaf962InnerLog.Valid 8 (innerAD leaf962Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf962CoverageChecked

private noncomputable def leaf962InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629199/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf962InputLogOnePlusV_eq :
    leaf962InputLogOnePlusV = outerEnclosure 24
      (leaf962Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf962RoundedFacts : LeafRoundedFacts 8
    leaf962Certificate.logOnePlusV leaf962InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf962InputLogOnePlusV_eq }

private noncomputable def leaf962Inputs : Inputs :=
  inputsOfCaches globalInput sk89RoundedInputs
    chi126InputQChi innerPair3Input
    leaf962InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf962LowerChecked :
    lowerCheck 24 leaf962Box leaf962Inputs = true := by
  rfl'

private theorem leaf962CoversExact : CoversExact 8
    leaf962Box leaf962Certificate leaf962InnerLog leaf962Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk89RoundedFacts chi126RoundedFacts
    innerPair3RoundedFacts leaf962RoundedFacts (by rfl)

private theorem leaf962FlatSound : Sound leaf962Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf962CertificateValid
    leaf962InnerLogValid leaf962CoversExact leaf962LowerChecked

private noncomputable def leaf963Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (9/128), chiHi := (5/64) }

private noncomputable def leaf963Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217831/134217728) }, vSqrt := { lower := (32765/32768), upper := (8388624/8388503) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (158366167/134217728) }, upper := { exponent := 0, mantissa := (617/512) } }, logOuter := sk90LogOuterCertificate, logK := sk90LogKCertificate, logChi := chi126LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (16777127/16777006) } }, logDArg := sk90LogDArgCertificate }

private noncomputable def leaf963InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf963LocalValidity :
    LeafFacts leaf963Box leaf963Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf963Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8388624/8388503) }) = true
      norm_num [leaf963Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf963CertificateValid :
    WideCertificateValid leaf963Box leaf963Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk90ValidityFacts chi126ValidityFacts
    leaf963LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf963CoverageChecked :
    coverageCheck (innerAD leaf963Box) leaf963InnerLog = true := by
  rfl'

private theorem leaf963InnerLogValid :
    leaf963InnerLog.Valid 8 (innerAD leaf963Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf963CoverageChecked

private noncomputable def leaf963InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814601/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf963InputLogOnePlusV_eq :
    leaf963InputLogOnePlusV = outerEnclosure 24
      (leaf963Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf963RoundedFacts : LeafRoundedFacts 8
    leaf963Certificate.logOnePlusV leaf963InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf963InputLogOnePlusV_eq }

private noncomputable def leaf963Inputs : Inputs :=
  inputsOfCaches globalInput sk90RoundedInputs
    chi126InputQChi innerPair3Input
    leaf963InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf963LowerChecked :
    lowerCheck 24 leaf963Box leaf963Inputs = true := by
  rfl'

private theorem leaf963CoversExact : CoversExact 8
    leaf963Box leaf963Certificate leaf963InnerLog leaf963Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk90RoundedFacts chi126RoundedFacts
    innerPair3RoundedFacts leaf963RoundedFacts (by rfl)

private theorem leaf963FlatSound : Sound leaf963Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf963CertificateValid
    leaf963InnerLogValid leaf963CoversExact leaf963LowerChecked

private noncomputable def leaf964Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (5/64), chiHi := (11/128) }

private noncomputable def leaf964Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217831/134217728) }, vSqrt := { lower := (32765/32768), upper := (33554496/33553981) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (160397659/134217728) }, upper := { exponent := 0, mantissa := (2499/2048) } }, logOuter := sk89LogOuterCertificate, logK := sk89LogKCertificate, logChi := chi103LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (67108477/67107962) } }, logDArg := sk89LogDArgCertificate }

private noncomputable def leaf964InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf964LocalValidity :
    LeafFacts leaf964Box leaf964Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf964Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (33554496/33553981) }) = true
      norm_num [leaf964Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf964CertificateValid :
    WideCertificateValid leaf964Box leaf964Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk89ValidityFacts chi103ValidityFacts
    leaf964LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf964CoverageChecked :
    coverageCheck (innerAD leaf964Box) leaf964InnerLog = true := by
  rfl'

private theorem leaf964InnerLogValid :
    leaf964InnerLog.Valid 8 (innerAD leaf964Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf964CoverageChecked

private noncomputable def leaf964InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629209/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf964InputLogOnePlusV_eq :
    leaf964InputLogOnePlusV = outerEnclosure 24
      (leaf964Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf964RoundedFacts : LeafRoundedFacts 8
    leaf964Certificate.logOnePlusV leaf964InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf964InputLogOnePlusV_eq }

private noncomputable def leaf964Inputs : Inputs :=
  inputsOfCaches globalInput sk89RoundedInputs
    chi103InputQChi innerPair12Input
    leaf964InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf964LowerChecked :
    lowerCheck 24 leaf964Box leaf964Inputs = true := by
  rfl'

private theorem leaf964CoversExact : CoversExact 8
    leaf964Box leaf964Certificate leaf964InnerLog leaf964Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk89RoundedFacts chi103RoundedFacts
    innerPair12RoundedFacts leaf964RoundedFacts (by rfl)

private theorem leaf964FlatSound : Sound leaf964Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf964CertificateValid
    leaf964InnerLogValid leaf964CoversExact leaf964LowerChecked

private noncomputable def leaf965Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (11/128), chiHi := (3/32) }

private noncomputable def leaf965Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217833/134217728) }, vSqrt := { lower := (32765/32768), upper := (8388624/8388485) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (163018937/134217728) }, upper := { exponent := 0, mantissa := (635/512) } }, logOuter := sk89LogOuterCertificate, logK := sk89LogKCertificate, logChi := chi104LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (16777109/16776970) } }, logDArg := sk89LogDArgCertificate }

private noncomputable def leaf965InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf965LocalValidity :
    LeafFacts leaf965Box leaf965Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf965Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8388624/8388485) }) = true
      norm_num [leaf965Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf965CertificateValid :
    WideCertificateValid leaf965Box leaf965Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk89ValidityFacts chi104ValidityFacts
    leaf965LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf965CoverageChecked :
    coverageCheck (innerAD leaf965Box) leaf965InnerLog = true := by
  rfl'

private theorem leaf965InnerLogValid :
    leaf965InnerLog.Valid 8 (innerAD leaf965Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf965CoverageChecked

private noncomputable def leaf965InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907305/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf965InputLogOnePlusV_eq :
    leaf965InputLogOnePlusV = outerEnclosure 24
      (leaf965Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf965RoundedFacts : LeafRoundedFacts 8
    leaf965Certificate.logOnePlusV leaf965InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf965InputLogOnePlusV_eq }

private noncomputable def leaf965Inputs : Inputs :=
  inputsOfCaches globalInput sk89RoundedInputs
    chi104InputQChi innerPair12Input
    leaf965InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf965LowerChecked :
    lowerCheck 24 leaf965Box leaf965Inputs = true := by
  rfl'

private theorem leaf965CoversExact : CoversExact 8
    leaf965Box leaf965Certificate leaf965InnerLog leaf965Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk89RoundedFacts chi104RoundedFacts
    innerPair12RoundedFacts leaf965RoundedFacts (by rfl)

private theorem leaf965FlatSound : Sound leaf965Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf965CertificateValid
    leaf965InnerLogValid leaf965CoversExact leaf965LowerChecked

private noncomputable def leaf966Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (5/64), chiHi := (11/128) }

private noncomputable def leaf966Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217833/134217728) }, vSqrt := { lower := (32765/32768), upper := (16777248/16776985) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (161052977/134217728) }, upper := { exponent := 0, mantissa := (1255/1024) } }, logOuter := sk90LogOuterCertificate, logK := sk90LogKCertificate, logChi := chi103LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (33554233/33553970) } }, logDArg := sk90LogDArgCertificate }

private noncomputable def leaf966InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf966LocalValidity :
    LeafFacts leaf966Box leaf966Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf966Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (16777248/16776985) }) = true
      norm_num [leaf966Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf966CertificateValid :
    WideCertificateValid leaf966Box leaf966Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk90ValidityFacts chi103ValidityFacts
    leaf966LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf966CoverageChecked :
    coverageCheck (innerAD leaf966Box) leaf966InnerLog = true := by
  rfl'

private theorem leaf966InnerLogValid :
    leaf966InnerLog.Valid 8 (innerAD leaf966Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf966CoverageChecked

private noncomputable def leaf966InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907303/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf966InputLogOnePlusV_eq :
    leaf966InputLogOnePlusV = outerEnclosure 24
      (leaf966Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf966RoundedFacts : LeafRoundedFacts 8
    leaf966Certificate.logOnePlusV leaf966InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf966InputLogOnePlusV_eq }

private noncomputable def leaf966Inputs : Inputs :=
  inputsOfCaches globalInput sk90RoundedInputs
    chi103InputQChi innerPair12Input
    leaf966InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf966LowerChecked :
    lowerCheck 24 leaf966Box leaf966Inputs = true := by
  rfl'

private theorem leaf966CoversExact : CoversExact 8
    leaf966Box leaf966Certificate leaf966InnerLog leaf966Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk90RoundedFacts chi103RoundedFacts
    innerPair12RoundedFacts leaf966RoundedFacts (by rfl)

private theorem leaf966FlatSound : Sound leaf966Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf966CertificateValid
    leaf966InnerLogValid leaf966CoversExact leaf966LowerChecked

private noncomputable def leaf967Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (11/128), chiHi := (3/32) }

private noncomputable def leaf967Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217835/134217728) }, vSqrt := { lower := (32765/32768), upper := (4194312/4194241) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (163739787/134217728) }, upper := { exponent := 0, mantissa := (319/256) } }, logOuter := sk90LogOuterCertificate, logK := sk90LogKCertificate, logChi := chi104LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (8388553/8388482) } }, logDArg := sk90LogDArgCertificate }

private noncomputable def leaf967InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf967LocalValidity :
    LeafFacts leaf967Box leaf967Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf967Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4194312/4194241) }) = true
      norm_num [leaf967Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf967CertificateValid :
    WideCertificateValid leaf967Box leaf967Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk90ValidityFacts chi104ValidityFacts
    leaf967LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf967CoverageChecked :
    coverageCheck (innerAD leaf967Box) leaf967InnerLog = true := by
  rfl'

private theorem leaf967InnerLogValid :
    leaf967InnerLog.Valid 8 (innerAD leaf967Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf967CoverageChecked

private noncomputable def leaf967InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629223/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf967InputLogOnePlusV_eq :
    leaf967InputLogOnePlusV = outerEnclosure 24
      (leaf967Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf967RoundedFacts : LeafRoundedFacts 8
    leaf967Certificate.logOnePlusV leaf967InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf967InputLogOnePlusV_eq }

private noncomputable def leaf967Inputs : Inputs :=
  inputsOfCaches globalInput sk90RoundedInputs
    chi104InputQChi innerPair12Input
    leaf967InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf967LowerChecked :
    lowerCheck 24 leaf967Box leaf967Inputs = true := by
  rfl'

private theorem leaf967CoversExact : CoversExact 8
    leaf967Box leaf967Certificate leaf967InnerLog leaf967Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk90RoundedFacts chi104RoundedFacts
    innerPair12RoundedFacts leaf967RoundedFacts (by rfl)

private theorem leaf967FlatSound : Sound leaf967Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf967CertificateValid
    leaf967InnerLogValid leaf967CoversExact leaf967LowerChecked

private noncomputable def leaf968Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (1/16), chiHi := (9/128) }

private noncomputable def leaf968Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217831/134217728) }, vSqrt := { lower := (32765/32768), upper := (33554496/33554045) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (156203611/134217728) }, upper := { exponent := 0, mantissa := (2435/2048) } }, logOuter := sk91LogOuterCertificate, logK := sk91LogKCertificate, logChi := chi125LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (67108541/67108090) } }, logDArg := sk91LogDArgCertificate }

private noncomputable def leaf968InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf968LocalValidity :
    LeafFacts leaf968Box leaf968Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf968Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (33554496/33554045) }) = true
      norm_num [leaf968Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf968CertificateValid :
    WideCertificateValid leaf968Box leaf968Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk91ValidityFacts chi125ValidityFacts
    leaf968LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf968CoverageChecked :
    coverageCheck (innerAD leaf968Box) leaf968InnerLog = true := by
  rfl'

private theorem leaf968InnerLogValid :
    leaf968InnerLog.Valid 8 (innerAD leaf968Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf968CoverageChecked

private noncomputable def leaf968InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629193/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf968InputLogOnePlusV_eq :
    leaf968InputLogOnePlusV = outerEnclosure 24
      (leaf968Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf968RoundedFacts : LeafRoundedFacts 8
    leaf968Certificate.logOnePlusV leaf968InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf968InputLogOnePlusV_eq }

private noncomputable def leaf968Inputs : Inputs :=
  inputsOfCaches globalInput sk91RoundedInputs
    chi125InputQChi innerPair3Input
    leaf968InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf968LowerChecked :
    lowerCheck 24 leaf968Box leaf968Inputs = true := by
  rfl'

private theorem leaf968CoversExact : CoversExact 8
    leaf968Box leaf968Certificate leaf968InnerLog leaf968Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk91RoundedFacts chi125RoundedFacts
    innerPair3RoundedFacts leaf968RoundedFacts (by rfl)

private theorem leaf968FlatSound : Sound leaf968Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf968CertificateValid
    leaf968InnerLogValid leaf968CoversExact leaf968LowerChecked

private noncomputable def leaf969Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (1/16), chiHi := (9/128) }

private noncomputable def leaf969Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217833/134217728) }, vSqrt := { lower := (32765/32768), upper := (8388624/8388509) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (156727865/134217728) }, upper := { exponent := 0, mantissa := (611/512) } }, logOuter := sk92LogOuterCertificate, logK := sk92LogKCertificate, logChi := chi125LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (16777133/16777018) } }, logDArg := sk92LogDArgCertificate }

private noncomputable def leaf969InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf969LocalValidity :
    LeafFacts leaf969Box leaf969Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf969Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8388624/8388509) }) = true
      norm_num [leaf969Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf969CertificateValid :
    WideCertificateValid leaf969Box leaf969Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk92ValidityFacts chi125ValidityFacts
    leaf969LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf969CoverageChecked :
    coverageCheck (innerAD leaf969Box) leaf969InnerLog = true := by
  rfl'

private theorem leaf969InnerLogValid :
    leaf969InnerLog.Valid 8 (innerAD leaf969Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf969CoverageChecked

private noncomputable def leaf969InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907299/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf969InputLogOnePlusV_eq :
    leaf969InputLogOnePlusV = outerEnclosure 24
      (leaf969Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf969RoundedFacts : LeafRoundedFacts 8
    leaf969Certificate.logOnePlusV leaf969InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf969InputLogOnePlusV_eq }

private noncomputable def leaf969Inputs : Inputs :=
  inputsOfCaches globalInput sk92RoundedInputs
    chi125InputQChi innerPair3Input
    leaf969InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf969LowerChecked :
    lowerCheck 24 leaf969Box leaf969Inputs = true := by
  rfl'

private theorem leaf969CoversExact : CoversExact 8
    leaf969Box leaf969Certificate leaf969InnerLog leaf969Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk92RoundedFacts chi125RoundedFacts
    innerPair3RoundedFacts leaf969RoundedFacts (by rfl)

private theorem leaf969FlatSound : Sound leaf969Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf969CertificateValid
    leaf969InnerLogValid leaf969CoversExact leaf969LowerChecked

private noncomputable def leaf970Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (9/128), chiHi := (5/64) }

private noncomputable def leaf970Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217833/134217728) }, vSqrt := { lower := (32765/32768), upper := (16777248/16777001) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (158955953/134217728) }, upper := { exponent := 0, mantissa := (1239/1024) } }, logOuter := sk91LogOuterCertificate, logK := sk91LogKCertificate, logChi := chi126LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (33554249/33554002) } }, logDArg := sk91LogDArgCertificate }

private noncomputable def leaf970InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf970LocalValidity :
    LeafFacts leaf970Box leaf970Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf970Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (16777248/16777001) }) = true
      norm_num [leaf970Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf970CertificateValid :
    WideCertificateValid leaf970Box leaf970Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk91ValidityFacts chi126ValidityFacts
    leaf970LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf970CoverageChecked :
    coverageCheck (innerAD leaf970Box) leaf970InnerLog = true := by
  rfl'

private theorem leaf970InnerLogValid :
    leaf970InnerLog.Valid 8 (innerAD leaf970Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf970CoverageChecked

private noncomputable def leaf970InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907301/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf970InputLogOnePlusV_eq :
    leaf970InputLogOnePlusV = outerEnclosure 24
      (leaf970Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf970RoundedFacts : LeafRoundedFacts 8
    leaf970Certificate.logOnePlusV leaf970InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf970InputLogOnePlusV_eq }

private noncomputable def leaf970Inputs : Inputs :=
  inputsOfCaches globalInput sk91RoundedInputs
    chi126InputQChi innerPair3Input
    leaf970InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf970LowerChecked :
    lowerCheck 24 leaf970Box leaf970Inputs = true := by
  rfl'

private theorem leaf970CoversExact : CoversExact 8
    leaf970Box leaf970Certificate leaf970InnerLog leaf970Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk91RoundedFacts chi126RoundedFacts
    innerPair3RoundedFacts leaf970RoundedFacts (by rfl)

private theorem leaf970FlatSound : Sound leaf970Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf970CertificateValid
    leaf970InnerLogValid leaf970CoversExact leaf970LowerChecked

private noncomputable def leaf971Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (9/128), chiHi := (5/64) }

private noncomputable def leaf971Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217835/134217728) }, vSqrt := { lower := (32765/32768), upper := (1398104/1398083) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (159545739/134217728) }, upper := { exponent := 0, mantissa := (311/256) } }, logOuter := sk92LogOuterCertificate, logK := sk92LogKCertificate, logChi := chi126LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (2796187/2796166) } }, logDArg := sk92LogDArgCertificate }

private noncomputable def leaf971InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf971LocalValidity :
    LeafFacts leaf971Box leaf971Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf971Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (1398104/1398083) }) = true
      norm_num [leaf971Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf971CertificateValid :
    WideCertificateValid leaf971Box leaf971Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk92ValidityFacts chi126ValidityFacts
    leaf971LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf971CoverageChecked :
    coverageCheck (innerAD leaf971Box) leaf971InnerLog = true := by
  rfl'

private theorem leaf971InnerLogValid :
    leaf971InnerLog.Valid 8 (innerAD leaf971Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf971CoverageChecked

private noncomputable def leaf971InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629207/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf971InputLogOnePlusV_eq :
    leaf971InputLogOnePlusV = outerEnclosure 24
      (leaf971Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf971RoundedFacts : LeafRoundedFacts 8
    leaf971Certificate.logOnePlusV leaf971InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf971InputLogOnePlusV_eq }

private noncomputable def leaf971Inputs : Inputs :=
  inputsOfCaches globalInput sk92RoundedInputs
    chi126InputQChi innerPair12Input
    leaf971InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf971LowerChecked :
    lowerCheck 24 leaf971Box leaf971Inputs = true := by
  rfl'

private theorem leaf971CoversExact : CoversExact 8
    leaf971Box leaf971Certificate leaf971InnerLog leaf971Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk92RoundedFacts chi126RoundedFacts
    innerPair12RoundedFacts leaf971RoundedFacts (by rfl)

private theorem leaf971FlatSound : Sound leaf971Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf971CertificateValid
    leaf971InnerLogValid leaf971CoversExact leaf971LowerChecked

private noncomputable def leaf972Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (5/64), chiHi := (11/128) }

private noncomputable def leaf972Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217835/134217728) }, vSqrt := { lower := (32765/32768), upper := (11184832/11184653) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (161708295/134217728) }, upper := { exponent := 0, mantissa := (2521/2048) } }, logOuter := sk91LogOuterCertificate, logK := sk91LogKCertificate, logChi := chi103LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (22369485/22369306) } }, logDArg := sk91LogDArgCertificate }

private noncomputable def leaf972InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf972LocalValidity :
    LeafFacts leaf972Box leaf972Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf972Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (11184832/11184653) }) = true
      norm_num [leaf972Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf972CertificateValid :
    WideCertificateValid leaf972Box leaf972Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk91ValidityFacts chi103ValidityFacts
    leaf972LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf972CoverageChecked :
    coverageCheck (innerAD leaf972Box) leaf972InnerLog = true := by
  rfl'

private theorem leaf972InnerLogValid :
    leaf972InnerLog.Valid 8 (innerAD leaf972Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf972CoverageChecked

private noncomputable def leaf972InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629215/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf972InputLogOnePlusV_eq :
    leaf972InputLogOnePlusV = outerEnclosure 24
      (leaf972Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf972RoundedFacts : LeafRoundedFacts 8
    leaf972Certificate.logOnePlusV leaf972InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf972InputLogOnePlusV_eq }

private noncomputable def leaf972Inputs : Inputs :=
  inputsOfCaches globalInput sk91RoundedInputs
    chi103InputQChi innerPair12Input
    leaf972InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf972LowerChecked :
    lowerCheck 24 leaf972Box leaf972Inputs = true := by
  rfl'

private theorem leaf972CoversExact : CoversExact 8
    leaf972Box leaf972Certificate leaf972InnerLog leaf972Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk91RoundedFacts chi103RoundedFacts
    innerPair12RoundedFacts leaf972RoundedFacts (by rfl)

private theorem leaf972FlatSound : Sound leaf972Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf972CertificateValid
    leaf972InnerLogValid leaf972CoversExact leaf972LowerChecked

private noncomputable def leaf973Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (11/128), chiHi := (3/32) }

private noncomputable def leaf973Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217837/134217728) }, vSqrt := { lower := (32765/32768), upper := (8388624/8388479) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (164460637/134217728) }, upper := { exponent := 0, mantissa := (641/512) } }, logOuter := sk91LogOuterCertificate, logK := sk91LogKCertificate, logChi := chi104LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (16777103/16776958) } }, logDArg := sk91LogDArgCertificate }

private noncomputable def leaf973InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf973LocalValidity :
    LeafFacts leaf973Box leaf973Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf973Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8388624/8388479) }) = true
      norm_num [leaf973Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf973CertificateValid :
    WideCertificateValid leaf973Box leaf973Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk91ValidityFacts chi104ValidityFacts
    leaf973LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf973CoverageChecked :
    coverageCheck (innerAD leaf973Box) leaf973InnerLog = true := by
  rfl'

private theorem leaf973InnerLogValid :
    leaf973InnerLog.Valid 8 (innerAD leaf973Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf973CoverageChecked

private noncomputable def leaf973InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814613/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf973InputLogOnePlusV_eq :
    leaf973InputLogOnePlusV = outerEnclosure 24
      (leaf973Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf973RoundedFacts : LeafRoundedFacts 8
    leaf973Certificate.logOnePlusV leaf973InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf973InputLogOnePlusV_eq }

private noncomputable def leaf973Inputs : Inputs :=
  inputsOfCaches globalInput sk91RoundedInputs
    chi104InputQChi innerPair13Input
    leaf973InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf973LowerChecked :
    lowerCheck 24 leaf973Box leaf973Inputs = true := by
  rfl'

private theorem leaf973CoversExact : CoversExact 8
    leaf973Box leaf973Certificate leaf973InnerLog leaf973Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk91RoundedFacts chi104RoundedFacts
    innerPair13RoundedFacts leaf973RoundedFacts (by rfl)

private theorem leaf973FlatSound : Sound leaf973Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf973CertificateValid
    leaf973InnerLogValid leaf973CoversExact leaf973LowerChecked

private noncomputable def leaf974Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (5/64), chiHi := (11/128) }

private noncomputable def leaf974Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217837/134217728) }, vSqrt := { lower := (32765/32768), upper := (8388624/8388487) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (162363613/134217728) }, upper := { exponent := 0, mantissa := (633/512) } }, logOuter := sk92LogOuterCertificate, logK := sk92LogKCertificate, logChi := chi103LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (16777111/16776974) } }, logDArg := sk92LogDArgCertificate }

private noncomputable def leaf974InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf974LocalValidity :
    LeafFacts leaf974Box leaf974Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf974Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8388624/8388487) }) = true
      norm_num [leaf974Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf974CertificateValid :
    WideCertificateValid leaf974Box leaf974Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk92ValidityFacts chi103ValidityFacts
    leaf974LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf974CoverageChecked :
    coverageCheck (innerAD leaf974Box) leaf974InnerLog = true := by
  rfl'

private theorem leaf974InnerLogValid :
    leaf974InnerLog.Valid 8 (innerAD leaf974Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf974CoverageChecked

private noncomputable def leaf974InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814609/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf974InputLogOnePlusV_eq :
    leaf974InputLogOnePlusV = outerEnclosure 24
      (leaf974Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf974RoundedFacts : LeafRoundedFacts 8
    leaf974Certificate.logOnePlusV leaf974InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf974InputLogOnePlusV_eq }

private noncomputable def leaf974Inputs : Inputs :=
  inputsOfCaches globalInput sk92RoundedInputs
    chi103InputQChi innerPair12Input
    leaf974InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf974LowerChecked :
    lowerCheck 24 leaf974Box leaf974Inputs = true := by
  rfl'

private theorem leaf974CoversExact : CoversExact 8
    leaf974Box leaf974Certificate leaf974InnerLog leaf974Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk92RoundedFacts chi103RoundedFacts
    innerPair12RoundedFacts leaf974RoundedFacts (by rfl)

private theorem leaf974FlatSound : Sound leaf974Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf974CertificateValid
    leaf974InnerLogValid leaf974CoversExact leaf974LowerChecked

private noncomputable def leaf975Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (11/128), chiHi := (3/32) }

private noncomputable def leaf975Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217839/134217728) }, vSqrt := { lower := (32765/32768), upper := (2097156/2097119) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (165181487/134217728) }, upper := { exponent := 0, mantissa := (161/128) } }, logOuter := sk92LogOuterCertificate, logK := sk92LogKCertificate, logChi := chi104LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (4194275/4194238) } }, logDArg := sk92LogDArgCertificate }

private noncomputable def leaf975InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf975LocalValidity :
    LeafFacts leaf975Box leaf975Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf975Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (2097156/2097119) }) = true
      norm_num [leaf975Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf975CertificateValid :
    WideCertificateValid leaf975Box leaf975Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk92ValidityFacts chi104ValidityFacts
    leaf975LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf975CoverageChecked :
    coverageCheck (innerAD leaf975Box) leaf975InnerLog = true := by
  rfl'

private theorem leaf975InnerLogValid :
    leaf975InnerLog.Valid 8 (innerAD leaf975Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf975CoverageChecked

private noncomputable def leaf975InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629229/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf975InputLogOnePlusV_eq :
    leaf975InputLogOnePlusV = outerEnclosure 24
      (leaf975Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf975RoundedFacts : LeafRoundedFacts 8
    leaf975Certificate.logOnePlusV leaf975InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf975InputLogOnePlusV_eq }

private noncomputable def leaf975Inputs : Inputs :=
  inputsOfCaches globalInput sk92RoundedInputs
    chi104InputQChi innerPair13Input
    leaf975InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf975LowerChecked :
    lowerCheck 24 leaf975Box leaf975Inputs = true := by
  rfl'

private theorem leaf975CoversExact : CoversExact 8
    leaf975Box leaf975Certificate leaf975InnerLog leaf975Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk92RoundedFacts chi104RoundedFacts
    innerPair13RoundedFacts leaf975RoundedFacts (by rfl)

private theorem leaf975FlatSound : Sound leaf975Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf975CertificateValid
    leaf975InnerLogValid leaf975CoversExact leaf975LowerChecked

private noncomputable def leaf976Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (3/32), chiHi := (13/128) }

private noncomputable def leaf976Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217835/134217728) }, vSqrt := { lower := (32765/32768), upper := (11184832/11184633) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (165640215/134217728) }, upper := { exponent := 0, mantissa := (2581/2048) } }, logOuter := sk89LogOuterCertificate, logK := sk89LogKCertificate, logChi := chi105LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (22369465/22369266) } }, logDArg := sk89LogDArgCertificate }

private noncomputable def leaf976InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf976LocalValidity :
    LeafFacts leaf976Box leaf976Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf976Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (11184832/11184633) }) = true
      norm_num [leaf976Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf976CertificateValid :
    WideCertificateValid leaf976Box leaf976Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk89ValidityFacts chi105ValidityFacts
    leaf976LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf976CoverageChecked :
    coverageCheck (innerAD leaf976Box) leaf976InnerLog = true := by
  rfl'

private theorem leaf976InnerLogValid :
    leaf976InnerLog.Valid 8 (innerAD leaf976Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf976CoverageChecked

private noncomputable def leaf976InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814615/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf976InputLogOnePlusV_eq :
    leaf976InputLogOnePlusV = outerEnclosure 24
      (leaf976Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf976RoundedFacts : LeafRoundedFacts 8
    leaf976Certificate.logOnePlusV leaf976InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf976InputLogOnePlusV_eq }

private noncomputable def leaf976Inputs : Inputs :=
  inputsOfCaches globalInput sk89RoundedInputs
    chi105InputQChi innerPair13Input
    leaf976InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf976LowerChecked :
    lowerCheck 24 leaf976Box leaf976Inputs = true := by
  rfl'

private theorem leaf976CoversExact : CoversExact 8
    leaf976Box leaf976Certificate leaf976InnerLog leaf976Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk89RoundedFacts chi105RoundedFacts
    innerPair13RoundedFacts leaf976RoundedFacts (by rfl)

private theorem leaf976FlatSound : Sound leaf976Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf976CertificateValid
    leaf976InnerLogValid leaf976CoversExact leaf976LowerChecked

private noncomputable def leaf977Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (13/128), chiHi := (7/64) }

private noncomputable def leaf977Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217837/134217728) }, vSqrt := { lower := (32765/32768), upper := (16777248/16776929) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (168261493/134217728) }, upper := { exponent := 0, mantissa := (1311/1024) } }, logOuter := sk89LogOuterCertificate, logK := sk89LogKCertificate, logChi := chi106LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (33554177/33553858) } }, logDArg := sk89LogDArgCertificate }

private noncomputable def leaf977InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf977LocalValidity :
    LeafFacts leaf977Box leaf977Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf977Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (16777248/16776929) }) = true
      norm_num [leaf977Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf977CertificateValid :
    WideCertificateValid leaf977Box leaf977Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk89ValidityFacts chi106ValidityFacts
    leaf977LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf977CoverageChecked :
    coverageCheck (innerAD leaf977Box) leaf977InnerLog = true := by
  rfl'

private theorem leaf977InnerLogValid :
    leaf977InnerLog.Valid 8 (innerAD leaf977Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf977CoverageChecked

private noncomputable def leaf977InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453655/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf977InputLogOnePlusV_eq :
    leaf977InputLogOnePlusV = outerEnclosure 24
      (leaf977Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf977RoundedFacts : LeafRoundedFacts 8
    leaf977Certificate.logOnePlusV leaf977InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf977InputLogOnePlusV_eq }

private noncomputable def leaf977Inputs : Inputs :=
  inputsOfCaches globalInput sk89RoundedInputs
    chi106InputQChi innerPair16Input
    leaf977InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf977LowerChecked :
    lowerCheck 24 leaf977Box leaf977Inputs = true := by
  rfl'

private theorem leaf977CoversExact : CoversExact 8
    leaf977Box leaf977Certificate leaf977InnerLog leaf977Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk89RoundedFacts chi106RoundedFacts
    innerPair16RoundedFacts leaf977RoundedFacts (by rfl)

private theorem leaf977FlatSound : Sound leaf977Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf977CertificateValid
    leaf977InnerLogValid leaf977CoversExact leaf977LowerChecked

private noncomputable def leaf978Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (3/32), chiHi := (13/128) }

private noncomputable def leaf978Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217837/134217728) }, vSqrt := { lower := (32765/32768), upper := (16777248/16776943) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (166426597/134217728) }, upper := { exponent := 0, mantissa := (1297/1024) } }, logOuter := sk90LogOuterCertificate, logK := sk90LogKCertificate, logChi := chi105LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (33554191/33553886) } }, logDArg := sk90LogDArgCertificate }

private noncomputable def leaf978InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf978LocalValidity :
    LeafFacts leaf978Box leaf978Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf978Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (16777248/16776943) }) = true
      norm_num [leaf978Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf978CertificateValid :
    WideCertificateValid leaf978Box leaf978Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk90ValidityFacts chi105ValidityFacts
    leaf978LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf978CoverageChecked :
    coverageCheck (innerAD leaf978Box) leaf978InnerLog = true := by
  rfl'

private theorem leaf978InnerLogValid :
    leaf978InnerLog.Valid 8 (innerAD leaf978Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf978CoverageChecked

private noncomputable def leaf978InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629233/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf978InputLogOnePlusV_eq :
    leaf978InputLogOnePlusV = outerEnclosure 24
      (leaf978Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf978RoundedFacts : LeafRoundedFacts 8
    leaf978Certificate.logOnePlusV leaf978InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf978InputLogOnePlusV_eq }

private noncomputable def leaf978Inputs : Inputs :=
  inputsOfCaches globalInput sk90RoundedInputs
    chi105InputQChi innerPair13Input
    leaf978InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf978LowerChecked :
    lowerCheck 24 leaf978Box leaf978Inputs = true := by
  rfl'

private theorem leaf978CoversExact : CoversExact 8
    leaf978Box leaf978Certificate leaf978InnerLog leaf978Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk90RoundedFacts chi105RoundedFacts
    innerPair13RoundedFacts leaf978RoundedFacts (by rfl)

private theorem leaf978FlatSound : Sound leaf978Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf978CertificateValid
    leaf978InnerLogValid leaf978CoversExact leaf978LowerChecked

private noncomputable def leaf979Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (13/128), chiHi := (7/64) }

private noncomputable def leaf979Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217839/134217728) }, vSqrt := { lower := (32765/32768), upper := (8388624/8388461) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (169113407/134217728) }, upper := { exponent := 0, mantissa := (659/512) } }, logOuter := sk90LogOuterCertificate, logK := sk90LogKCertificate, logChi := chi106LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (16777085/16776922) } }, logDArg := sk90LogDArgCertificate }

private noncomputable def leaf979InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf979LocalValidity :
    LeafFacts leaf979Box leaf979Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf979Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8388624/8388461) }) = true
      norm_num [leaf979Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf979CertificateValid :
    WideCertificateValid leaf979Box leaf979Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk90ValidityFacts chi106ValidityFacts
    leaf979LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf979CoverageChecked :
    coverageCheck (innerAD leaf979Box) leaf979InnerLog = true := by
  rfl'

private theorem leaf979InnerLogValid :
    leaf979InnerLog.Valid 8 (innerAD leaf979Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf979CoverageChecked

private noncomputable def leaf979InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907311/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf979InputLogOnePlusV_eq :
    leaf979InputLogOnePlusV = outerEnclosure 24
      (leaf979Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf979RoundedFacts : LeafRoundedFacts 8
    leaf979Certificate.logOnePlusV leaf979InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf979InputLogOnePlusV_eq }

private noncomputable def leaf979Inputs : Inputs :=
  inputsOfCaches globalInput sk90RoundedInputs
    chi106InputQChi innerPair16Input
    leaf979InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf979LowerChecked :
    lowerCheck 24 leaf979Box leaf979Inputs = true := by
  rfl'

private theorem leaf979CoversExact : CoversExact 8
    leaf979Box leaf979Certificate leaf979InnerLog leaf979Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk90RoundedFacts chi106RoundedFacts
    innerPair16RoundedFacts leaf979RoundedFacts (by rfl)

private theorem leaf979FlatSound : Sound leaf979Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf979CertificateValid
    leaf979InnerLogValid leaf979CoversExact leaf979LowerChecked

private noncomputable def leaf980Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (7/64), chiHi := (15/128) }

private noncomputable def leaf980Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217839/134217728) }, vSqrt := { lower := (32765/32768), upper := (33554496/33553817) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (170882771/134217728) }, upper := { exponent := 0, mantissa := (2663/2048) } }, logOuter := sk89LogOuterCertificate, logK := sk89LogKCertificate, logChi := chi98LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (67108313/67107634) } }, logDArg := sk89LogDArgCertificate }

private noncomputable def leaf980InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf980LocalValidity :
    LeafFacts leaf980Box leaf980Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf980Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (33554496/33553817) }) = true
      norm_num [leaf980Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf980CertificateValid :
    WideCertificateValid leaf980Box leaf980Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk89ValidityFacts chi98ValidityFacts
    leaf980LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf980CoverageChecked :
    coverageCheck (innerAD leaf980Box) leaf980InnerLog = true := by
  rfl'

private theorem leaf980InnerLogValid :
    leaf980InnerLog.Valid 8 (innerAD leaf980Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf980CoverageChecked

private noncomputable def leaf980InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814625/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf980InputLogOnePlusV_eq :
    leaf980InputLogOnePlusV = outerEnclosure 24
      (leaf980Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf980RoundedFacts : LeafRoundedFacts 8
    leaf980Certificate.logOnePlusV leaf980InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf980InputLogOnePlusV_eq }

private noncomputable def leaf980Inputs : Inputs :=
  inputsOfCaches globalInput sk89RoundedInputs
    chi98InputQChi innerPair16Input
    leaf980InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf980LowerChecked :
    lowerCheck 24 leaf980Box leaf980Inputs = true := by
  rfl'

private theorem leaf980CoversExact : CoversExact 8
    leaf980Box leaf980Certificate leaf980InnerLog leaf980Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk89RoundedFacts chi98RoundedFacts
    innerPair16RoundedFacts leaf980RoundedFacts (by rfl)

private theorem leaf980FlatSound : Sound leaf980Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf980CertificateValid
    leaf980InnerLogValid leaf980CoversExact leaf980LowerChecked

private noncomputable def leaf981Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (81/32), chiLo := (15/128), chiHi := (1/8) }

private noncomputable def leaf981Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435649/268435456) }, vSqrt := { lower := (32765/32768), upper := (246724/246719) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (347040897/268435456) }, upper := { exponent := 0, mantissa := (337/256) } }, logOuter := sk99LogOuterCertificate, logK := sk99LogKCertificate, logChi := chi99LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (493443/493438) } }, logDArg := sk99LogDArgCertificate }

private noncomputable def leaf981InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf981LocalValidity :
    LeafFacts leaf981Box leaf981Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf981Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (246724/246719) }) = true
      norm_num [leaf981Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf981CertificateValid :
    WideCertificateValid leaf981Box leaf981Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk99ValidityFacts chi99ValidityFacts
    leaf981LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf981CoverageChecked :
    coverageCheck (innerAD leaf981Box) leaf981InnerLog = true := by
  rfl'

private theorem leaf981InnerLogValid :
    leaf981InnerLog.Valid 8 (innerAD leaf981Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf981CoverageChecked

private noncomputable def leaf981InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629251/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf981InputLogOnePlusV_eq :
    leaf981InputLogOnePlusV = outerEnclosure 24
      (leaf981Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf981RoundedFacts : LeafRoundedFacts 8
    leaf981Certificate.logOnePlusV leaf981InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf981InputLogOnePlusV_eq }

private noncomputable def leaf981Inputs : Inputs :=
  inputsOfCaches globalInput sk99RoundedInputs
    chi99InputQChi innerPair17Input
    leaf981InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf981LowerChecked :
    lowerCheck 24 leaf981Box leaf981Inputs = true := by
  rfl'

private theorem leaf981CoversExact : CoversExact 8
    leaf981Box leaf981Certificate leaf981InnerLog leaf981Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk99RoundedFacts chi99RoundedFacts
    innerPair17RoundedFacts leaf981RoundedFacts (by rfl)

private theorem leaf981FlatSound : Sound leaf981Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf981CertificateValid
    leaf981InnerLogValid leaf981CoversExact leaf981LowerChecked

private noncomputable def leaf982Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (81/32), kHi := (41/16), chiLo := (15/128), chiHi := (1/8) }

private noncomputable def leaf982Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435651/268435456) }, vSqrt := { lower := (32765/32768), upper := (2097154/2097111) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (348023875/268435456) }, upper := { exponent := 0, mantissa := (169/128) } }, logOuter := sk100LogOuterCertificate, logK := sk100LogKCertificate, logChi := chi99LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (4194265/4194222) } }, logDArg := sk100LogDArgCertificate }

private noncomputable def leaf982InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf982LocalValidity :
    LeafFacts leaf982Box leaf982Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf982Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (2097154/2097111) }) = true
      norm_num [leaf982Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf982CertificateValid :
    WideCertificateValid leaf982Box leaf982Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk100ValidityFacts chi99ValidityFacts
    leaf982LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf982CoverageChecked :
    coverageCheck (innerAD leaf982Box) leaf982InnerLog = true := by
  rfl'

private theorem leaf982InnerLogValid :
    leaf982InnerLog.Valid 8 (innerAD leaf982Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf982CoverageChecked

private noncomputable def leaf982InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629253/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf982InputLogOnePlusV_eq :
    leaf982InputLogOnePlusV = outerEnclosure 24
      (leaf982Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf982RoundedFacts : LeafRoundedFacts 8
    leaf982Certificate.logOnePlusV leaf982InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf982InputLogOnePlusV_eq }

private noncomputable def leaf982Inputs : Inputs :=
  inputsOfCaches globalInput sk100RoundedInputs
    chi99InputQChi innerPair17Input
    leaf982InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf982LowerChecked :
    lowerCheck 24 leaf982Box leaf982Inputs = true := by
  rfl'

private theorem leaf982CoversExact : CoversExact 8
    leaf982Box leaf982Certificate leaf982InnerLog leaf982Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk100RoundedFacts chi99RoundedFacts
    innerPair17RoundedFacts leaf982RoundedFacts (by rfl)

private theorem leaf982FlatSound : Sound leaf982Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf982CertificateValid
    leaf982InnerLogValid leaf982CoversExact leaf982LowerChecked

private noncomputable def leaf983Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (83/32), chiLo := (7/64), chiHi := (15/128) }

private noncomputable def leaf983Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435651/268435456) }, vSqrt := { lower := (32765/32768), upper := (3947584/3947507) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (343633231/268435456) }, upper := { exponent := 0, mantissa := (5341/4096) } }, logOuter := sk101LogOuterCertificate, logK := sk101LogKCertificate, logChi := chi98LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (7895091/7895014) } }, logDArg := sk101LogDArgCertificate }

private noncomputable def leaf983InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf983LocalValidity :
    LeafFacts leaf983Box leaf983Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf983Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (3947584/3947507) }) = true
      norm_num [leaf983Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf983CertificateValid :
    WideCertificateValid leaf983Box leaf983Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk101ValidityFacts chi98ValidityFacts
    leaf983LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf983CoverageChecked :
    coverageCheck (innerAD leaf983Box) leaf983InnerLog = true := by
  rfl'

private theorem leaf983InnerLogValid :
    leaf983InnerLog.Valid 8 (innerAD leaf983Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf983CoverageChecked

private noncomputable def leaf983InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907311/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf983InputLogOnePlusV_eq :
    leaf983InputLogOnePlusV = outerEnclosure 24
      (leaf983Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf983RoundedFacts : LeafRoundedFacts 8
    leaf983Certificate.logOnePlusV leaf983InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf983InputLogOnePlusV_eq }

private noncomputable def leaf983Inputs : Inputs :=
  inputsOfCaches globalInput sk101RoundedInputs
    chi98InputQChi innerPair16Input
    leaf983InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf983LowerChecked :
    lowerCheck 24 leaf983Box leaf983Inputs = true := by
  rfl'

private theorem leaf983CoversExact : CoversExact 8
    leaf983Box leaf983Certificate leaf983InnerLog leaf983Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk101RoundedFacts chi98RoundedFacts
    innerPair16RoundedFacts leaf983RoundedFacts (by rfl)

private theorem leaf983FlatSound : Sound leaf983Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf983CertificateValid
    leaf983InnerLogValid leaf983CoversExact leaf983LowerChecked

private noncomputable def leaf984Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (83/32), kHi := (21/8), chiLo := (7/64), chiHi := (15/128) }

private noncomputable def leaf984Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435653/268435456) }, vSqrt := { lower := (32765/32768), upper := (16777232/16776901) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (344550677/268435456) }, upper := { exponent := 0, mantissa := (1339/1024) } }, logOuter := sk102LogOuterCertificate, logK := sk102LogKCertificate, logChi := chi98LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (33554133/33553802) } }, logDArg := sk102LogDArgCertificate }

private noncomputable def leaf984InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf984LocalValidity :
    LeafFacts leaf984Box leaf984Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf984Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (16777232/16776901) }) = true
      norm_num [leaf984Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf984CertificateValid :
    WideCertificateValid leaf984Box leaf984Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk102ValidityFacts chi98ValidityFacts
    leaf984LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf984CoverageChecked :
    coverageCheck (innerAD leaf984Box) leaf984InnerLog = true := by
  rfl'

private theorem leaf984InnerLogValid :
    leaf984InnerLog.Valid 8 (innerAD leaf984Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf984CoverageChecked

private noncomputable def leaf984InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814623/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf984InputLogOnePlusV_eq :
    leaf984InputLogOnePlusV = outerEnclosure 24
      (leaf984Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf984RoundedFacts : LeafRoundedFacts 8
    leaf984Certificate.logOnePlusV leaf984InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf984InputLogOnePlusV_eq }

private noncomputable def leaf984Inputs : Inputs :=
  inputsOfCaches globalInput sk102RoundedInputs
    chi98InputQChi innerPair16Input
    leaf984InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf984LowerChecked :
    lowerCheck 24 leaf984Box leaf984Inputs = true := by
  rfl'

private theorem leaf984CoversExact : CoversExact 8
    leaf984Box leaf984Certificate leaf984InnerLog leaf984Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk102RoundedFacts chi98RoundedFacts
    innerPair16RoundedFacts leaf984RoundedFacts (by rfl)

private theorem leaf984FlatSound : Sound leaf984Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf984CertificateValid
    leaf984InnerLogValid leaf984CoversExact leaf984LowerChecked

private noncomputable def leaf985Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (83/32), chiLo := (15/128), chiHi := (1/8) }

private noncomputable def leaf985Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435653/268435456) }, vSqrt := { lower := (32765/32768), upper := (4194308/4194221) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (349006853/268435456) }, upper := { exponent := 0, mantissa := (339/256) } }, logOuter := sk101LogOuterCertificate, logK := sk101LogKCertificate, logChi := chi99LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (8388529/8388442) } }, logDArg := sk101LogDArgCertificate }

private noncomputable def leaf985InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf985LocalValidity :
    LeafFacts leaf985Box leaf985Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf985Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4194308/4194221) }) = true
      norm_num [leaf985Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf985CertificateValid :
    WideCertificateValid leaf985Box leaf985Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk101ValidityFacts chi99ValidityFacts
    leaf985LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf985CoverageChecked :
    coverageCheck (innerAD leaf985Box) leaf985InnerLog = true := by
  rfl'

private theorem leaf985InnerLogValid :
    leaf985InnerLog.Valid 8 (innerAD leaf985Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf985CoverageChecked

private noncomputable def leaf985InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629255/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf985InputLogOnePlusV_eq :
    leaf985InputLogOnePlusV = outerEnclosure 24
      (leaf985Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf985RoundedFacts : LeafRoundedFacts 8
    leaf985Certificate.logOnePlusV leaf985InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf985InputLogOnePlusV_eq }

private noncomputable def leaf985Inputs : Inputs :=
  inputsOfCaches globalInput sk101RoundedInputs
    chi99InputQChi innerPair17Input
    leaf985InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf985LowerChecked :
    lowerCheck 24 leaf985Box leaf985Inputs = true := by
  rfl'

private theorem leaf985CoversExact : CoversExact 8
    leaf985Box leaf985Certificate leaf985InnerLog leaf985Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk101RoundedFacts chi99RoundedFacts
    innerPair17RoundedFacts leaf985RoundedFacts (by rfl)

private theorem leaf985FlatSound : Sound leaf985Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf985CertificateValid
    leaf985InnerLogValid leaf985CoversExact leaf985LowerChecked

private noncomputable def leaf986Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (83/32), kHi := (21/8), chiLo := (15/128), chiHi := (1/8) }

private noncomputable def leaf986Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435655/268435456) }, vSqrt := { lower := (32765/32768), upper := (1048577/1048555) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (349989831/268435456) }, upper := { exponent := 0, mantissa := (85/64) } }, logOuter := sk102LogOuterCertificate, logK := sk102LogKCertificate, logChi := chi99LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (1048566/1048555) } }, logDArg := sk102LogDArgCertificate }

private noncomputable def leaf986InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf986LocalValidity :
    LeafFacts leaf986Box leaf986Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf986Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (1048577/1048555) }) = true
      norm_num [leaf986Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf986CertificateValid :
    WideCertificateValid leaf986Box leaf986Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk102ValidityFacts chi99ValidityFacts
    leaf986LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf986CoverageChecked :
    coverageCheck (innerAD leaf986Box) leaf986InnerLog = true := by
  rfl'

private theorem leaf986InnerLogValid :
    leaf986InnerLog.Valid 8 (innerAD leaf986Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf986CoverageChecked

private noncomputable def leaf986InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629257/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf986InputLogOnePlusV_eq :
    leaf986InputLogOnePlusV = outerEnclosure 24
      (leaf986Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf986RoundedFacts : LeafRoundedFacts 8
    leaf986Certificate.logOnePlusV leaf986InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf986InputLogOnePlusV_eq }

private noncomputable def leaf986Inputs : Inputs :=
  inputsOfCaches globalInput sk102RoundedInputs
    chi99InputQChi innerPair17Input
    leaf986InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf986LowerChecked :
    lowerCheck 24 leaf986Box leaf986Inputs = true := by
  rfl'

private theorem leaf986CoversExact : CoversExact 8
    leaf986Box leaf986Certificate leaf986InnerLog leaf986Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk102RoundedFacts chi99RoundedFacts
    innerPair17RoundedFacts leaf986RoundedFacts (by rfl)

private theorem leaf986FlatSound : Sound leaf986Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf986CertificateValid
    leaf986InnerLogValid leaf986CoversExact leaf986LowerChecked

private noncomputable def leaf987Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (3/32), chiHi := (13/128) }

private noncomputable def leaf987Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217839/134217728) }, vSqrt := { lower := (32765/32768), upper := (33554496/33553873) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (167212979/134217728) }, upper := { exponent := 0, mantissa := (2607/2048) } }, logOuter := sk91LogOuterCertificate, logK := sk91LogKCertificate, logChi := chi105LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (67108369/67107746) } }, logDArg := sk91LogDArgCertificate }

private noncomputable def leaf987InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf987LocalValidity :
    LeafFacts leaf987Box leaf987Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf987Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (33554496/33553873) }) = true
      norm_num [leaf987Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf987CertificateValid :
    WideCertificateValid leaf987Box leaf987Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk91ValidityFacts chi105ValidityFacts
    leaf987LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf987CoverageChecked :
    coverageCheck (innerAD leaf987Box) leaf987InnerLog = true := by
  rfl'

private theorem leaf987InnerLogValid :
    leaf987InnerLog.Valid 8 (innerAD leaf987Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf987CoverageChecked

private noncomputable def leaf987InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907309/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf987InputLogOnePlusV_eq :
    leaf987InputLogOnePlusV = outerEnclosure 24
      (leaf987Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf987RoundedFacts : LeafRoundedFacts 8
    leaf987Certificate.logOnePlusV leaf987InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf987InputLogOnePlusV_eq }

private noncomputable def leaf987Inputs : Inputs :=
  inputsOfCaches globalInput sk91RoundedInputs
    chi105InputQChi innerPair13Input
    leaf987InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf987LowerChecked :
    lowerCheck 24 leaf987Box leaf987Inputs = true := by
  rfl'

private theorem leaf987CoversExact : CoversExact 8
    leaf987Box leaf987Certificate leaf987InnerLog leaf987Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk91RoundedFacts chi105RoundedFacts
    innerPair13RoundedFacts leaf987RoundedFacts (by rfl)

private theorem leaf987FlatSound : Sound leaf987Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf987CertificateValid
    leaf987InnerLogValid leaf987CoversExact leaf987LowerChecked

private noncomputable def leaf988Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (13/128), chiHi := (7/64) }

private noncomputable def leaf988Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217841/134217728) }, vSqrt := { lower := (32765/32768), upper := (5592416/5592305) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (169965321/134217728) }, upper := { exponent := 0, mantissa := (1325/1024) } }, logOuter := sk91LogOuterCertificate, logK := sk91LogKCertificate, logChi := chi106LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (11184721/11184610) } }, logDArg := sk91LogDArgCertificate }

private noncomputable def leaf988InnerLog : WideLogData :=
  innerPair390Data

set_option maxRecDepth 1000000 in
private theorem leaf988LocalValidity :
    LeafFacts leaf988Box leaf988Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf988Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (5592416/5592305) }) = true
      norm_num [leaf988Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf988CertificateValid :
    WideCertificateValid leaf988Box leaf988Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk91ValidityFacts chi106ValidityFacts
    leaf988LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf988CoverageChecked :
    coverageCheck (innerAD leaf988Box) leaf988InnerLog = true := by
  rfl'

private theorem leaf988InnerLogValid :
    leaf988InnerLog.Valid 8 (innerAD leaf988Box) :=
  wideLogDataValid_of_cachedCheck endpoint100PositiveFacts
    endpoint115PositiveFacts.valid leaf988CoverageChecked

private noncomputable def leaf988InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629247/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf988InputLogOnePlusV_eq :
    leaf988InputLogOnePlusV = outerEnclosure 24
      (leaf988Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf988RoundedFacts : LeafRoundedFacts 8
    leaf988Certificate.logOnePlusV leaf988InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf988InputLogOnePlusV_eq }

private noncomputable def leaf988Inputs : Inputs :=
  inputsOfCaches globalInput sk91RoundedInputs
    chi106InputQChi innerPair390Input
    leaf988InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf988LowerChecked :
    lowerCheck 24 leaf988Box leaf988Inputs = true := by
  rfl'

private theorem leaf988CoversExact : CoversExact 8
    leaf988Box leaf988Certificate leaf988InnerLog leaf988Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk91RoundedFacts chi106RoundedFacts
    innerPair390RoundedFacts leaf988RoundedFacts (by rfl)

private theorem leaf988FlatSound : Sound leaf988Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf988CertificateValid
    leaf988InnerLogValid leaf988CoversExact leaf988LowerChecked

private noncomputable def leaf989Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (3/32), chiHi := (13/128) }

private noncomputable def leaf989Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217841/134217728) }, vSqrt := { lower := (32765/32768), upper := (2796208/2796155) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (167999361/134217728) }, upper := { exponent := 0, mantissa := (655/512) } }, logOuter := sk92LogOuterCertificate, logK := sk92LogKCertificate, logChi := chi105LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (5592363/5592310) } }, logDArg := sk92LogDArgCertificate }

private noncomputable def leaf989InnerLog : WideLogData :=
  innerPair20Data

set_option maxRecDepth 1000000 in
private theorem leaf989LocalValidity :
    LeafFacts leaf989Box leaf989Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf989Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (2796208/2796155) }) = true
      norm_num [leaf989Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf989CertificateValid :
    WideCertificateValid leaf989Box leaf989Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk92ValidityFacts chi105ValidityFacts
    leaf989LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf989CoverageChecked :
    coverageCheck (innerAD leaf989Box) leaf989InnerLog = true := by
  rfl'

private theorem leaf989InnerLogValid :
    leaf989InnerLog.Valid 8 (innerAD leaf989Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint28PositiveFacts.valid leaf989CoverageChecked

private noncomputable def leaf989InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453655/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf989InputLogOnePlusV_eq :
    leaf989InputLogOnePlusV = outerEnclosure 24
      (leaf989Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf989RoundedFacts : LeafRoundedFacts 8
    leaf989Certificate.logOnePlusV leaf989InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf989InputLogOnePlusV_eq }

private noncomputable def leaf989Inputs : Inputs :=
  inputsOfCaches globalInput sk92RoundedInputs
    chi105InputQChi innerPair20Input
    leaf989InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf989LowerChecked :
    lowerCheck 24 leaf989Box leaf989Inputs = true := by
  rfl'

private theorem leaf989CoversExact : CoversExact 8
    leaf989Box leaf989Certificate leaf989InnerLog leaf989Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk92RoundedFacts chi105RoundedFacts
    innerPair20RoundedFacts leaf989RoundedFacts (by rfl)

private theorem leaf989FlatSound : Sound leaf989Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf989CertificateValid
    leaf989InnerLogValid leaf989CoversExact leaf989LowerChecked

private noncomputable def leaf990Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (13/128), chiHi := (7/64) }

private noncomputable def leaf990Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435657/268435456) }, vSqrt := { lower := (32765/32768), upper := (33554464/33553823) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (341667265/268435456) }, upper := { exponent := 0, mantissa := (2657/2048) } }, logOuter := sk103LogOuterCertificate, logK := sk103LogKCertificate, logChi := chi106LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (67108287/67107646) } }, logDArg := sk103LogDArgCertificate }

private noncomputable def leaf990InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf990LocalValidity :
    LeafFacts leaf990Box leaf990Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf990Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (33554464/33553823) }) = true
      norm_num [leaf990Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf990CertificateValid :
    WideCertificateValid leaf990Box leaf990Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk103ValidityFacts chi106ValidityFacts
    leaf990LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf990CoverageChecked :
    coverageCheck (innerAD leaf990Box) leaf990InnerLog = true := by
  rfl'

private theorem leaf990InnerLogValid :
    leaf990InnerLog.Valid 8 (innerAD leaf990Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf990CoverageChecked

private noncomputable def leaf990InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629241/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf990InputLogOnePlusV_eq :
    leaf990InputLogOnePlusV = outerEnclosure 24
      (leaf990Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf990RoundedFacts : LeafRoundedFacts 8
    leaf990Certificate.logOnePlusV leaf990InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf990InputLogOnePlusV_eq }

private noncomputable def leaf990Inputs : Inputs :=
  inputsOfCaches globalInput sk103RoundedInputs
    chi106InputQChi innerPair16Input
    leaf990InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf990LowerChecked :
    lowerCheck 24 leaf990Box leaf990Inputs = true := by
  rfl'

private theorem leaf990CoversExact : CoversExact 8
    leaf990Box leaf990Certificate leaf990InnerLog leaf990Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk103RoundedFacts chi106RoundedFacts
    innerPair16RoundedFacts leaf990RoundedFacts (by rfl)

private theorem leaf990FlatSound : Sound leaf990Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf990CertificateValid
    leaf990InnerLogValid leaf990CoversExact leaf990LowerChecked

private noncomputable def leaf991Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (13/128), chiHi := (7/64) }

private noncomputable def leaf991Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435659/268435456) }, vSqrt := { lower := (32765/32768), upper := (4194308/4194227) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (342519179/268435456) }, upper := { exponent := 0, mantissa := (333/256) } }, logOuter := sk104LogOuterCertificate, logK := sk104LogKCertificate, logChi := chi106LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (8388535/8388454) } }, logDArg := sk104LogDArgCertificate }

private noncomputable def leaf991InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf991LocalValidity :
    LeafFacts leaf991Box leaf991Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf991Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4194308/4194227) }) = true
      norm_num [leaf991Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf991CertificateValid :
    WideCertificateValid leaf991Box leaf991Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk104ValidityFacts chi106ValidityFacts
    leaf991LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf991CoverageChecked :
    coverageCheck (innerAD leaf991Box) leaf991InnerLog = true := by
  rfl'

private theorem leaf991InnerLogValid :
    leaf991InnerLog.Valid 8 (innerAD leaf991Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf991CoverageChecked

private noncomputable def leaf991InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629243/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf991InputLogOnePlusV_eq :
    leaf991InputLogOnePlusV = outerEnclosure 24
      (leaf991Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf991RoundedFacts : LeafRoundedFacts 8
    leaf991Certificate.logOnePlusV leaf991InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf991InputLogOnePlusV_eq }

private noncomputable def leaf991Inputs : Inputs :=
  inputsOfCaches globalInput sk104RoundedInputs
    chi106InputQChi innerPair16Input
    leaf991InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf991LowerChecked :
    lowerCheck 24 leaf991Box leaf991Inputs = true := by
  rfl'

private theorem leaf991CoversExact : CoversExact 8
    leaf991Box leaf991Certificate leaf991InnerLog leaf991Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk104RoundedFacts chi106RoundedFacts
    innerPair16RoundedFacts leaf991RoundedFacts (by rfl)

private theorem leaf991FlatSound : Sound leaf991Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf991CertificateValid
    leaf991InnerLogValid leaf991CoversExact leaf991LowerChecked

private noncomputable def leaf992Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (85/32), chiLo := (7/64), chiHi := (15/128) }

private noncomputable def leaf992Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435655/268435456) }, vSqrt := { lower := (32765/32768), upper := (67108928/67107589) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (345468123/268435456) }, upper := { exponent := 0, mantissa := (5371/4096) } }, logOuter := sk105LogOuterCertificate, logK := sk105LogKCertificate, logChi := chi98LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (134216517/134215178) } }, logDArg := sk105LogDArgCertificate }

private noncomputable def leaf992InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf992LocalValidity :
    LeafFacts leaf992Box leaf992Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf992Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (67108928/67107589) }) = true
      norm_num [leaf992Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf992CertificateValid :
    WideCertificateValid leaf992Box leaf992Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk105ValidityFacts chi98ValidityFacts
    leaf992LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf992CoverageChecked :
    coverageCheck (innerAD leaf992Box) leaf992InnerLog = true := by
  rfl'

private theorem leaf992InnerLogValid :
    leaf992InnerLog.Valid 8 (innerAD leaf992Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf992CoverageChecked

private noncomputable def leaf992InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (181707/262144) }

set_option maxRecDepth 1000000 in
private theorem leaf992InputLogOnePlusV_eq :
    leaf992InputLogOnePlusV = outerEnclosure 24
      (leaf992Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf992RoundedFacts : LeafRoundedFacts 8
    leaf992Certificate.logOnePlusV leaf992InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf992InputLogOnePlusV_eq }

private noncomputable def leaf992Inputs : Inputs :=
  inputsOfCaches globalInput sk105RoundedInputs
    chi98InputQChi innerPair16Input
    leaf992InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf992LowerChecked :
    lowerCheck 24 leaf992Box leaf992Inputs = true := by
  rfl'

private theorem leaf992CoversExact : CoversExact 8
    leaf992Box leaf992Certificate leaf992InnerLog leaf992Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk105RoundedFacts chi98RoundedFacts
    innerPair16RoundedFacts leaf992RoundedFacts (by rfl)

private theorem leaf992FlatSound : Sound leaf992Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf992CertificateValid
    leaf992InnerLogValid leaf992CoversExact leaf992LowerChecked

private noncomputable def leaf993Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (85/32), kHi := (43/16), chiLo := (7/64), chiHi := (15/128) }

private noncomputable def leaf993Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435657/268435456) }, vSqrt := { lower := (32765/32768), upper := (33554464/33553787) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (346385569/268435456) }, upper := { exponent := 0, mantissa := (2693/2048) } }, logOuter := sk106LogOuterCertificate, logK := sk106LogKCertificate, logChi := chi98LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (67108251/67107574) } }, logDArg := sk106LogDArgCertificate }

private noncomputable def leaf993InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf993LocalValidity :
    LeafFacts leaf993Box leaf993Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf993Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (33554464/33553787) }) = true
      norm_num [leaf993Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf993CertificateValid :
    WideCertificateValid leaf993Box leaf993Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk106ValidityFacts chi98ValidityFacts
    leaf993LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf993CoverageChecked :
    coverageCheck (innerAD leaf993Box) leaf993InnerLog = true := by
  rfl'

private theorem leaf993InnerLogValid :
    leaf993InnerLog.Valid 8 (innerAD leaf993Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf993CoverageChecked

private noncomputable def leaf993InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814625/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf993InputLogOnePlusV_eq :
    leaf993InputLogOnePlusV = outerEnclosure 24
      (leaf993Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf993RoundedFacts : LeafRoundedFacts 8
    leaf993Certificate.logOnePlusV leaf993InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf993InputLogOnePlusV_eq }

private noncomputable def leaf993Inputs : Inputs :=
  inputsOfCaches globalInput sk106RoundedInputs
    chi98InputQChi innerPair17Input
    leaf993InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf993LowerChecked :
    lowerCheck 24 leaf993Box leaf993Inputs = true := by
  rfl'

private theorem leaf993CoversExact : CoversExact 8
    leaf993Box leaf993Certificate leaf993InnerLog leaf993Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk106RoundedFacts chi98RoundedFacts
    innerPair17RoundedFacts leaf993RoundedFacts (by rfl)

private theorem leaf993FlatSound : Sound leaf993Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf993CertificateValid
    leaf993InnerLogValid leaf993CoversExact leaf993LowerChecked

private noncomputable def leaf994Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (85/32), chiLo := (15/128), chiHi := (1/8) }

private noncomputable def leaf994Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435657/268435456) }, vSqrt := { lower := (32765/32768), upper := (4194308/4194219) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (350972809/268435456) }, upper := { exponent := 0, mantissa := (341/256) } }, logOuter := sk105LogOuterCertificate, logK := sk105LogKCertificate, logChi := chi99LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (8388527/8388438) } }, logDArg := sk105LogDArgCertificate }

private noncomputable def leaf994InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf994LocalValidity :
    LeafFacts leaf994Box leaf994Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf994Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4194308/4194219) }) = true
      norm_num [leaf994Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf994CertificateValid :
    WideCertificateValid leaf994Box leaf994Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk105ValidityFacts chi99ValidityFacts
    leaf994LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf994CoverageChecked :
    coverageCheck (innerAD leaf994Box) leaf994InnerLog = true := by
  rfl'

private theorem leaf994InnerLogValid :
    leaf994InnerLog.Valid 8 (innerAD leaf994Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf994CoverageChecked

private noncomputable def leaf994InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629259/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf994InputLogOnePlusV_eq :
    leaf994InputLogOnePlusV = outerEnclosure 24
      (leaf994Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf994RoundedFacts : LeafRoundedFacts 8
    leaf994Certificate.logOnePlusV leaf994InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf994InputLogOnePlusV_eq }

private noncomputable def leaf994Inputs : Inputs :=
  inputsOfCaches globalInput sk105RoundedInputs
    chi99InputQChi innerPair17Input
    leaf994InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf994LowerChecked :
    lowerCheck 24 leaf994Box leaf994Inputs = true := by
  rfl'

private theorem leaf994CoversExact : CoversExact 8
    leaf994Box leaf994Certificate leaf994InnerLog leaf994Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk105RoundedFacts chi99RoundedFacts
    innerPair17RoundedFacts leaf994RoundedFacts (by rfl)

private theorem leaf994FlatSound : Sound leaf994Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf994CertificateValid
    leaf994InnerLogValid leaf994CoversExact leaf994LowerChecked

private noncomputable def leaf995Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (85/32), kHi := (43/16), chiLo := (15/128), chiHi := (1/8) }

private noncomputable def leaf995Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435659/268435456) }, vSqrt := { lower := (32765/32768), upper := (2097154/2097109) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (351955787/268435456) }, upper := { exponent := 0, mantissa := (171/128) } }, logOuter := sk106LogOuterCertificate, logK := sk106LogKCertificate, logChi := chi99LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (4194263/4194218) } }, logDArg := sk106LogDArgCertificate }

private noncomputable def leaf995InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf995LocalValidity :
    LeafFacts leaf995Box leaf995Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf995Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (2097154/2097109) }) = true
      norm_num [leaf995Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf995CertificateValid :
    WideCertificateValid leaf995Box leaf995Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk106ValidityFacts chi99ValidityFacts
    leaf995LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf995CoverageChecked :
    coverageCheck (innerAD leaf995Box) leaf995InnerLog = true := by
  rfl'

private theorem leaf995InnerLogValid :
    leaf995InnerLog.Valid 8 (innerAD leaf995Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf995CoverageChecked

private noncomputable def leaf995InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629261/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf995InputLogOnePlusV_eq :
    leaf995InputLogOnePlusV = outerEnclosure 24
      (leaf995Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf995RoundedFacts : LeafRoundedFacts 8
    leaf995Certificate.logOnePlusV leaf995InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf995InputLogOnePlusV_eq }

private noncomputable def leaf995Inputs : Inputs :=
  inputsOfCaches globalInput sk106RoundedInputs
    chi99InputQChi innerPair17Input
    leaf995InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf995LowerChecked :
    lowerCheck 24 leaf995Box leaf995Inputs = true := by
  rfl'

private theorem leaf995CoversExact : CoversExact 8
    leaf995Box leaf995Certificate leaf995InnerLog leaf995Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk106RoundedFacts chi99RoundedFacts
    innerPair17RoundedFacts leaf995RoundedFacts (by rfl)

private theorem leaf995FlatSound : Sound leaf995Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf995CertificateValid
    leaf995InnerLogValid leaf995CoversExact leaf995LowerChecked

private noncomputable def leaf996Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (7/64), chiHi := (15/128) }

private noncomputable def leaf996Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435659/268435456) }, vSqrt := { lower := (32765/32768), upper := (67108928/67107559) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (347303015/268435456) }, upper := { exponent := 0, mantissa := (5401/4096) } }, logOuter := sk103LogOuterCertificate, logK := sk103LogKCertificate, logChi := chi98LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (134216487/134215118) } }, logDArg := sk103LogDArgCertificate }

private noncomputable def leaf996InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf996LocalValidity :
    LeafFacts leaf996Box leaf996Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf996Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (67108928/67107559) }) = true
      norm_num [leaf996Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf996CertificateValid :
    WideCertificateValid leaf996Box leaf996Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk103ValidityFacts chi98ValidityFacts
    leaf996LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf996CoverageChecked :
    coverageCheck (innerAD leaf996Box) leaf996InnerLog = true := by
  rfl'

private theorem leaf996InnerLogValid :
    leaf996InnerLog.Valid 8 (innerAD leaf996Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf996CoverageChecked

private noncomputable def leaf996InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907313/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf996InputLogOnePlusV_eq :
    leaf996InputLogOnePlusV = outerEnclosure 24
      (leaf996Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf996RoundedFacts : LeafRoundedFacts 8
    leaf996Certificate.logOnePlusV leaf996InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf996InputLogOnePlusV_eq }

private noncomputable def leaf996Inputs : Inputs :=
  inputsOfCaches globalInput sk103RoundedInputs
    chi98InputQChi innerPair17Input
    leaf996InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf996LowerChecked :
    lowerCheck 24 leaf996Box leaf996Inputs = true := by
  rfl'

private theorem leaf996CoversExact : CoversExact 8
    leaf996Box leaf996Certificate leaf996InnerLog leaf996Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk103RoundedFacts chi98RoundedFacts
    innerPair17RoundedFacts leaf996RoundedFacts (by rfl)

private theorem leaf996FlatSound : Sound leaf996Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf996CertificateValid
    leaf996InnerLogValid leaf996CoversExact leaf996LowerChecked

private noncomputable def leaf997Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (7/64), chiHi := (15/128) }

private noncomputable def leaf997Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435661/268435456) }, vSqrt := { lower := (32765/32768), upper := (8388616/8388443) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (348220461/268435456) }, upper := { exponent := 0, mantissa := (677/512) } }, logOuter := sk104LogOuterCertificate, logK := sk104LogKCertificate, logChi := chi98LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (16777059/16776886) } }, logDArg := sk104LogDArgCertificate }

private noncomputable def leaf997InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf997LocalValidity :
    LeafFacts leaf997Box leaf997Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf997Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8388616/8388443) }) = true
      norm_num [leaf997Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf997CertificateValid :
    WideCertificateValid leaf997Box leaf997Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk104ValidityFacts chi98ValidityFacts
    leaf997LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf997CoverageChecked :
    coverageCheck (innerAD leaf997Box) leaf997InnerLog = true := by
  rfl'

private theorem leaf997InnerLogValid :
    leaf997InnerLog.Valid 8 (innerAD leaf997Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf997CoverageChecked

private noncomputable def leaf997InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814627/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf997InputLogOnePlusV_eq :
    leaf997InputLogOnePlusV = outerEnclosure 24
      (leaf997Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf997RoundedFacts : LeafRoundedFacts 8
    leaf997Certificate.logOnePlusV leaf997InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf997InputLogOnePlusV_eq }

private noncomputable def leaf997Inputs : Inputs :=
  inputsOfCaches globalInput sk104RoundedInputs
    chi98InputQChi innerPair17Input
    leaf997InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf997LowerChecked :
    lowerCheck 24 leaf997Box leaf997Inputs = true := by
  rfl'

private theorem leaf997CoversExact : CoversExact 8
    leaf997Box leaf997Certificate leaf997InnerLog leaf997Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk104RoundedFacts chi98RoundedFacts
    innerPair17RoundedFacts leaf997RoundedFacts (by rfl)

private theorem leaf997FlatSound : Sound leaf997Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf997CertificateValid
    leaf997InnerLogValid leaf997CoversExact leaf997LowerChecked

private noncomputable def leaf998Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (15/128), chiHi := (1/8) }

private noncomputable def leaf998Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435661/268435456) }, vSqrt := { lower := (32765/32768), upper := (4194308/4194217) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (352938765/268435456) }, upper := { exponent := 0, mantissa := (343/256) } }, logOuter := sk103LogOuterCertificate, logK := sk103LogKCertificate, logChi := chi99LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (8388525/8388434) } }, logDArg := sk103LogDArgCertificate }

private noncomputable def leaf998InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf998LocalValidity :
    LeafFacts leaf998Box leaf998Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf998Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4194308/4194217) }) = true
      norm_num [leaf998Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf998CertificateValid :
    WideCertificateValid leaf998Box leaf998Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk103ValidityFacts chi99ValidityFacts
    leaf998LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf998CoverageChecked :
    coverageCheck (innerAD leaf998Box) leaf998InnerLog = true := by
  rfl'

private theorem leaf998InnerLogValid :
    leaf998InnerLog.Valid 8 (innerAD leaf998Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf998CoverageChecked

private noncomputable def leaf998InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629263/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf998InputLogOnePlusV_eq :
    leaf998InputLogOnePlusV = outerEnclosure 24
      (leaf998Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf998RoundedFacts : LeafRoundedFacts 8
    leaf998Certificate.logOnePlusV leaf998InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf998InputLogOnePlusV_eq }

private noncomputable def leaf998Inputs : Inputs :=
  inputsOfCaches globalInput sk103RoundedInputs
    chi99InputQChi innerPair21Input
    leaf998InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf998LowerChecked :
    lowerCheck 24 leaf998Box leaf998Inputs = true := by
  rfl'

private theorem leaf998CoversExact : CoversExact 8
    leaf998Box leaf998Certificate leaf998InnerLog leaf998Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk103RoundedFacts chi99RoundedFacts
    innerPair21RoundedFacts leaf998RoundedFacts (by rfl)

private theorem leaf998FlatSound : Sound leaf998Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf998CertificateValid
    leaf998InnerLogValid leaf998CoversExact leaf998LowerChecked

private noncomputable def leaf999Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (15/128), chiHi := (1/8) }

private noncomputable def leaf999Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435663/268435456) }, vSqrt := { lower := (32765/32768), upper := (1048577/1048554) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (353921743/268435456) }, upper := { exponent := 0, mantissa := (43/32) } }, logOuter := sk104LogOuterCertificate, logK := sk104LogKCertificate, logChi := chi99LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (2097131/2097108) } }, logDArg := sk104LogDArgCertificate }

private noncomputable def leaf999InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf999LocalValidity :
    LeafFacts leaf999Box leaf999Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf999Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (1048577/1048554) }) = true
      norm_num [leaf999Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf999CertificateValid :
    WideCertificateValid leaf999Box leaf999Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk104ValidityFacts chi99ValidityFacts
    leaf999LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf999CoverageChecked :
    coverageCheck (innerAD leaf999Box) leaf999InnerLog = true := by
  rfl'

private theorem leaf999InnerLogValid :
    leaf999InnerLog.Valid 8 (innerAD leaf999Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf999CoverageChecked

private noncomputable def leaf999InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629265/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf999InputLogOnePlusV_eq :
    leaf999InputLogOnePlusV = outerEnclosure 24
      (leaf999Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf999RoundedFacts : LeafRoundedFacts 8
    leaf999Certificate.logOnePlusV leaf999InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf999InputLogOnePlusV_eq }

private noncomputable def leaf999Inputs : Inputs :=
  inputsOfCaches globalInput sk104RoundedInputs
    chi99InputQChi innerPair21Input
    leaf999InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf999LowerChecked :
    lowerCheck 24 leaf999Box leaf999Inputs = true := by
  rfl'

private theorem leaf999CoversExact : CoversExact 8
    leaf999Box leaf999Certificate leaf999InnerLog leaf999Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk104RoundedFacts chi99RoundedFacts
    innerPair21RoundedFacts leaf999RoundedFacts (by rfl)

private theorem leaf999FlatSound : Sound leaf999Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf999CertificateValid
    leaf999InnerLogValid leaf999CoversExact leaf999LowerChecked

private noncomputable def component23Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (1/16), chiHi := (9/128) }

set_option maxRecDepth 1000000 in
private theorem component23Node0_sound : Sound component23Node0Box :=
  sound_of_literal_split component23Node0Box leaf960Box leaf961Box
    .k (41/16) (by rfl) (by rfl)
    leaf960FlatSound leaf961FlatSound

private noncomputable def component23Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (9/128), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component23Node1_sound : Sound component23Node1Box :=
  sound_of_literal_split component23Node1Box leaf962Box leaf963Box
    .k (41/16) (by rfl) (by rfl)
    leaf962FlatSound leaf963FlatSound

private noncomputable def component23Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (1/16), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component23Node2_sound : Sound component23Node2Box :=
  sound_of_literal_split component23Node2Box component23Node0Box component23Node1Box
    .chi (9/128) (by rfl) (by rfl)
    component23Node0_sound component23Node1_sound

private noncomputable def component23Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (5/64), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component23Node3_sound : Sound component23Node3Box :=
  sound_of_literal_split component23Node3Box leaf964Box leaf965Box
    .chi (11/128) (by rfl) (by rfl)
    leaf964FlatSound leaf965FlatSound

private noncomputable def component23Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (5/64), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component23Node4_sound : Sound component23Node4Box :=
  sound_of_literal_split component23Node4Box leaf966Box leaf967Box
    .chi (11/128) (by rfl) (by rfl)
    leaf966FlatSound leaf967FlatSound

private noncomputable def component23Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (5/64), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component23Node5_sound : Sound component23Node5Box :=
  sound_of_literal_split component23Node5Box component23Node3Box component23Node4Box
    .k (41/16) (by rfl) (by rfl)
    component23Node3_sound component23Node4_sound

private noncomputable def component23Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (1/16), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component23Node6_sound : Sound component23Node6Box :=
  sound_of_literal_split component23Node6Box component23Node2Box component23Node5Box
    .chi (5/64) (by rfl) (by rfl)
    component23Node2_sound component23Node5_sound

private noncomputable def component23Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (1/16), chiHi := (9/128) }

set_option maxRecDepth 1000000 in
private theorem component23Node7_sound : Sound component23Node7Box :=
  sound_of_literal_split component23Node7Box leaf968Box leaf969Box
    .k (43/16) (by rfl) (by rfl)
    leaf968FlatSound leaf969FlatSound

private noncomputable def component23Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (9/128), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component23Node8_sound : Sound component23Node8Box :=
  sound_of_literal_split component23Node8Box leaf970Box leaf971Box
    .k (43/16) (by rfl) (by rfl)
    leaf970FlatSound leaf971FlatSound

private noncomputable def component23Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (1/16), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component23Node9_sound : Sound component23Node9Box :=
  sound_of_literal_split component23Node9Box component23Node7Box component23Node8Box
    .chi (9/128) (by rfl) (by rfl)
    component23Node7_sound component23Node8_sound

private noncomputable def component23Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (5/64), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component23Node10_sound : Sound component23Node10Box :=
  sound_of_literal_split component23Node10Box leaf972Box leaf973Box
    .chi (11/128) (by rfl) (by rfl)
    leaf972FlatSound leaf973FlatSound

private noncomputable def component23Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (5/64), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component23Node11_sound : Sound component23Node11Box :=
  sound_of_literal_split component23Node11Box leaf974Box leaf975Box
    .chi (11/128) (by rfl) (by rfl)
    leaf974FlatSound leaf975FlatSound

private noncomputable def component23Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (5/64), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component23Node12_sound : Sound component23Node12Box :=
  sound_of_literal_split component23Node12Box component23Node10Box component23Node11Box
    .k (43/16) (by rfl) (by rfl)
    component23Node10_sound component23Node11_sound

private noncomputable def component23Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (1/16), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component23Node13_sound : Sound component23Node13Box :=
  sound_of_literal_split component23Node13Box component23Node9Box component23Node12Box
    .chi (5/64) (by rfl) (by rfl)
    component23Node9_sound component23Node12_sound

private noncomputable def component23Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (11/4), chiLo := (1/16), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component23Node14_sound : Sound component23Node14Box :=
  sound_of_literal_split component23Node14Box component23Node6Box component23Node13Box
    .k (21/8) (by rfl) (by rfl)
    component23Node6_sound component23Node13_sound

private noncomputable def component23Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (3/32), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component23Node15_sound : Sound component23Node15Box :=
  sound_of_literal_split component23Node15Box leaf976Box leaf977Box
    .chi (13/128) (by rfl) (by rfl)
    leaf976FlatSound leaf977FlatSound

private noncomputable def component23Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (3/32), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component23Node16_sound : Sound component23Node16Box :=
  sound_of_literal_split component23Node16Box leaf978Box leaf979Box
    .chi (13/128) (by rfl) (by rfl)
    leaf978FlatSound leaf979FlatSound

private noncomputable def component23Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (3/32), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component23Node17_sound : Sound component23Node17Box :=
  sound_of_literal_split component23Node17Box component23Node15Box component23Node16Box
    .k (41/16) (by rfl) (by rfl)
    component23Node15_sound component23Node16_sound

private noncomputable def component23Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (15/128), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component23Node18_sound : Sound component23Node18Box :=
  sound_of_literal_split component23Node18Box leaf981Box leaf982Box
    .k (81/32) (by rfl) (by rfl)
    leaf981FlatSound leaf982FlatSound

private noncomputable def component23Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (7/64), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component23Node19_sound : Sound component23Node19Box :=
  sound_of_literal_split component23Node19Box leaf980Box component23Node18Box
    .chi (15/128) (by rfl) (by rfl)
    leaf980FlatSound component23Node18_sound

private noncomputable def component23Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (7/64), chiHi := (15/128) }

set_option maxRecDepth 1000000 in
private theorem component23Node20_sound : Sound component23Node20Box :=
  sound_of_literal_split component23Node20Box leaf983Box leaf984Box
    .k (83/32) (by rfl) (by rfl)
    leaf983FlatSound leaf984FlatSound

private noncomputable def component23Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (15/128), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component23Node21_sound : Sound component23Node21Box :=
  sound_of_literal_split component23Node21Box leaf985Box leaf986Box
    .k (83/32) (by rfl) (by rfl)
    leaf985FlatSound leaf986FlatSound

private noncomputable def component23Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (7/64), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component23Node22_sound : Sound component23Node22Box :=
  sound_of_literal_split component23Node22Box component23Node20Box component23Node21Box
    .chi (15/128) (by rfl) (by rfl)
    component23Node20_sound component23Node21_sound

private noncomputable def component23Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (7/64), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component23Node23_sound : Sound component23Node23Box :=
  sound_of_literal_split component23Node23Box component23Node19Box component23Node22Box
    .k (41/16) (by rfl) (by rfl)
    component23Node19_sound component23Node22_sound

private noncomputable def component23Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (3/32), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component23Node24_sound : Sound component23Node24Box :=
  sound_of_literal_split component23Node24Box component23Node17Box component23Node23Box
    .chi (7/64) (by rfl) (by rfl)
    component23Node17_sound component23Node23_sound

private noncomputable def component23Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (3/32), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component23Node25_sound : Sound component23Node25Box :=
  sound_of_literal_split component23Node25Box leaf987Box leaf988Box
    .chi (13/128) (by rfl) (by rfl)
    leaf987FlatSound leaf988FlatSound

private noncomputable def component23Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (13/128), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component23Node26_sound : Sound component23Node26Box :=
  sound_of_literal_split component23Node26Box leaf990Box leaf991Box
    .k (87/32) (by rfl) (by rfl)
    leaf990FlatSound leaf991FlatSound

private noncomputable def component23Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (3/32), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component23Node27_sound : Sound component23Node27Box :=
  sound_of_literal_split component23Node27Box leaf989Box component23Node26Box
    .chi (13/128) (by rfl) (by rfl)
    leaf989FlatSound component23Node26_sound

private noncomputable def component23Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (3/32), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component23Node28_sound : Sound component23Node28Box :=
  sound_of_literal_split component23Node28Box component23Node25Box component23Node27Box
    .k (43/16) (by rfl) (by rfl)
    component23Node25_sound component23Node27_sound

private noncomputable def component23Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (7/64), chiHi := (15/128) }

set_option maxRecDepth 1000000 in
private theorem component23Node29_sound : Sound component23Node29Box :=
  sound_of_literal_split component23Node29Box leaf992Box leaf993Box
    .k (85/32) (by rfl) (by rfl)
    leaf992FlatSound leaf993FlatSound

private noncomputable def component23Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (15/128), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component23Node30_sound : Sound component23Node30Box :=
  sound_of_literal_split component23Node30Box leaf994Box leaf995Box
    .k (85/32) (by rfl) (by rfl)
    leaf994FlatSound leaf995FlatSound

private noncomputable def component23Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (7/64), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component23Node31_sound : Sound component23Node31Box :=
  sound_of_literal_split component23Node31Box component23Node29Box component23Node30Box
    .chi (15/128) (by rfl) (by rfl)
    component23Node29_sound component23Node30_sound

private noncomputable def component23Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (7/64), chiHi := (15/128) }

set_option maxRecDepth 1000000 in
private theorem component23Node32_sound : Sound component23Node32Box :=
  sound_of_literal_split component23Node32Box leaf996Box leaf997Box
    .k (87/32) (by rfl) (by rfl)
    leaf996FlatSound leaf997FlatSound

private noncomputable def component23Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (15/128), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component23Node33_sound : Sound component23Node33Box :=
  sound_of_literal_split component23Node33Box leaf998Box leaf999Box
    .k (87/32) (by rfl) (by rfl)
    leaf998FlatSound leaf999FlatSound

private noncomputable def component23Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (7/64), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component23Node34_sound : Sound component23Node34Box :=
  sound_of_literal_split component23Node34Box component23Node32Box component23Node33Box
    .chi (15/128) (by rfl) (by rfl)
    component23Node32_sound component23Node33_sound

private noncomputable def component23Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (7/64), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component23Node35_sound : Sound component23Node35Box :=
  sound_of_literal_split component23Node35Box component23Node31Box component23Node34Box
    .k (43/16) (by rfl) (by rfl)
    component23Node31_sound component23Node34_sound

private noncomputable def component23Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (3/32), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component23Node36_sound : Sound component23Node36Box :=
  sound_of_literal_split component23Node36Box component23Node28Box component23Node35Box
    .chi (7/64) (by rfl) (by rfl)
    component23Node28_sound component23Node35_sound

private noncomputable def component23Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (11/4), chiLo := (3/32), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component23Node37_sound : Sound component23Node37Box :=
  sound_of_literal_split component23Node37Box component23Node24Box component23Node36Box
    .k (21/8) (by rfl) (by rfl)
    component23Node24_sound component23Node36_sound

noncomputable def component23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (11/4), chiLo := (1/16), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
theorem component23_sound : Sound component23Box :=
  sound_of_literal_split component23Box component23Node14Box component23Node37Box
    .chi (3/32) (by rfl) (by rfl)
    component23Node14_sound component23Node37_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
