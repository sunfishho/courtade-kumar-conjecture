import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch7
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch8
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch12
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch5
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

private noncomputable def leaf6587Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (9/16), chiHi := (73/128) }

private noncomputable def leaf6587Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217971/134217728) }, vSqrt := { lower := (65529/65536), upper := (2642940849/2642775040) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (360663311/268435456) }, upper := { exponent := 1, mantissa := (5625/4096) } }, logOuter := sk123LogOuterCertificate, logK := sk123LogKCertificate, logChi := chi335LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (5285715889/5285550080) } }, logDArg := sk123LogDArgCertificate }

private noncomputable def leaf6587InnerLog : WideLogData :=
  innerPair346Data

set_option maxRecDepth 1000000 in
private theorem leaf6587LocalValidity :
    LeafFacts leaf6587Box leaf6587Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6587Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (2642940849/2642775040) }) = true
      norm_num [leaf6587Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6587CertificateValid :
    WideCertificateValid leaf6587Box leaf6587Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk123ValidityFacts chi335ValidityFacts
    leaf6587LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6587CoverageChecked :
    coverageCheck (innerAD leaf6587Box) leaf6587InnerLog = true := by
  rfl'

private theorem leaf6587InnerLogValid :
    leaf6587InnerLog.Valid 8 (innerAD leaf6587Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint93PositiveFacts.valid leaf6587CoverageChecked

private noncomputable def leaf6587InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629607/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6587InputLogOnePlusV_eq :
    leaf6587InputLogOnePlusV = outerEnclosure 24
      (leaf6587Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6587RoundedFacts : LeafRoundedFacts 8
    leaf6587Certificate.logOnePlusV leaf6587InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6587InputLogOnePlusV_eq }

private noncomputable def leaf6587Inputs : Inputs :=
  inputsOfCaches globalInput sk123RoundedInputs
    chi335InputQChi innerPair346Input
    leaf6587InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6587LowerChecked :
    lowerCheck 24 leaf6587Box leaf6587Inputs = true := by
  rfl'

private theorem leaf6587CoversExact : CoversExact 8
    leaf6587Box leaf6587Certificate leaf6587InnerLog leaf6587Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk123RoundedFacts chi335RoundedFacts
    innerPair346RoundedFacts leaf6587RoundedFacts (by rfl)

private theorem leaf6587FlatSound : Sound leaf6587Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6587CertificateValid
    leaf6587InnerLogValid leaf6587CoversExact leaf6587LowerChecked

private noncomputable def leaf6588Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (73/128), chiHi := (37/64) }

private noncomputable def leaf6588Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217973/134217728) }, vSqrt := { lower := (65529/65536), upper := (11452743679/11452008448) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (363808845/268435456) }, upper := { exponent := 1, mantissa := (2837/2048) } }, logOuter := sk123LogOuterCertificate, logK := sk123LogKCertificate, logChi := chi336LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (22904752127/22904016896) } }, logDArg := sk123LogDArgCertificate }

private noncomputable def leaf6588InnerLog : WideLogData :=
  innerPair353Data

set_option maxRecDepth 1000000 in
private theorem leaf6588LocalValidity :
    LeafFacts leaf6588Box leaf6588Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6588Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (11452743679/11452008448) }) = true
      norm_num [leaf6588Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6588CertificateValid :
    WideCertificateValid leaf6588Box leaf6588Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk123ValidityFacts chi336ValidityFacts
    leaf6588LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6588CoverageChecked :
    coverageCheck (innerAD leaf6588Box) leaf6588InnerLog = true := by
  rfl'

private theorem leaf6588InnerLogValid :
    leaf6588InnerLog.Valid 8 (innerAD leaf6588Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint96PositiveFacts.valid leaf6588CoverageChecked

private noncomputable def leaf6588InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629619/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6588InputLogOnePlusV_eq :
    leaf6588InputLogOnePlusV = outerEnclosure 24
      (leaf6588Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6588RoundedFacts : LeafRoundedFacts 8
    leaf6588Certificate.logOnePlusV leaf6588InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6588InputLogOnePlusV_eq }

private noncomputable def leaf6588Inputs : Inputs :=
  inputsOfCaches globalInput sk123RoundedInputs
    chi336InputQChi innerPair353Input
    leaf6588InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6588LowerChecked :
    lowerCheck 24 leaf6588Box leaf6588Inputs = true := by
  rfl'

private theorem leaf6588CoversExact : CoversExact 8
    leaf6588Box leaf6588Certificate leaf6588InnerLog leaf6588Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk123RoundedFacts chi336RoundedFacts
    innerPair353RoundedFacts leaf6588RoundedFacts (by rfl)

private theorem leaf6588FlatSound : Sound leaf6588Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6588CertificateValid
    leaf6588InnerLogValid leaf6588CoversExact leaf6588LowerChecked

private noncomputable def leaf6589Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (37/64), chiHi := (75/128) }

private noncomputable def leaf6589Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217975/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34355975168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (366954379/268435456) }, upper := { exponent := 1, mantissa := (5723/4096) } }, logOuter := sk123LogOuterCertificate, logK := sk123LogKCertificate, logChi := chi337LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68714206205/68711950336) } }, logDArg := sk123LogDArgCertificate }

private noncomputable def leaf6589InnerLog : WideLogData :=
  innerPair353Data

set_option maxRecDepth 1000000 in
private theorem leaf6589LocalValidity :
    LeafFacts leaf6589Box leaf6589Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6589Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34355975168) }) = true
      norm_num [leaf6589Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6589CertificateValid :
    WideCertificateValid leaf6589Box leaf6589Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk123ValidityFacts chi337ValidityFacts
    leaf6589LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6589CoverageChecked :
    coverageCheck (innerAD leaf6589Box) leaf6589InnerLog = true := by
  rfl'

private theorem leaf6589InnerLogValid :
    leaf6589InnerLog.Valid 8 (innerAD leaf6589Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint96PositiveFacts.valid leaf6589CoverageChecked

private noncomputable def leaf6589InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (181713/262144) }

set_option maxRecDepth 1000000 in
private theorem leaf6589InputLogOnePlusV_eq :
    leaf6589InputLogOnePlusV = outerEnclosure 24
      (leaf6589Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6589RoundedFacts : LeafRoundedFacts 8
    leaf6589Certificate.logOnePlusV leaf6589InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6589InputLogOnePlusV_eq }

private noncomputable def leaf6589Inputs : Inputs :=
  inputsOfCaches globalInput sk123RoundedInputs
    chi337InputQChi innerPair353Input
    leaf6589InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6589LowerChecked :
    lowerCheck 24 leaf6589Box leaf6589Inputs = true := by
  rfl'

private theorem leaf6589CoversExact : CoversExact 8
    leaf6589Box leaf6589Certificate leaf6589InnerLog leaf6589Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk123RoundedFacts chi337RoundedFacts
    innerPair353RoundedFacts leaf6589RoundedFacts (by rfl)

private theorem leaf6589FlatSound : Sound leaf6589Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6589CertificateValid
    leaf6589InnerLogValid leaf6589CoversExact leaf6589LowerChecked

private noncomputable def leaf6590Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (75/128), chiHi := (19/32) }

private noncomputable def leaf6590Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217977/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34355924992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (370099913/268435456) }, upper := { exponent := 1, mantissa := (1443/1024) } }, logOuter := sk123LogOuterCertificate, logK := sk123LogKCertificate, logChi := chi338LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68714156029/68711849984) } }, logDArg := sk123LogDArgCertificate }

private noncomputable def leaf6590InnerLog : WideLogData :=
  innerPair357Data

set_option maxRecDepth 1000000 in
private theorem leaf6590LocalValidity :
    LeafFacts leaf6590Box leaf6590Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6590Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34355924992) }) = true
      norm_num [leaf6590Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6590CertificateValid :
    WideCertificateValid leaf6590Box leaf6590Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk123ValidityFacts chi338ValidityFacts
    leaf6590LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6590CoverageChecked :
    coverageCheck (innerAD leaf6590Box) leaf6590InnerLog = true := by
  rfl'

private theorem leaf6590InnerLogValid :
    leaf6590InnerLog.Valid 8 (innerAD leaf6590Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint97PositiveFacts.valid leaf6590CoverageChecked

private noncomputable def leaf6590InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907411/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6590InputLogOnePlusV_eq :
    leaf6590InputLogOnePlusV = outerEnclosure 24
      (leaf6590Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6590RoundedFacts : LeafRoundedFacts 8
    leaf6590Certificate.logOnePlusV leaf6590InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6590InputLogOnePlusV_eq }

private noncomputable def leaf6590Inputs : Inputs :=
  inputsOfCaches globalInput sk123RoundedInputs
    chi338InputQChi innerPair357Input
    leaf6590InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6590LowerChecked :
    lowerCheck 24 leaf6590Box leaf6590Inputs = true := by
  rfl'

private theorem leaf6590CoversExact : CoversExact 8
    leaf6590Box leaf6590Certificate leaf6590InnerLog leaf6590Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk123RoundedFacts chi338RoundedFacts
    innerPair357RoundedFacts leaf6590RoundedFacts (by rfl)

private theorem leaf6590FlatSound : Sound leaf6590Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6590CertificateValid
    leaf6590InnerLogValid leaf6590CoversExact leaf6590LowerChecked

private noncomputable def leaf6591Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (9/16), chiHi := (73/128) }

private noncomputable def leaf6591Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217973/134217728) }, vSqrt := { lower := (65529/65536), upper := (11452743679/11452000256) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (365381613/268435456) }, upper := { exponent := 1, mantissa := (2849/2048) } }, logOuter := sk124LogOuterCertificate, logK := sk124LogKCertificate, logChi := chi335LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (22904743935/22904000512) } }, logDArg := sk124LogDArgCertificate }

private noncomputable def leaf6591InnerLog : WideLogData :=
  innerPair353Data

set_option maxRecDepth 1000000 in
private theorem leaf6591LocalValidity :
    LeafFacts leaf6591Box leaf6591Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6591Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (11452743679/11452000256) }) = true
      norm_num [leaf6591Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6591CertificateValid :
    WideCertificateValid leaf6591Box leaf6591Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk124ValidityFacts chi335ValidityFacts
    leaf6591LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6591CoverageChecked :
    coverageCheck (innerAD leaf6591Box) leaf6591InnerLog = true := by
  rfl'

private theorem leaf6591InnerLogValid :
    leaf6591InnerLog.Valid 8 (innerAD leaf6591Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint96PositiveFacts.valid leaf6591CoverageChecked

private noncomputable def leaf6591InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629625/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6591InputLogOnePlusV_eq :
    leaf6591InputLogOnePlusV = outerEnclosure 24
      (leaf6591Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6591RoundedFacts : LeafRoundedFacts 8
    leaf6591Certificate.logOnePlusV leaf6591InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6591InputLogOnePlusV_eq }

private noncomputable def leaf6591Inputs : Inputs :=
  inputsOfCaches globalInput sk124RoundedInputs
    chi335InputQChi innerPair353Input
    leaf6591InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6591LowerChecked :
    lowerCheck 24 leaf6591Box leaf6591Inputs = true := by
  rfl'

private theorem leaf6591CoversExact : CoversExact 8
    leaf6591Box leaf6591Certificate leaf6591InnerLog leaf6591Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk124RoundedFacts chi335RoundedFacts
    innerPair353RoundedFacts leaf6591RoundedFacts (by rfl)

private theorem leaf6591FlatSound : Sound leaf6591Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6591CertificateValid
    leaf6591InnerLogValid leaf6591CoversExact leaf6591LowerChecked

private noncomputable def leaf6592Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (73/128), chiHi := (37/64) }

private noncomputable def leaf6592Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217975/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34355949568) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (368592679/268435456) }, upper := { exponent := 1, mantissa := (1437/1024) } }, logOuter := sk124LogOuterCertificate, logK := sk124LogKCertificate, logChi := chi336LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68714180605/68711899136) } }, logDArg := sk124LogDArgCertificate }

private noncomputable def leaf6592InnerLog : WideLogData :=
  innerPair353Data

set_option maxRecDepth 1000000 in
private theorem leaf6592LocalValidity :
    LeafFacts leaf6592Box leaf6592Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6592Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34355949568) }) = true
      norm_num [leaf6592Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6592CertificateValid :
    WideCertificateValid leaf6592Box leaf6592Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk124ValidityFacts chi336ValidityFacts
    leaf6592LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6592CoverageChecked :
    coverageCheck (innerAD leaf6592Box) leaf6592InnerLog = true := by
  rfl'

private theorem leaf6592InnerLogValid :
    leaf6592InnerLog.Valid 8 (innerAD leaf6592Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint96PositiveFacts.valid leaf6592CoverageChecked

private noncomputable def leaf6592InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814819/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6592InputLogOnePlusV_eq :
    leaf6592InputLogOnePlusV = outerEnclosure 24
      (leaf6592Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6592RoundedFacts : LeafRoundedFacts 8
    leaf6592Certificate.logOnePlusV leaf6592InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6592InputLogOnePlusV_eq }

private noncomputable def leaf6592Inputs : Inputs :=
  inputsOfCaches globalInput sk124RoundedInputs
    chi336InputQChi innerPair353Input
    leaf6592InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6592LowerChecked :
    lowerCheck 24 leaf6592Box leaf6592Inputs = true := by
  rfl'

private theorem leaf6592CoversExact : CoversExact 8
    leaf6592Box leaf6592Certificate leaf6592InnerLog leaf6592Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk124RoundedFacts chi336RoundedFacts
    innerPair353RoundedFacts leaf6592RoundedFacts (by rfl)

private theorem leaf6592FlatSound : Sound leaf6592Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6592CertificateValid
    leaf6592InnerLogValid leaf6592CoversExact leaf6592LowerChecked

private noncomputable def leaf6593Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (37/64), chiHi := (75/128) }

private noncomputable def leaf6593Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217977/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34355898368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (371803745/268435456) }, upper := { exponent := 1, mantissa := (2899/2048) } }, logOuter := sk124LogOuterCertificate, logK := sk124LogKCertificate, logChi := chi337LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68714129405/68711796736) } }, logDArg := sk124LogDArgCertificate }

private noncomputable def leaf6593InnerLog : WideLogData :=
  innerPair357Data

set_option maxRecDepth 1000000 in
private theorem leaf6593LocalValidity :
    LeafFacts leaf6593Box leaf6593Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6593Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34355898368) }) = true
      norm_num [leaf6593Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6593CertificateValid :
    WideCertificateValid leaf6593Box leaf6593Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk124ValidityFacts chi337ValidityFacts
    leaf6593LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6593CoverageChecked :
    coverageCheck (innerAD leaf6593Box) leaf6593InnerLog = true := by
  rfl'

private theorem leaf6593InnerLogValid :
    leaf6593InnerLog.Valid 8 (innerAD leaf6593Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint97PositiveFacts.valid leaf6593CoverageChecked

private noncomputable def leaf6593InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814825/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6593InputLogOnePlusV_eq :
    leaf6593InputLogOnePlusV = outerEnclosure 24
      (leaf6593Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6593RoundedFacts : LeafRoundedFacts 8
    leaf6593Certificate.logOnePlusV leaf6593InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6593InputLogOnePlusV_eq }

private noncomputable def leaf6593Inputs : Inputs :=
  inputsOfCaches globalInput sk124RoundedInputs
    chi337InputQChi innerPair357Input
    leaf6593InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6593LowerChecked :
    lowerCheck 24 leaf6593Box leaf6593Inputs = true := by
  rfl'

private theorem leaf6593CoversExact : CoversExact 8
    leaf6593Box leaf6593Certificate leaf6593InnerLog leaf6593Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk124RoundedFacts chi337RoundedFacts
    innerPair357RoundedFacts leaf6593RoundedFacts (by rfl)

private theorem leaf6593FlatSound : Sound leaf6593Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6593CertificateValid
    leaf6593InnerLogValid leaf6593CoversExact leaf6593LowerChecked

private noncomputable def leaf6594Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (75/128), chiHi := (19/32) }

private noncomputable def leaf6594Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217979/134217728) }, vSqrt := { lower := (65529/65536), upper := (11452743679/11451949056) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (375014811/268435456) }, upper := { exponent := 1, mantissa := (731/512) } }, logOuter := sk124LogOuterCertificate, logK := sk124LogKCertificate, logChi := chi338LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (22904692735/22903898112) } }, logDArg := sk124LogDArgCertificate }

private noncomputable def leaf6594InnerLog : WideLogData :=
  innerPair357Data

set_option maxRecDepth 1000000 in
private theorem leaf6594LocalValidity :
    LeafFacts leaf6594Box leaf6594Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6594Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (11452743679/11451949056) }) = true
      norm_num [leaf6594Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6594CertificateValid :
    WideCertificateValid leaf6594Box leaf6594Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk124ValidityFacts chi338ValidityFacts
    leaf6594LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6594CoverageChecked :
    coverageCheck (innerAD leaf6594Box) leaf6594InnerLog = true := by
  rfl'

private theorem leaf6594InnerLogValid :
    leaf6594InnerLog.Valid 8 (innerAD leaf6594Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint97PositiveFacts.valid leaf6594CoverageChecked

private noncomputable def leaf6594InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629663/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6594InputLogOnePlusV_eq :
    leaf6594InputLogOnePlusV = outerEnclosure 24
      (leaf6594Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6594RoundedFacts : LeafRoundedFacts 8
    leaf6594Certificate.logOnePlusV leaf6594InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6594InputLogOnePlusV_eq }

private noncomputable def leaf6594Inputs : Inputs :=
  inputsOfCaches globalInput sk124RoundedInputs
    chi338InputQChi innerPair357Input
    leaf6594InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6594LowerChecked :
    lowerCheck 24 leaf6594Box leaf6594Inputs = true := by
  rfl'

private theorem leaf6594CoversExact : CoversExact 8
    leaf6594Box leaf6594Certificate leaf6594InnerLog leaf6594Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk124RoundedFacts chi338RoundedFacts
    innerPair357RoundedFacts leaf6594RoundedFacts (by rfl)

private theorem leaf6594FlatSound : Sound leaf6594Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6594CertificateValid
    leaf6594InnerLogValid leaf6594CoversExact leaf6594LowerChecked

private noncomputable def leaf6595Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (19/32), chiHi := (77/128) }

private noncomputable def leaf6595Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217979/134217728) }, vSqrt := { lower := (65529/65536), upper := (11452743679/11451958272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (373245447/268435456) }, upper := { exponent := 1, mantissa := (5821/4096) } }, logOuter := sk123LogOuterCertificate, logK := sk123LogKCertificate, logChi := chi339LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (22904701951/22903916544) } }, logDArg := sk123LogDArgCertificate }

private noncomputable def leaf6595InnerLog : WideLogData :=
  innerPair357Data

set_option maxRecDepth 1000000 in
private theorem leaf6595LocalValidity :
    LeafFacts leaf6595Box leaf6595Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6595Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (11452743679/11451958272) }) = true
      norm_num [leaf6595Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6595CertificateValid :
    WideCertificateValid leaf6595Box leaf6595Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk123ValidityFacts chi339ValidityFacts
    leaf6595LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6595CoverageChecked :
    coverageCheck (innerAD leaf6595Box) leaf6595InnerLog = true := by
  rfl'

private theorem leaf6595InnerLogValid :
    leaf6595InnerLog.Valid 8 (innerAD leaf6595Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint97PositiveFacts.valid leaf6595CoverageChecked

private noncomputable def leaf6595InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453707/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf6595InputLogOnePlusV_eq :
    leaf6595InputLogOnePlusV = outerEnclosure 24
      (leaf6595Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6595RoundedFacts : LeafRoundedFacts 8
    leaf6595Certificate.logOnePlusV leaf6595InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6595InputLogOnePlusV_eq }

private noncomputable def leaf6595Inputs : Inputs :=
  inputsOfCaches globalInput sk123RoundedInputs
    chi339InputQChi innerPair357Input
    leaf6595InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6595LowerChecked :
    lowerCheck 24 leaf6595Box leaf6595Inputs = true := by
  rfl'

private theorem leaf6595CoversExact : CoversExact 8
    leaf6595Box leaf6595Certificate leaf6595InnerLog leaf6595Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk123RoundedFacts chi339RoundedFacts
    innerPair357RoundedFacts leaf6595RoundedFacts (by rfl)

private theorem leaf6595FlatSound : Sound leaf6595Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6595CertificateValid
    leaf6595InnerLogValid leaf6595CoversExact leaf6595LowerChecked

private noncomputable def leaf6596Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (77/128), chiHi := (39/64) }

private noncomputable def leaf6596Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217981/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34355824640) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (376390981/268435456) }, upper := { exponent := 1, mantissa := (2935/2048) } }, logOuter := sk123LogOuterCertificate, logK := sk123LogKCertificate, logChi := chi340LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68714055677/68711649280) } }, logDArg := sk123LogDArgCertificate }

private noncomputable def leaf6596InnerLog : WideLogData :=
  innerPair357Data

set_option maxRecDepth 1000000 in
private theorem leaf6596LocalValidity :
    LeafFacts leaf6596Box leaf6596Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6596Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34355824640) }) = true
      norm_num [leaf6596Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6596CertificateValid :
    WideCertificateValid leaf6596Box leaf6596Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk123ValidityFacts chi340ValidityFacts
    leaf6596LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6596CoverageChecked :
    coverageCheck (innerAD leaf6596Box) leaf6596InnerLog = true := by
  rfl'

private theorem leaf6596InnerLogValid :
    leaf6596InnerLog.Valid 8 (innerAD leaf6596Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint97PositiveFacts.valid leaf6596CoverageChecked

private noncomputable def leaf6596InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907417/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6596InputLogOnePlusV_eq :
    leaf6596InputLogOnePlusV = outerEnclosure 24
      (leaf6596Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6596RoundedFacts : LeafRoundedFacts 8
    leaf6596Certificate.logOnePlusV leaf6596InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6596InputLogOnePlusV_eq }

private noncomputable def leaf6596Inputs : Inputs :=
  inputsOfCaches globalInput sk123RoundedInputs
    chi340InputQChi innerPair357Input
    leaf6596InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6596LowerChecked :
    lowerCheck 24 leaf6596Box leaf6596Inputs = true := by
  rfl'

private theorem leaf6596CoversExact : CoversExact 8
    leaf6596Box leaf6596Certificate leaf6596InnerLog leaf6596Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk123RoundedFacts chi340RoundedFacts
    innerPair357RoundedFacts leaf6596RoundedFacts (by rfl)

private theorem leaf6596FlatSound : Sound leaf6596Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6596CertificateValid
    leaf6596InnerLogValid leaf6596CoversExact leaf6596LowerChecked

private noncomputable def leaf6597Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (39/64), chiHi := (5/8) }

private noncomputable def leaf6597Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109041/67108864) }, vSqrt := { lower := (65529/65536), upper := (11452743679/11451908096) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (189751825/134217728) }, upper := { exponent := 1, mantissa := (373/256) } }, logOuter := sk123LogOuterCertificate, logK := sk123LogKCertificate, logChi := chi322LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (22904651775/22903816192) } }, logDArg := sk123LogDArgCertificate }

private noncomputable def leaf6597InnerLog : WideLogData :=
  innerPair825Data

set_option maxRecDepth 1000000 in
private theorem leaf6597LocalValidity :
    LeafFacts leaf6597Box leaf6597Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6597Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (11452743679/11451908096) }) = true
      norm_num [leaf6597Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6597CertificateValid :
    WideCertificateValid leaf6597Box leaf6597Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk123ValidityFacts chi322ValidityFacts
    leaf6597LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6597CoverageChecked :
    coverageCheck (innerAD leaf6597Box) leaf6597InnerLog = true := by
  rfl'

private theorem leaf6597InnerLogValid :
    leaf6597InnerLog.Valid 8 (innerAD leaf6597Box) :=
  wideLogDataValid_of_cachedCheck endpoint516PositiveFacts
    endpoint517PositiveFacts.valid leaf6597CoverageChecked

private noncomputable def leaf6597InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629693/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6597InputLogOnePlusV_eq :
    leaf6597InputLogOnePlusV = outerEnclosure 24
      (leaf6597Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6597RoundedFacts : LeafRoundedFacts 8
    leaf6597Certificate.logOnePlusV leaf6597InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6597InputLogOnePlusV_eq }

private noncomputable def leaf6597Inputs : Inputs :=
  inputsOfCaches globalInput sk123RoundedInputs
    chi322InputQChi innerPair825Input
    leaf6597InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6597LowerChecked :
    lowerCheck 24 leaf6597Box leaf6597Inputs = true := by
  rfl'

private theorem leaf6597CoversExact : CoversExact 8
    leaf6597Box leaf6597Certificate leaf6597InnerLog leaf6597Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk123RoundedFacts chi322RoundedFacts
    innerPair825RoundedFacts leaf6597RoundedFacts (by rfl)

private theorem leaf6597FlatSound : Sound leaf6597Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6597CertificateValid
    leaf6597InnerLogValid leaf6597CoversExact leaf6597LowerChecked

private noncomputable def leaf6598Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (19/32), chiHi := (77/128) }

private noncomputable def leaf6598Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217981/134217728) }, vSqrt := { lower := (65529/65536), upper := (2642940849/2642753536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (378225877/268435456) }, upper := { exponent := 1, mantissa := (2949/2048) } }, logOuter := sk124LogOuterCertificate, logK := sk124LogKCertificate, logChi := chi339LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (5285694385/5285507072) } }, logDArg := sk124LogDArgCertificate }

private noncomputable def leaf6598InnerLog : WideLogData :=
  innerPair368Data

set_option maxRecDepth 1000000 in
private theorem leaf6598LocalValidity :
    LeafFacts leaf6598Box leaf6598Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6598Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (2642940849/2642753536) }) = true
      norm_num [leaf6598Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6598CertificateValid :
    WideCertificateValid leaf6598Box leaf6598Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk124ValidityFacts chi339ValidityFacts
    leaf6598LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6598CoverageChecked :
    coverageCheck (innerAD leaf6598Box) leaf6598InnerLog = true := by
  rfl'

private theorem leaf6598InnerLogValid :
    leaf6598InnerLog.Valid 8 (innerAD leaf6598Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint98PositiveFacts.valid leaf6598CoverageChecked

private noncomputable def leaf6598InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629675/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6598InputLogOnePlusV_eq :
    leaf6598InputLogOnePlusV = outerEnclosure 24
      (leaf6598Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6598RoundedFacts : LeafRoundedFacts 8
    leaf6598Certificate.logOnePlusV leaf6598InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6598InputLogOnePlusV_eq }

private noncomputable def leaf6598Inputs : Inputs :=
  inputsOfCaches globalInput sk124RoundedInputs
    chi339InputQChi innerPair368Input
    leaf6598InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6598LowerChecked :
    lowerCheck 24 leaf6598Box leaf6598Inputs = true := by
  rfl'

private theorem leaf6598CoversExact : CoversExact 8
    leaf6598Box leaf6598Certificate leaf6598InnerLog leaf6598Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk124RoundedFacts chi339RoundedFacts
    innerPair368RoundedFacts leaf6598RoundedFacts (by rfl)

private theorem leaf6598FlatSound : Sound leaf6598Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6598CertificateValid
    leaf6598InnerLogValid leaf6598CoversExact leaf6598LowerChecked

private noncomputable def leaf6599Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (77/128), chiHi := (39/64) }

private noncomputable def leaf6599Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217983/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34355744768) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (381436943/268435456) }, upper := { exponent := 1, mantissa := (1487/1024) } }, logOuter := sk124LogOuterCertificate, logK := sk124LogKCertificate, logChi := chi340LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68713975805/68711489536) } }, logDArg := sk124LogDArgCertificate }

private noncomputable def leaf6599InnerLog : WideLogData :=
  innerPair368Data

set_option maxRecDepth 1000000 in
private theorem leaf6599LocalValidity :
    LeafFacts leaf6599Box leaf6599Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6599Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34355744768) }) = true
      norm_num [leaf6599Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6599CertificateValid :
    WideCertificateValid leaf6599Box leaf6599Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk124ValidityFacts chi340ValidityFacts
    leaf6599LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6599CoverageChecked :
    coverageCheck (innerAD leaf6599Box) leaf6599InnerLog = true := by
  rfl'

private theorem leaf6599InnerLogValid :
    leaf6599InnerLog.Valid 8 (innerAD leaf6599Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint98PositiveFacts.valid leaf6599CoverageChecked

private noncomputable def leaf6599InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453711/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf6599InputLogOnePlusV_eq :
    leaf6599InputLogOnePlusV = outerEnclosure 24
      (leaf6599Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6599RoundedFacts : LeafRoundedFacts 8
    leaf6599Certificate.logOnePlusV leaf6599InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6599InputLogOnePlusV_eq }

private noncomputable def leaf6599Inputs : Inputs :=
  inputsOfCaches globalInput sk124RoundedInputs
    chi340InputQChi innerPair368Input
    leaf6599InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6599LowerChecked :
    lowerCheck 24 leaf6599Box leaf6599Inputs = true := by
  rfl'

private theorem leaf6599CoversExact : CoversExact 8
    leaf6599Box leaf6599Certificate leaf6599InnerLog leaf6599Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk124RoundedFacts chi340RoundedFacts
    innerPair368RoundedFacts leaf6599RoundedFacts (by rfl)

private theorem leaf6599FlatSound : Sound leaf6599Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6599CertificateValid
    leaf6599InnerLogValid leaf6599CoversExact leaf6599LowerChecked

private noncomputable def leaf6600Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (39/64), chiHi := (79/128) }

private noncomputable def leaf6600Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217985/134217728) }, vSqrt := { lower := (65529/65536), upper := (161306249/161294336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (384648009/268435456) }, upper := { exponent := 1, mantissa := (2999/2048) } }, logOuter := sk124LogOuterCertificate, logK := sk124LogKCertificate, logChi := chi347LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (322600585/322588672) } }, logDArg := sk124LogDArgCertificate }

private noncomputable def leaf6600InnerLog : WideLogData :=
  innerPair368Data

set_option maxRecDepth 1000000 in
private theorem leaf6600LocalValidity :
    LeafFacts leaf6600Box leaf6600Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6600Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (161306249/161294336) }) = true
      norm_num [leaf6600Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6600CertificateValid :
    WideCertificateValid leaf6600Box leaf6600Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk124ValidityFacts chi347ValidityFacts
    leaf6600LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6600CoverageChecked :
    coverageCheck (innerAD leaf6600Box) leaf6600InnerLog = true := by
  rfl'

private theorem leaf6600InnerLogValid :
    leaf6600InnerLog.Valid 8 (innerAD leaf6600Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint98PositiveFacts.valid leaf6600CoverageChecked

private noncomputable def leaf6600InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907425/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6600InputLogOnePlusV_eq :
    leaf6600InputLogOnePlusV = outerEnclosure 24
      (leaf6600Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6600RoundedFacts : LeafRoundedFacts 8
    leaf6600Certificate.logOnePlusV leaf6600InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6600InputLogOnePlusV_eq }

private noncomputable def leaf6600Inputs : Inputs :=
  inputsOfCaches globalInput sk124RoundedInputs
    chi347InputQChi innerPair368Input
    leaf6600InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6600LowerChecked :
    lowerCheck 24 leaf6600Box leaf6600Inputs = true := by
  rfl'

private theorem leaf6600CoversExact : CoversExact 8
    leaf6600Box leaf6600Certificate leaf6600InnerLog leaf6600Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk124RoundedFacts chi347RoundedFacts
    innerPair368RoundedFacts leaf6600RoundedFacts (by rfl)

private theorem leaf6600FlatSound : Sound leaf6600Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6600CertificateValid
    leaf6600InnerLogValid leaf6600CoversExact leaf6600LowerChecked

private noncomputable def leaf6601Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (79/128), chiHi := (5/8) }

private noncomputable def leaf6601Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217987/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34355642368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (387859075/268435456) }, upper := { exponent := 1, mantissa := (189/128) } }, logOuter := sk124LogOuterCertificate, logK := sk124LogKCertificate, logChi := chi348LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68713873405/68711284736) } }, logDArg := sk124LogDArgCertificate }

private noncomputable def leaf6601InnerLog : WideLogData :=
  innerPair372Data

set_option maxRecDepth 1000000 in
private theorem leaf6601LocalValidity :
    LeafFacts leaf6601Box leaf6601Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6601Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34355642368) }) = true
      norm_num [leaf6601Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6601CertificateValid :
    WideCertificateValid leaf6601Box leaf6601Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk124ValidityFacts chi348ValidityFacts
    leaf6601LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6601CoverageChecked :
    coverageCheck (innerAD leaf6601Box) leaf6601InnerLog = true := by
  rfl'

private theorem leaf6601InnerLogValid :
    leaf6601InnerLog.Valid 8 (innerAD leaf6601Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint99PositiveFacts.valid leaf6601CoverageChecked

private noncomputable def leaf6601InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629713/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6601InputLogOnePlusV_eq :
    leaf6601InputLogOnePlusV = outerEnclosure 24
      (leaf6601Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6601RoundedFacts : LeafRoundedFacts 8
    leaf6601Certificate.logOnePlusV leaf6601InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6601InputLogOnePlusV_eq }

private noncomputable def leaf6601Inputs : Inputs :=
  inputsOfCaches globalInput sk124RoundedInputs
    chi348InputQChi innerPair372Input
    leaf6601InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6601LowerChecked :
    lowerCheck 24 leaf6601Box leaf6601Inputs = true := by
  rfl'

private theorem leaf6601CoversExact : CoversExact 8
    leaf6601Box leaf6601Certificate leaf6601InnerLog leaf6601Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk124RoundedFacts chi348RoundedFacts
    innerPair372RoundedFacts leaf6601RoundedFacts (by rfl)

private theorem leaf6601FlatSound : Sound leaf6601Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6601CertificateValid
    leaf6601InnerLogValid leaf6601CoversExact leaf6601LowerChecked

private noncomputable def leaf6602Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (9/16), chiHi := (73/128) }

private noncomputable def leaf6602Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217975/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34355926016) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (370099915/268435456) }, upper := { exponent := 1, mantissa := (5771/4096) } }, logOuter := sk125LogOuterCertificate, logK := sk125LogKCertificate, logChi := chi335LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68714157053/68711852032) } }, logDArg := sk125LogDArgCertificate }

private noncomputable def leaf6602InnerLog : WideLogData :=
  innerPair359Data

set_option maxRecDepth 1000000 in
private theorem leaf6602LocalValidity :
    LeafFacts leaf6602Box leaf6602Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6602Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34355926016) }) = true
      norm_num [leaf6602Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6602CertificateValid :
    WideCertificateValid leaf6602Box leaf6602Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk125ValidityFacts chi335ValidityFacts
    leaf6602LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6602CoverageChecked :
    coverageCheck (innerAD leaf6602Box) leaf6602InnerLog = true := by
  rfl'

private theorem leaf6602InnerLogValid :
    leaf6602InnerLog.Valid 8 (innerAD leaf6602Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint464PositiveFacts.valid leaf6602CoverageChecked

private noncomputable def leaf6602InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907411/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6602InputLogOnePlusV_eq :
    leaf6602InputLogOnePlusV = outerEnclosure 24
      (leaf6602Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6602RoundedFacts : LeafRoundedFacts 8
    leaf6602Certificate.logOnePlusV leaf6602InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6602InputLogOnePlusV_eq }

private noncomputable def leaf6602Inputs : Inputs :=
  inputsOfCaches globalInput sk125RoundedInputs
    chi335InputQChi innerPair359Input
    leaf6602InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6602LowerChecked :
    lowerCheck 24 leaf6602Box leaf6602Inputs = true := by
  rfl'

private theorem leaf6602CoversExact : CoversExact 8
    leaf6602Box leaf6602Certificate leaf6602InnerLog leaf6602Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk125RoundedFacts chi335RoundedFacts
    innerPair359RoundedFacts leaf6602RoundedFacts (by rfl)

private theorem leaf6602FlatSound : Sound leaf6602Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6602CertificateValid
    leaf6602InnerLogValid leaf6602CoversExact leaf6602LowerChecked

private noncomputable def leaf6603Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (73/128), chiHi := (37/64) }

private noncomputable def leaf6603Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217977/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34355873792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (373376513/268435456) }, upper := { exponent := 1, mantissa := (2911/2048) } }, logOuter := sk125LogOuterCertificate, logK := sk125LogKCertificate, logChi := chi336LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68714104829/68711747584) } }, logDArg := sk125LogDArgCertificate }

private noncomputable def leaf6603InnerLog : WideLogData :=
  innerPair357Data

set_option maxRecDepth 1000000 in
private theorem leaf6603LocalValidity :
    LeafFacts leaf6603Box leaf6603Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6603Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34355873792) }) = true
      norm_num [leaf6603Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6603CertificateValid :
    WideCertificateValid leaf6603Box leaf6603Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk125ValidityFacts chi336ValidityFacts
    leaf6603LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6603CoverageChecked :
    coverageCheck (innerAD leaf6603Box) leaf6603InnerLog = true := by
  rfl'

private theorem leaf6603InnerLogValid :
    leaf6603InnerLog.Valid 8 (innerAD leaf6603Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint97PositiveFacts.valid leaf6603CoverageChecked

private noncomputable def leaf6603InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453707/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf6603InputLogOnePlusV_eq :
    leaf6603InputLogOnePlusV = outerEnclosure 24
      (leaf6603Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6603RoundedFacts : LeafRoundedFacts 8
    leaf6603Certificate.logOnePlusV leaf6603InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6603InputLogOnePlusV_eq }

private noncomputable def leaf6603Inputs : Inputs :=
  inputsOfCaches globalInput sk125RoundedInputs
    chi336InputQChi innerPair357Input
    leaf6603InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6603LowerChecked :
    lowerCheck 24 leaf6603Box leaf6603Inputs = true := by
  rfl'

private theorem leaf6603CoversExact : CoversExact 8
    leaf6603Box leaf6603Certificate leaf6603InnerLog leaf6603Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk125RoundedFacts chi336RoundedFacts
    innerPair357RoundedFacts leaf6603RoundedFacts (by rfl)

private theorem leaf6603FlatSound : Sound leaf6603Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6603CertificateValid
    leaf6603InnerLogValid leaf6603CoversExact leaf6603LowerChecked

private noncomputable def leaf6604Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (9/16), chiHi := (73/128) }

private noncomputable def leaf6604Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217977/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34355851264) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (374818217/268435456) }, upper := { exponent := 1, mantissa := (1461/1024) } }, logOuter := sk126LogOuterCertificate, logK := sk126LogKCertificate, logChi := chi335LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68714082301/68711702528) } }, logDArg := sk126LogDArgCertificate }

private noncomputable def leaf6604InnerLog : WideLogData :=
  innerPair357Data

set_option maxRecDepth 1000000 in
private theorem leaf6604LocalValidity :
    LeafFacts leaf6604Box leaf6604Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6604Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34355851264) }) = true
      norm_num [leaf6604Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6604CertificateValid :
    WideCertificateValid leaf6604Box leaf6604Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk126ValidityFacts chi335ValidityFacts
    leaf6604LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6604CoverageChecked :
    coverageCheck (innerAD leaf6604Box) leaf6604InnerLog = true := by
  rfl'

private theorem leaf6604InnerLogValid :
    leaf6604InnerLog.Valid 8 (innerAD leaf6604Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint97PositiveFacts.valid leaf6604CoverageChecked

private noncomputable def leaf6604InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814831/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6604InputLogOnePlusV_eq :
    leaf6604InputLogOnePlusV = outerEnclosure 24
      (leaf6604Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6604RoundedFacts : LeafRoundedFacts 8
    leaf6604Certificate.logOnePlusV leaf6604InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6604InputLogOnePlusV_eq }

private noncomputable def leaf6604Inputs : Inputs :=
  inputsOfCaches globalInput sk126RoundedInputs
    chi335InputQChi innerPair357Input
    leaf6604InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6604LowerChecked :
    lowerCheck 24 leaf6604Box leaf6604Inputs = true := by
  rfl'

private theorem leaf6604CoversExact : CoversExact 8
    leaf6604Box leaf6604Certificate leaf6604InnerLog leaf6604Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk126RoundedFacts chi335RoundedFacts
    innerPair357RoundedFacts leaf6604RoundedFacts (by rfl)

private theorem leaf6604FlatSound : Sound leaf6604Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6604CertificateValid
    leaf6604InnerLogValid leaf6604CoversExact leaf6604LowerChecked

private noncomputable def leaf6605Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (73/128), chiHi := (37/64) }

private noncomputable def leaf6605Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217979/134217728) }, vSqrt := { lower := (65529/65536), upper := (11452743679/11451932672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (378160347/268435456) }, upper := { exponent := 1, mantissa := (737/512) } }, logOuter := sk126LogOuterCertificate, logK := sk126LogKCertificate, logChi := chi336LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (22904676351/22903865344) } }, logDArg := sk126LogDArgCertificate }

private noncomputable def leaf6605InnerLog : WideLogData :=
  innerPair370Data

set_option maxRecDepth 1000000 in
private theorem leaf6605LocalValidity :
    LeafFacts leaf6605Box leaf6605Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6605Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (11452743679/11451932672) }) = true
      norm_num [leaf6605Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6605CertificateValid :
    WideCertificateValid leaf6605Box leaf6605Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk126ValidityFacts chi336ValidityFacts
    leaf6605LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6605CoverageChecked :
    coverageCheck (innerAD leaf6605Box) leaf6605InnerLog = true := by
  rfl'

private theorem leaf6605InnerLogValid :
    leaf6605InnerLog.Valid 8 (innerAD leaf6605Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint470PositiveFacts.valid leaf6605CoverageChecked

private noncomputable def leaf6605InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629675/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6605InputLogOnePlusV_eq :
    leaf6605InputLogOnePlusV = outerEnclosure 24
      (leaf6605Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6605RoundedFacts : LeafRoundedFacts 8
    leaf6605Certificate.logOnePlusV leaf6605InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6605InputLogOnePlusV_eq }

private noncomputable def leaf6605Inputs : Inputs :=
  inputsOfCaches globalInput sk126RoundedInputs
    chi336InputQChi innerPair370Input
    leaf6605InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6605LowerChecked :
    lowerCheck 24 leaf6605Box leaf6605Inputs = true := by
  rfl'

private theorem leaf6605CoversExact : CoversExact 8
    leaf6605Box leaf6605Certificate leaf6605InnerLog leaf6605Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk126RoundedFacts chi336RoundedFacts
    innerPair370RoundedFacts leaf6605RoundedFacts (by rfl)

private theorem leaf6605FlatSound : Sound leaf6605Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6605CertificateValid
    leaf6605InnerLogValid leaf6605CoversExact leaf6605LowerChecked

private noncomputable def leaf6606Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (37/64), chiHi := (75/128) }

private noncomputable def leaf6606Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217979/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34355821568) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (376653111/268435456) }, upper := { exponent := 1, mantissa := (5873/4096) } }, logOuter := sk125LogOuterCertificate, logK := sk125LogKCertificate, logChi := chi337LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68714052605/68711643136) } }, logDArg := sk125LogDArgCertificate }

private noncomputable def leaf6606InnerLog : WideLogData :=
  innerPair357Data

set_option maxRecDepth 1000000 in
private theorem leaf6606LocalValidity :
    LeafFacts leaf6606Box leaf6606Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6606Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34355821568) }) = true
      norm_num [leaf6606Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6606CertificateValid :
    WideCertificateValid leaf6606Box leaf6606Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk125ValidityFacts chi337ValidityFacts
    leaf6606LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6606CoverageChecked :
    coverageCheck (innerAD leaf6606Box) leaf6606InnerLog = true := by
  rfl'

private theorem leaf6606InnerLogValid :
    leaf6606InnerLog.Valid 8 (innerAD leaf6606Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint97PositiveFacts.valid leaf6606CoverageChecked

private noncomputable def leaf6606InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629669/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6606InputLogOnePlusV_eq :
    leaf6606InputLogOnePlusV = outerEnclosure 24
      (leaf6606Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6606RoundedFacts : LeafRoundedFacts 8
    leaf6606Certificate.logOnePlusV leaf6606InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6606InputLogOnePlusV_eq }

private noncomputable def leaf6606Inputs : Inputs :=
  inputsOfCaches globalInput sk125RoundedInputs
    chi337InputQChi innerPair357Input
    leaf6606InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6606LowerChecked :
    lowerCheck 24 leaf6606Box leaf6606Inputs = true := by
  rfl'

private theorem leaf6606CoversExact : CoversExact 8
    leaf6606Box leaf6606Certificate leaf6606InnerLog leaf6606Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk125RoundedFacts chi337RoundedFacts
    innerPair357RoundedFacts leaf6606RoundedFacts (by rfl)

private theorem leaf6606FlatSound : Sound leaf6606Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6606CertificateValid
    leaf6606InnerLogValid leaf6606CoversExact leaf6606LowerChecked

private noncomputable def leaf6607Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (75/128), chiHi := (19/32) }

private noncomputable def leaf6607Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217981/134217728) }, vSqrt := { lower := (65529/65536), upper := (2642940849/2642751488) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (379929709/268435456) }, upper := { exponent := 1, mantissa := (1481/1024) } }, logOuter := sk125LogOuterCertificate, logK := sk125LogKCertificate, logChi := chi338LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (5285692337/5285502976) } }, logDArg := sk125LogDArgCertificate }

private noncomputable def leaf6607InnerLog : WideLogData :=
  innerPair368Data

set_option maxRecDepth 1000000 in
private theorem leaf6607LocalValidity :
    LeafFacts leaf6607Box leaf6607Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6607Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (2642940849/2642751488) }) = true
      norm_num [leaf6607Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6607CertificateValid :
    WideCertificateValid leaf6607Box leaf6607Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk125ValidityFacts chi338ValidityFacts
    leaf6607LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6607CoverageChecked :
    coverageCheck (innerAD leaf6607Box) leaf6607InnerLog = true := by
  rfl'

private theorem leaf6607InnerLogValid :
    leaf6607InnerLog.Valid 8 (innerAD leaf6607Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint98PositiveFacts.valid leaf6607CoverageChecked

private noncomputable def leaf6607InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814841/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6607InputLogOnePlusV_eq :
    leaf6607InputLogOnePlusV = outerEnclosure 24
      (leaf6607Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6607RoundedFacts : LeafRoundedFacts 8
    leaf6607Certificate.logOnePlusV leaf6607InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6607InputLogOnePlusV_eq }

private noncomputable def leaf6607Inputs : Inputs :=
  inputsOfCaches globalInput sk125RoundedInputs
    chi338InputQChi innerPair368Input
    leaf6607InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6607LowerChecked :
    lowerCheck 24 leaf6607Box leaf6607Inputs = true := by
  rfl'

private theorem leaf6607CoversExact : CoversExact 8
    leaf6607Box leaf6607Certificate leaf6607InnerLog leaf6607Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk125RoundedFacts chi338RoundedFacts
    innerPair368RoundedFacts leaf6607RoundedFacts (by rfl)

private theorem leaf6607FlatSound : Sound leaf6607Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6607CertificateValid
    leaf6607InnerLogValid leaf6607CoversExact leaf6607LowerChecked

private noncomputable def leaf6608Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (37/64), chiHi := (75/128) }

private noncomputable def leaf6608Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217981/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34355744768) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (381502477/268435456) }, upper := { exponent := 1, mantissa := (1487/1024) } }, logOuter := sk126LogOuterCertificate, logK := sk126LogKCertificate, logChi := chi337LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68713975805/68711489536) } }, logDArg := sk126LogDArgCertificate }

private noncomputable def leaf6608InnerLog : WideLogData :=
  innerPair368Data

set_option maxRecDepth 1000000 in
private theorem leaf6608LocalValidity :
    LeafFacts leaf6608Box leaf6608Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6608Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34355744768) }) = true
      norm_num [leaf6608Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6608CertificateValid :
    WideCertificateValid leaf6608Box leaf6608Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk126ValidityFacts chi337ValidityFacts
    leaf6608LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6608CoverageChecked :
    coverageCheck (innerAD leaf6608Box) leaf6608InnerLog = true := by
  rfl'

private theorem leaf6608InnerLogValid :
    leaf6608InnerLog.Valid 8 (innerAD leaf6608Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint98PositiveFacts.valid leaf6608CoverageChecked

private noncomputable def leaf6608InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453711/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf6608InputLogOnePlusV_eq :
    leaf6608InputLogOnePlusV = outerEnclosure 24
      (leaf6608Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6608RoundedFacts : LeafRoundedFacts 8
    leaf6608Certificate.logOnePlusV leaf6608InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6608InputLogOnePlusV_eq }

private noncomputable def leaf6608Inputs : Inputs :=
  inputsOfCaches globalInput sk126RoundedInputs
    chi337InputQChi innerPair368Input
    leaf6608InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6608LowerChecked :
    lowerCheck 24 leaf6608Box leaf6608Inputs = true := by
  rfl'

private theorem leaf6608CoversExact : CoversExact 8
    leaf6608Box leaf6608Certificate leaf6608InnerLog leaf6608Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk126RoundedFacts chi337RoundedFacts
    innerPair368RoundedFacts leaf6608RoundedFacts (by rfl)

private theorem leaf6608FlatSound : Sound leaf6608Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6608CertificateValid
    leaf6608InnerLogValid leaf6608CoversExact leaf6608LowerChecked

private noncomputable def leaf6609Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (75/128), chiHi := (19/32) }

private noncomputable def leaf6609Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217983/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34355691520) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (384844607/268435456) }, upper := { exponent := 1, mantissa := (375/256) } }, logOuter := sk126LogOuterCertificate, logK := sk126LogKCertificate, logChi := chi338LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68713922557/68711383040) } }, logDArg := sk126LogDArgCertificate }

private noncomputable def leaf6609InnerLog : WideLogData :=
  innerPair368Data

set_option maxRecDepth 1000000 in
private theorem leaf6609LocalValidity :
    LeafFacts leaf6609Box leaf6609Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6609Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34355691520) }) = true
      norm_num [leaf6609Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6609CertificateValid :
    WideCertificateValid leaf6609Box leaf6609Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk126ValidityFacts chi338ValidityFacts
    leaf6609LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6609CoverageChecked :
    coverageCheck (innerAD leaf6609Box) leaf6609InnerLog = true := by
  rfl'

private theorem leaf6609InnerLogValid :
    leaf6609InnerLog.Valid 8 (innerAD leaf6609Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint98PositiveFacts.valid leaf6609CoverageChecked

private noncomputable def leaf6609InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629701/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6609InputLogOnePlusV_eq :
    leaf6609InputLogOnePlusV = outerEnclosure 24
      (leaf6609Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6609RoundedFacts : LeafRoundedFacts 8
    leaf6609Certificate.logOnePlusV leaf6609InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6609InputLogOnePlusV_eq }

private noncomputable def leaf6609Inputs : Inputs :=
  inputsOfCaches globalInput sk126RoundedInputs
    chi338InputQChi innerPair368Input
    leaf6609InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6609LowerChecked :
    lowerCheck 24 leaf6609Box leaf6609Inputs = true := by
  rfl'

private theorem leaf6609CoversExact : CoversExact 8
    leaf6609Box leaf6609Certificate leaf6609InnerLog leaf6609Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk126RoundedFacts chi338RoundedFacts
    innerPair368RoundedFacts leaf6609RoundedFacts (by rfl)

private theorem leaf6609FlatSound : Sound leaf6609Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6609CertificateValid
    leaf6609InnerLogValid leaf6609CoversExact leaf6609LowerChecked

private noncomputable def leaf6610Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (19/32), chiHi := (77/128) }

private noncomputable def leaf6610Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217983/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34355717120) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (383206307/268435456) }, upper := { exponent := 1, mantissa := (5975/4096) } }, logOuter := sk125LogOuterCertificate, logK := sk125LogKCertificate, logChi := chi339LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68713948157/68711434240) } }, logDArg := sk125LogDArgCertificate }

private noncomputable def leaf6610InnerLog : WideLogData :=
  innerPair368Data

set_option maxRecDepth 1000000 in
private theorem leaf6610LocalValidity :
    LeafFacts leaf6610Box leaf6610Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6610Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34355717120) }) = true
      norm_num [leaf6610Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6610CertificateValid :
    WideCertificateValid leaf6610Box leaf6610Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk125ValidityFacts chi339ValidityFacts
    leaf6610LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6610CoverageChecked :
    coverageCheck (innerAD leaf6610Box) leaf6610InnerLog = true := by
  rfl'

private theorem leaf6610InnerLogValid :
    leaf6610InnerLog.Valid 8 (innerAD leaf6610Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint98PositiveFacts.valid leaf6610CoverageChecked

private noncomputable def leaf6610InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629695/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6610InputLogOnePlusV_eq :
    leaf6610InputLogOnePlusV = outerEnclosure 24
      (leaf6610Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6610RoundedFacts : LeafRoundedFacts 8
    leaf6610Certificate.logOnePlusV leaf6610InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6610InputLogOnePlusV_eq }

private noncomputable def leaf6610Inputs : Inputs :=
  inputsOfCaches globalInput sk125RoundedInputs
    chi339InputQChi innerPair368Input
    leaf6610InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6610LowerChecked :
    lowerCheck 24 leaf6610Box leaf6610Inputs = true := by
  rfl'

private theorem leaf6610CoversExact : CoversExact 8
    leaf6610Box leaf6610Certificate leaf6610InnerLog leaf6610Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk125RoundedFacts chi339RoundedFacts
    innerPair368RoundedFacts leaf6610RoundedFacts (by rfl)

private theorem leaf6610FlatSound : Sound leaf6610Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6610CertificateValid
    leaf6610InnerLogValid leaf6610CoversExact leaf6610LowerChecked

private noncomputable def leaf6611Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (77/128), chiHi := (39/64) }

private noncomputable def leaf6611Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217985/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34355664896) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (386482905/268435456) }, upper := { exponent := 1, mantissa := (3013/2048) } }, logOuter := sk125LogOuterCertificate, logK := sk125LogKCertificate, logChi := chi340LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68713895933/68711329792) } }, logDArg := sk125LogDArgCertificate }

private noncomputable def leaf6611InnerLog : WideLogData :=
  innerPair372Data

set_option maxRecDepth 1000000 in
private theorem leaf6611LocalValidity :
    LeafFacts leaf6611Box leaf6611Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6611Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34355664896) }) = true
      norm_num [leaf6611Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6611CertificateValid :
    WideCertificateValid leaf6611Box leaf6611Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk125ValidityFacts chi340ValidityFacts
    leaf6611LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6611CoverageChecked :
    coverageCheck (innerAD leaf6611Box) leaf6611InnerLog = true := by
  rfl'

private theorem leaf6611InnerLogValid :
    leaf6611InnerLog.Valid 8 (innerAD leaf6611Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint99PositiveFacts.valid leaf6611CoverageChecked

private noncomputable def leaf6611InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629707/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6611InputLogOnePlusV_eq :
    leaf6611InputLogOnePlusV = outerEnclosure 24
      (leaf6611Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6611RoundedFacts : LeafRoundedFacts 8
    leaf6611Certificate.logOnePlusV leaf6611InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6611InputLogOnePlusV_eq }

private noncomputable def leaf6611Inputs : Inputs :=
  inputsOfCaches globalInput sk125RoundedInputs
    chi340InputQChi innerPair372Input
    leaf6611InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6611LowerChecked :
    lowerCheck 24 leaf6611Box leaf6611Inputs = true := by
  rfl'

private theorem leaf6611CoversExact : CoversExact 8
    leaf6611Box leaf6611Certificate leaf6611InnerLog leaf6611Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk125RoundedFacts chi340RoundedFacts
    innerPair372RoundedFacts leaf6611RoundedFacts (by rfl)

private theorem leaf6611FlatSound : Sound leaf6611Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6611CertificateValid
    leaf6611InnerLogValid leaf6611CoversExact leaf6611LowerChecked

private noncomputable def leaf6612Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (19/32), chiHi := (77/128) }

private noncomputable def leaf6612Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217985/134217728) }, vSqrt := { lower := (65529/65536), upper := (11452743679/11451879424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (388186737/268435456) }, upper := { exponent := 1, mantissa := (1513/1024) } }, logOuter := sk126LogOuterCertificate, logK := sk126LogKCertificate, logChi := chi339LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (22904623103/22903758848) } }, logDArg := sk126LogDArgCertificate }

private noncomputable def leaf6612InnerLog : WideLogData :=
  innerPair372Data

set_option maxRecDepth 1000000 in
private theorem leaf6612LocalValidity :
    LeafFacts leaf6612Box leaf6612Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6612Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (11452743679/11451879424) }) = true
      norm_num [leaf6612Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6612CertificateValid :
    WideCertificateValid leaf6612Box leaf6612Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk126ValidityFacts chi339ValidityFacts
    leaf6612LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6612CoverageChecked :
    coverageCheck (innerAD leaf6612Box) leaf6612InnerLog = true := by
  rfl'

private theorem leaf6612InnerLogValid :
    leaf6612InnerLog.Valid 8 (innerAD leaf6612Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint99PositiveFacts.valid leaf6612CoverageChecked

private noncomputable def leaf6612InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814857/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6612InputLogOnePlusV_eq :
    leaf6612InputLogOnePlusV = outerEnclosure 24
      (leaf6612Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6612RoundedFacts : LeafRoundedFacts 8
    leaf6612Certificate.logOnePlusV leaf6612InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6612InputLogOnePlusV_eq }

private noncomputable def leaf6612Inputs : Inputs :=
  inputsOfCaches globalInput sk126RoundedInputs
    chi339InputQChi innerPair372Input
    leaf6612InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6612LowerChecked :
    lowerCheck 24 leaf6612Box leaf6612Inputs = true := by
  rfl'

private theorem leaf6612CoversExact : CoversExact 8
    leaf6612Box leaf6612Certificate leaf6612InnerLog leaf6612Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk126RoundedFacts chi339RoundedFacts
    innerPair372RoundedFacts leaf6612RoundedFacts (by rfl)

private theorem leaf6612FlatSound : Sound leaf6612Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6612CertificateValid
    leaf6612InnerLogValid leaf6612CoversExact leaf6612LowerChecked

private noncomputable def leaf6613Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (77/128), chiHi := (39/64) }

private noncomputable def leaf6613Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217987/134217728) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588896256) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (391528867/268435456) }, upper := { exponent := 1, mantissa := (763/512) } }, logOuter := sk126LogOuterCertificate, logK := sk126LogKCertificate, logChi := chi340LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178322943/17177792512) } }, logDArg := sk126LogDArgCertificate }

private noncomputable def leaf6613InnerLog : WideLogData :=
  innerPair372Data

set_option maxRecDepth 1000000 in
private theorem leaf6613LocalValidity :
    LeafFacts leaf6613Box leaf6613Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6613Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588896256) }) = true
      norm_num [leaf6613Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6613CertificateValid :
    WideCertificateValid leaf6613Box leaf6613Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk126ValidityFacts chi340ValidityFacts
    leaf6613LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6613CoverageChecked :
    coverageCheck (innerAD leaf6613Box) leaf6613InnerLog = true := by
  rfl'

private theorem leaf6613InnerLogValid :
    leaf6613InnerLog.Valid 8 (innerAD leaf6613Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint99PositiveFacts.valid leaf6613CoverageChecked

private noncomputable def leaf6613InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629599/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6613InputLogOnePlusV_eq :
    leaf6613InputLogOnePlusV = outerEnclosure 24
      (leaf6613Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6613RoundedFacts : LeafRoundedFacts 8
    leaf6613Certificate.logOnePlusV leaf6613InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6613InputLogOnePlusV_eq }

private noncomputable def leaf6613Inputs : Inputs :=
  inputsOfCaches globalInput sk126RoundedInputs
    chi340InputQChi innerPair372Input
    leaf6613InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6613LowerChecked :
    lowerCheck 24 leaf6613Box leaf6613Inputs = true := by
  rfl'

private theorem leaf6613CoversExact : CoversExact 8
    leaf6613Box leaf6613Certificate leaf6613InnerLog leaf6613Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk126RoundedFacts chi340RoundedFacts
    innerPair372RoundedFacts leaf6613RoundedFacts (by rfl)

private theorem leaf6613FlatSound : Sound leaf6613Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6613CertificateValid
    leaf6613InnerLogValid leaf6613CoversExact leaf6613LowerChecked

private noncomputable def leaf6614Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (39/64), chiHi := (79/128) }

private noncomputable def leaf6614Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217987/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34355612672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (389759503/268435456) }, upper := { exponent := 1, mantissa := (6077/4096) } }, logOuter := sk125LogOuterCertificate, logK := sk125LogKCertificate, logChi := chi347LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68713843709/68711225344) } }, logDArg := sk125LogDArgCertificate }

private noncomputable def leaf6614InnerLog : WideLogData :=
  innerPair372Data

set_option maxRecDepth 1000000 in
private theorem leaf6614LocalValidity :
    LeafFacts leaf6614Box leaf6614Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6614Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34355612672) }) = true
      norm_num [leaf6614Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6614CertificateValid :
    WideCertificateValid leaf6614Box leaf6614Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk125ValidityFacts chi347ValidityFacts
    leaf6614LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6614CoverageChecked :
    coverageCheck (innerAD leaf6614Box) leaf6614InnerLog = true := by
  rfl'

private theorem leaf6614InnerLogValid :
    leaf6614InnerLog.Valid 8 (innerAD leaf6614Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint99PositiveFacts.valid leaf6614CoverageChecked

private noncomputable def leaf6614InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453715/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf6614InputLogOnePlusV_eq :
    leaf6614InputLogOnePlusV = outerEnclosure 24
      (leaf6614Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6614RoundedFacts : LeafRoundedFacts 8
    leaf6614Certificate.logOnePlusV leaf6614InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6614InputLogOnePlusV_eq }

private noncomputable def leaf6614Inputs : Inputs :=
  inputsOfCaches globalInput sk125RoundedInputs
    chi347InputQChi innerPair372Input
    leaf6614InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6614LowerChecked :
    lowerCheck 24 leaf6614Box leaf6614Inputs = true := by
  rfl'

private theorem leaf6614CoversExact : CoversExact 8
    leaf6614Box leaf6614Certificate leaf6614InnerLog leaf6614Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk125RoundedFacts chi347RoundedFacts
    innerPair372RoundedFacts leaf6614RoundedFacts (by rfl)

private theorem leaf6614FlatSound : Sound leaf6614Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6614CertificateValid
    leaf6614InnerLogValid leaf6614CoversExact leaf6614LowerChecked

private noncomputable def leaf6615Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (79/128), chiHi := (5/8) }

private noncomputable def leaf6615Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217989/134217728) }, vSqrt := { lower := (65529/65536), upper := (67633281/67629056) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (393036101/268435456) }, upper := { exponent := 1, mantissa := (383/256) } }, logOuter := sk125LogOuterCertificate, logK := sk125LogKCertificate, logChi := chi348LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (135262337/135258112) } }, logDArg := sk125LogDArgCertificate }

private noncomputable def leaf6615InnerLog : WideLogData :=
  innerPair372Data

set_option maxRecDepth 1000000 in
private theorem leaf6615LocalValidity :
    LeafFacts leaf6615Box leaf6615Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6615Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67633281/67629056) }) = true
      norm_num [leaf6615Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6615CertificateValid :
    WideCertificateValid leaf6615Box leaf6615Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk125ValidityFacts chi348ValidityFacts
    leaf6615LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6615CoverageChecked :
    coverageCheck (innerAD leaf6615Box) leaf6615InnerLog = true := by
  rfl'

private theorem leaf6615InnerLogValid :
    leaf6615InnerLog.Valid 8 (innerAD leaf6615Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint99PositiveFacts.valid leaf6615CoverageChecked

private noncomputable def leaf6615InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629605/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6615InputLogOnePlusV_eq :
    leaf6615InputLogOnePlusV = outerEnclosure 24
      (leaf6615Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6615RoundedFacts : LeafRoundedFacts 8
    leaf6615Certificate.logOnePlusV leaf6615InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6615InputLogOnePlusV_eq }

private noncomputable def leaf6615Inputs : Inputs :=
  inputsOfCaches globalInput sk125RoundedInputs
    chi348InputQChi innerPair372Input
    leaf6615InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6615LowerChecked :
    lowerCheck 24 leaf6615Box leaf6615Inputs = true := by
  rfl'

private theorem leaf6615CoversExact : CoversExact 8
    leaf6615Box leaf6615Certificate leaf6615InnerLog leaf6615Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk125RoundedFacts chi348RoundedFacts
    innerPair372RoundedFacts leaf6615RoundedFacts (by rfl)

private theorem leaf6615FlatSound : Sound leaf6615Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6615CertificateValid
    leaf6615InnerLogValid leaf6615CoversExact leaf6615LowerChecked

private noncomputable def leaf6616Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (39/64), chiHi := (79/128) }

private noncomputable def leaf6616Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134217989/134217728) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588882944) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (394870997/268435456) }, upper := { exponent := 1, mantissa := (1539/1024) } }, logOuter := sk126LogOuterCertificate, logK := sk126LogKCertificate, logChi := chi347LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178309631/17177765888) } }, logDArg := sk126LogDArgCertificate }

private noncomputable def leaf6616InnerLog : WideLogData :=
  innerPair376Data

set_option maxRecDepth 1000000 in
private theorem leaf6616LocalValidity :
    LeafFacts leaf6616Box leaf6616Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6616Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588882944) }) = true
      norm_num [leaf6616Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6616CertificateValid :
    WideCertificateValid leaf6616Box leaf6616Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk126ValidityFacts chi347ValidityFacts
    leaf6616LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6616CoverageChecked :
    coverageCheck (innerAD leaf6616Box) leaf6616InnerLog = true := by
  rfl'

private theorem leaf6616InnerLogValid :
    leaf6616InnerLog.Valid 8 (innerAD leaf6616Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint482PositiveFacts.valid leaf6616CoverageChecked

private noncomputable def leaf6616InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907403/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6616InputLogOnePlusV_eq :
    leaf6616InputLogOnePlusV = outerEnclosure 24
      (leaf6616Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6616RoundedFacts : LeafRoundedFacts 8
    leaf6616Certificate.logOnePlusV leaf6616InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6616InputLogOnePlusV_eq }

private noncomputable def leaf6616Inputs : Inputs :=
  inputsOfCaches globalInput sk126RoundedInputs
    chi347InputQChi innerPair376Input
    leaf6616InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6616LowerChecked :
    lowerCheck 24 leaf6616Box leaf6616Inputs = true := by
  rfl'

private theorem leaf6616CoversExact : CoversExact 8
    leaf6616Box leaf6616Certificate leaf6616InnerLog leaf6616Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk126RoundedFacts chi347RoundedFacts
    innerPair376RoundedFacts leaf6616RoundedFacts (by rfl)

private theorem leaf6616FlatSound : Sound leaf6616Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6616CertificateValid
    leaf6616InnerLogValid leaf6616CoversExact leaf6616LowerChecked

private noncomputable def leaf6617Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (79/128), chiHi := (5/8) }

private noncomputable def leaf6617Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134217991/134217728) }, vSqrt := { lower := (65529/65536), upper := (954380743/954318848) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (398213127/268435456) }, upper := { exponent := 1, mantissa := (97/64) } }, logOuter := sk126LogOuterCertificate, logK := sk126LogKCertificate, logChi := chi348LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (1908699591/1908637696) } }, logDArg := sk126LogDArgCertificate }

private noncomputable def leaf6617InnerLog : WideLogData :=
  innerPair376Data

set_option maxRecDepth 1000000 in
private theorem leaf6617LocalValidity :
    LeafFacts leaf6617Box leaf6617Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6617Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (954380743/954318848) }) = true
      norm_num [leaf6617Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6617CertificateValid :
    WideCertificateValid leaf6617Box leaf6617Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk126ValidityFacts chi348ValidityFacts
    leaf6617LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6617CoverageChecked :
    coverageCheck (innerAD leaf6617Box) leaf6617InnerLog = true := by
  rfl'

private theorem leaf6617InnerLogValid :
    leaf6617InnerLog.Valid 8 (innerAD leaf6617Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint482PositiveFacts.valid leaf6617CoverageChecked

private noncomputable def leaf6617InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629625/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6617InputLogOnePlusV_eq :
    leaf6617InputLogOnePlusV = outerEnclosure 24
      (leaf6617Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6617RoundedFacts : LeafRoundedFacts 8
    leaf6617Certificate.logOnePlusV leaf6617InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6617InputLogOnePlusV_eq }

private noncomputable def leaf6617Inputs : Inputs :=
  inputsOfCaches globalInput sk126RoundedInputs
    chi348InputQChi innerPair376Input
    leaf6617InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6617LowerChecked :
    lowerCheck 24 leaf6617Box leaf6617Inputs = true := by
  rfl'

private theorem leaf6617CoversExact : CoversExact 8
    leaf6617Box leaf6617Certificate leaf6617InnerLog leaf6617Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk126RoundedFacts chi348RoundedFacts
    innerPair376RoundedFacts leaf6617RoundedFacts (by rfl)

private theorem leaf6617FlatSound : Sound leaf6617Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6617CertificateValid
    leaf6617InnerLogValid leaf6617CoversExact leaf6617LowerChecked

private noncomputable def component133Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (9/16), chiHi := (37/64) }

set_option maxRecDepth 1000000 in
private theorem component133Node0_sound : Sound component133Node0Box :=
  sound_of_literal_split component133Node0Box leaf6587Box leaf6588Box
    .chi (73/128) (by rfl) (by rfl)
    leaf6587FlatSound leaf6588FlatSound

private noncomputable def component133Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (37/64), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component133Node1_sound : Sound component133Node1Box :=
  sound_of_literal_split component133Node1Box leaf6589Box leaf6590Box
    .chi (75/128) (by rfl) (by rfl)
    leaf6589FlatSound leaf6590FlatSound

private noncomputable def component133Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (9/16), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component133Node2_sound : Sound component133Node2Box :=
  sound_of_literal_split component133Node2Box component133Node0Box component133Node1Box
    .chi (37/64) (by rfl) (by rfl)
    component133Node0_sound component133Node1_sound

private noncomputable def component133Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (9/16), chiHi := (37/64) }

set_option maxRecDepth 1000000 in
private theorem component133Node3_sound : Sound component133Node3Box :=
  sound_of_literal_split component133Node3Box leaf6591Box leaf6592Box
    .chi (73/128) (by rfl) (by rfl)
    leaf6591FlatSound leaf6592FlatSound

private noncomputable def component133Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (37/64), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component133Node4_sound : Sound component133Node4Box :=
  sound_of_literal_split component133Node4Box leaf6593Box leaf6594Box
    .chi (75/128) (by rfl) (by rfl)
    leaf6593FlatSound leaf6594FlatSound

private noncomputable def component133Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (9/16), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component133Node5_sound : Sound component133Node5Box :=
  sound_of_literal_split component133Node5Box component133Node3Box component133Node4Box
    .chi (37/64) (by rfl) (by rfl)
    component133Node3_sound component133Node4_sound

private noncomputable def component133Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (9/16), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component133Node6_sound : Sound component133Node6Box :=
  sound_of_literal_split component133Node6Box component133Node2Box component133Node5Box
    .k (49/16) (by rfl) (by rfl)
    component133Node2_sound component133Node5_sound

private noncomputable def component133Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (19/32), chiHi := (39/64) }

set_option maxRecDepth 1000000 in
private theorem component133Node7_sound : Sound component133Node7Box :=
  sound_of_literal_split component133Node7Box leaf6595Box leaf6596Box
    .chi (77/128) (by rfl) (by rfl)
    leaf6595FlatSound leaf6596FlatSound

private noncomputable def component133Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (19/32), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component133Node8_sound : Sound component133Node8Box :=
  sound_of_literal_split component133Node8Box component133Node7Box leaf6597Box
    .chi (39/64) (by rfl) (by rfl)
    component133Node7_sound leaf6597FlatSound

private noncomputable def component133Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (19/32), chiHi := (39/64) }

set_option maxRecDepth 1000000 in
private theorem component133Node9_sound : Sound component133Node9Box :=
  sound_of_literal_split component133Node9Box leaf6598Box leaf6599Box
    .chi (77/128) (by rfl) (by rfl)
    leaf6598FlatSound leaf6599FlatSound

private noncomputable def component133Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (39/64), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component133Node10_sound : Sound component133Node10Box :=
  sound_of_literal_split component133Node10Box leaf6600Box leaf6601Box
    .chi (79/128) (by rfl) (by rfl)
    leaf6600FlatSound leaf6601FlatSound

private noncomputable def component133Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (19/32), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component133Node11_sound : Sound component133Node11Box :=
  sound_of_literal_split component133Node11Box component133Node9Box component133Node10Box
    .chi (39/64) (by rfl) (by rfl)
    component133Node9_sound component133Node10_sound

private noncomputable def component133Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (19/32), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component133Node12_sound : Sound component133Node12Box :=
  sound_of_literal_split component133Node12Box component133Node8Box component133Node11Box
    .k (49/16) (by rfl) (by rfl)
    component133Node8_sound component133Node11_sound

private noncomputable def component133Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (9/16), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component133Node13_sound : Sound component133Node13Box :=
  sound_of_literal_split component133Node13Box component133Node6Box component133Node12Box
    .chi (19/32) (by rfl) (by rfl)
    component133Node6_sound component133Node12_sound

private noncomputable def component133Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (9/16), chiHi := (37/64) }

set_option maxRecDepth 1000000 in
private theorem component133Node14_sound : Sound component133Node14Box :=
  sound_of_literal_split component133Node14Box leaf6602Box leaf6603Box
    .chi (73/128) (by rfl) (by rfl)
    leaf6602FlatSound leaf6603FlatSound

private noncomputable def component133Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (9/16), chiHi := (37/64) }

set_option maxRecDepth 1000000 in
private theorem component133Node15_sound : Sound component133Node15Box :=
  sound_of_literal_split component133Node15Box leaf6604Box leaf6605Box
    .chi (73/128) (by rfl) (by rfl)
    leaf6604FlatSound leaf6605FlatSound

private noncomputable def component133Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (9/16), chiHi := (37/64) }

set_option maxRecDepth 1000000 in
private theorem component133Node16_sound : Sound component133Node16Box :=
  sound_of_literal_split component133Node16Box component133Node14Box component133Node15Box
    .k (51/16) (by rfl) (by rfl)
    component133Node14_sound component133Node15_sound

private noncomputable def component133Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (37/64), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component133Node17_sound : Sound component133Node17Box :=
  sound_of_literal_split component133Node17Box leaf6606Box leaf6607Box
    .chi (75/128) (by rfl) (by rfl)
    leaf6606FlatSound leaf6607FlatSound

private noncomputable def component133Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (37/64), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component133Node18_sound : Sound component133Node18Box :=
  sound_of_literal_split component133Node18Box leaf6608Box leaf6609Box
    .chi (75/128) (by rfl) (by rfl)
    leaf6608FlatSound leaf6609FlatSound

private noncomputable def component133Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (37/64), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component133Node19_sound : Sound component133Node19Box :=
  sound_of_literal_split component133Node19Box component133Node17Box component133Node18Box
    .k (51/16) (by rfl) (by rfl)
    component133Node17_sound component133Node18_sound

private noncomputable def component133Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (9/16), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component133Node20_sound : Sound component133Node20Box :=
  sound_of_literal_split component133Node20Box component133Node16Box component133Node19Box
    .chi (37/64) (by rfl) (by rfl)
    component133Node16_sound component133Node19_sound

private noncomputable def component133Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (19/32), chiHi := (39/64) }

set_option maxRecDepth 1000000 in
private theorem component133Node21_sound : Sound component133Node21Box :=
  sound_of_literal_split component133Node21Box leaf6610Box leaf6611Box
    .chi (77/128) (by rfl) (by rfl)
    leaf6610FlatSound leaf6611FlatSound

private noncomputable def component133Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (19/32), chiHi := (39/64) }

set_option maxRecDepth 1000000 in
private theorem component133Node22_sound : Sound component133Node22Box :=
  sound_of_literal_split component133Node22Box leaf6612Box leaf6613Box
    .chi (77/128) (by rfl) (by rfl)
    leaf6612FlatSound leaf6613FlatSound

private noncomputable def component133Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (19/32), chiHi := (39/64) }

set_option maxRecDepth 1000000 in
private theorem component133Node23_sound : Sound component133Node23Box :=
  sound_of_literal_split component133Node23Box component133Node21Box component133Node22Box
    .k (51/16) (by rfl) (by rfl)
    component133Node21_sound component133Node22_sound

private noncomputable def component133Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (39/64), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component133Node24_sound : Sound component133Node24Box :=
  sound_of_literal_split component133Node24Box leaf6614Box leaf6615Box
    .chi (79/128) (by rfl) (by rfl)
    leaf6614FlatSound leaf6615FlatSound

private noncomputable def component133Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (39/64), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component133Node25_sound : Sound component133Node25Box :=
  sound_of_literal_split component133Node25Box leaf6616Box leaf6617Box
    .chi (79/128) (by rfl) (by rfl)
    leaf6616FlatSound leaf6617FlatSound

private noncomputable def component133Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (39/64), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component133Node26_sound : Sound component133Node26Box :=
  sound_of_literal_split component133Node26Box component133Node24Box component133Node25Box
    .k (51/16) (by rfl) (by rfl)
    component133Node24_sound component133Node25_sound

private noncomputable def component133Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (19/32), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component133Node27_sound : Sound component133Node27Box :=
  sound_of_literal_split component133Node27Box component133Node23Box component133Node26Box
    .chi (39/64) (by rfl) (by rfl)
    component133Node23_sound component133Node26_sound

private noncomputable def component133Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (9/16), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component133Node28_sound : Sound component133Node28Box :=
  sound_of_literal_split component133Node28Box component133Node20Box component133Node27Box
    .chi (19/32) (by rfl) (by rfl)
    component133Node20_sound component133Node27_sound

noncomputable def component133Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (13/4), chiLo := (9/16), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
theorem component133_sound : Sound component133Box :=
  sound_of_literal_split component133Box component133Node13Box component133Node28Box
    .k (25/8) (by rfl) (by rfl)
    component133Node13_sound component133Node28_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
