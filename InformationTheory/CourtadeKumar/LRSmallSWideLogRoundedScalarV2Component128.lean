import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch7
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch11
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch4
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

private noncomputable def leaf6356Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (5/8), chiHi := (41/64) }

private noncomputable def leaf6356Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109027/67108864) }, vSqrt := { lower := (32765/32768), upper := (11452743679/11452098560) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (171927135/134217728) }, upper := { exponent := 1, mantissa := (2705/2048) } }, logOuter := sk89LogOuterCertificate, logK := sk89LogKCertificate, logChi := chi323LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (22904842239/22904197120) } }, logDArg := sk89LogDArgCertificate }

private noncomputable def leaf6356InnerLog : WideLogData :=
  innerPair295Data

set_option maxRecDepth 1000000 in
private theorem leaf6356LocalValidity :
    LeafFacts leaf6356Box leaf6356Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6356Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (11452743679/11452098560) }) = true
      norm_num [leaf6356Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6356CertificateValid :
    WideCertificateValid leaf6356Box leaf6356Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk89ValidityFacts chi323ValidityFacts
    leaf6356LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6356CoverageChecked :
    coverageCheck (innerAD leaf6356Box) leaf6356InnerLog = true := by
  rfl'

private theorem leaf6356InnerLogValid :
    leaf6356InnerLog.Valid 8 (innerAD leaf6356Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint92PositiveFacts.valid leaf6356CoverageChecked

private noncomputable def leaf6356InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629553/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6356InputLogOnePlusV_eq :
    leaf6356InputLogOnePlusV = outerEnclosure 24
      (leaf6356Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6356RoundedFacts : LeafRoundedFacts 8
    leaf6356Certificate.logOnePlusV leaf6356InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6356InputLogOnePlusV_eq }

private noncomputable def leaf6356Inputs : Inputs :=
  inputsOfCaches globalInput sk89RoundedInputs
    chi323InputQChi innerPair295Input
    leaf6356InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6356LowerChecked :
    lowerCheck 24 leaf6356Box leaf6356Inputs = true := by
  rfl'

private theorem leaf6356CoversExact : CoversExact 8
    leaf6356Box leaf6356Certificate leaf6356InnerLog leaf6356Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk89RoundedFacts chi323RoundedFacts
    innerPair295RoundedFacts leaf6356RoundedFacts (by rfl)

private theorem leaf6356FlatSound : Sound leaf6356Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6356CertificateValid
    leaf6356InnerLogValid leaf6356CoversExact leaf6356LowerChecked

private noncomputable def leaf6357Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (41/64), chiHi := (21/32) }

private noncomputable def leaf6357Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109029/67108864) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34356211712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (174548413/134217728) }, upper := { exponent := 1, mantissa := (1373/1024) } }, logOuter := sk89LogOuterCertificate, logK := sk89LogKCertificate, logChi := chi324LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714442749/68712423424) } }, logDArg := sk89LogDArgCertificate }

private noncomputable def leaf6357InnerLog : WideLogData :=
  innerPair340Data

set_option maxRecDepth 1000000 in
private theorem leaf6357LocalValidity :
    LeafFacts leaf6357Box leaf6357Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6357Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34356211712) }) = true
      norm_num [leaf6357Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6357CertificateValid :
    WideCertificateValid leaf6357Box leaf6357Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk89ValidityFacts chi324ValidityFacts
    leaf6357LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6357CoverageChecked :
    coverageCheck (innerAD leaf6357Box) leaf6357InnerLog = true := by
  rfl'

private theorem leaf6357InnerLogValid :
    leaf6357InnerLog.Valid 8 (innerAD leaf6357Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint92PositiveFacts.valid leaf6357CoverageChecked

private noncomputable def leaf6357InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814787/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6357InputLogOnePlusV_eq :
    leaf6357InputLogOnePlusV = outerEnclosure 24
      (leaf6357Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6357RoundedFacts : LeafRoundedFacts 8
    leaf6357Certificate.logOnePlusV leaf6357InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6357InputLogOnePlusV_eq }

private noncomputable def leaf6357Inputs : Inputs :=
  inputsOfCaches globalInput sk89RoundedInputs
    chi324InputQChi innerPair340Input
    leaf6357InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6357LowerChecked :
    lowerCheck 24 leaf6357Box leaf6357Inputs = true := by
  rfl'

private theorem leaf6357CoversExact : CoversExact 8
    leaf6357Box leaf6357Certificate leaf6357InnerLog leaf6357Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk89RoundedFacts chi324RoundedFacts
    innerPair340RoundedFacts leaf6357RoundedFacts (by rfl)

private theorem leaf6357FlatSound : Sound leaf6357Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6357CertificateValid
    leaf6357InnerLogValid leaf6357CoversExact leaf6357LowerChecked

private noncomputable def leaf6358Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (5/8), chiHi := (41/64) }

private noncomputable def leaf6358Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109029/67108864) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34356211712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (174548413/134217728) }, upper := { exponent := 1, mantissa := (1373/1024) } }, logOuter := sk90LogOuterCertificate, logK := sk90LogKCertificate, logChi := chi323LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714442749/68712423424) } }, logDArg := sk90LogDArgCertificate }

private noncomputable def leaf6358InnerLog : WideLogData :=
  innerPair340Data

set_option maxRecDepth 1000000 in
private theorem leaf6358LocalValidity :
    LeafFacts leaf6358Box leaf6358Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6358Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34356211712) }) = true
      norm_num [leaf6358Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6358CertificateValid :
    WideCertificateValid leaf6358Box leaf6358Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk90ValidityFacts chi323ValidityFacts
    leaf6358LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6358CoverageChecked :
    coverageCheck (innerAD leaf6358Box) leaf6358InnerLog = true := by
  rfl'

private theorem leaf6358InnerLogValid :
    leaf6358InnerLog.Valid 8 (innerAD leaf6358Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint92PositiveFacts.valid leaf6358CoverageChecked

private noncomputable def leaf6358InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814787/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6358InputLogOnePlusV_eq :
    leaf6358InputLogOnePlusV = outerEnclosure 24
      (leaf6358Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6358RoundedFacts : LeafRoundedFacts 8
    leaf6358Certificate.logOnePlusV leaf6358InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6358InputLogOnePlusV_eq }

private noncomputable def leaf6358Inputs : Inputs :=
  inputsOfCaches globalInput sk90RoundedInputs
    chi323InputQChi innerPair340Input
    leaf6358InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6358LowerChecked :
    lowerCheck 24 leaf6358Box leaf6358Inputs = true := by
  rfl'

private theorem leaf6358CoversExact : CoversExact 8
    leaf6358Box leaf6358Certificate leaf6358InnerLog leaf6358Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk90RoundedFacts chi323RoundedFacts
    innerPair340RoundedFacts leaf6358RoundedFacts (by rfl)

private theorem leaf6358FlatSound : Sound leaf6358Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6358CertificateValid
    leaf6358InnerLogValid leaf6358CoversExact leaf6358LowerChecked

private noncomputable def leaf6359Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (41/64), chiHi := (21/32) }

private noncomputable def leaf6359Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109031/67108864) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34356125696) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (177235223/134217728) }, upper := { exponent := 1, mantissa := (697/512) } }, logOuter := sk90LogOuterCertificate, logK := sk90LogKCertificate, logChi := chi324LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714356733/68712251392) } }, logDArg := sk90LogDArgCertificate }

private noncomputable def leaf6359InnerLog : WideLogData :=
  innerPair346Data

set_option maxRecDepth 1000000 in
private theorem leaf6359LocalValidity :
    LeafFacts leaf6359Box leaf6359Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6359Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34356125696) }) = true
      norm_num [leaf6359Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6359CertificateValid :
    WideCertificateValid leaf6359Box leaf6359Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk90ValidityFacts chi324ValidityFacts
    leaf6359LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6359CoverageChecked :
    coverageCheck (innerAD leaf6359Box) leaf6359InnerLog = true := by
  rfl'

private theorem leaf6359InnerLogValid :
    leaf6359InnerLog.Valid 8 (innerAD leaf6359Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint93PositiveFacts.valid leaf6359CoverageChecked

private noncomputable def leaf6359InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629595/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6359InputLogOnePlusV_eq :
    leaf6359InputLogOnePlusV = outerEnclosure 24
      (leaf6359Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6359RoundedFacts : LeafRoundedFacts 8
    leaf6359Certificate.logOnePlusV leaf6359InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6359InputLogOnePlusV_eq }

private noncomputable def leaf6359Inputs : Inputs :=
  inputsOfCaches globalInput sk90RoundedInputs
    chi324InputQChi innerPair346Input
    leaf6359InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6359LowerChecked :
    lowerCheck 24 leaf6359Box leaf6359Inputs = true := by
  rfl'

private theorem leaf6359CoversExact : CoversExact 8
    leaf6359Box leaf6359Certificate leaf6359InnerLog leaf6359Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk90RoundedFacts chi324RoundedFacts
    innerPair346RoundedFacts leaf6359RoundedFacts (by rfl)

private theorem leaf6359FlatSound : Sound leaf6359Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6359CertificateValid
    leaf6359InnerLogValid leaf6359CoversExact leaf6359LowerChecked

private noncomputable def leaf6360Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (21/32), chiHi := (43/64) }

private noncomputable def leaf6360Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109031/67108864) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34356127744) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (177169691/134217728) }, upper := { exponent := 1, mantissa := (2787/2048) } }, logOuter := sk89LogOuterCertificate, logK := sk89LogKCertificate, logChi := chi325LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714358781/68712255488) } }, logDArg := sk89LogDArgCertificate }

private noncomputable def leaf6360InnerLog : WideLogData :=
  innerPair346Data

set_option maxRecDepth 1000000 in
private theorem leaf6360LocalValidity :
    LeafFacts leaf6360Box leaf6360Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6360Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34356127744) }) = true
      norm_num [leaf6360Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6360CertificateValid :
    WideCertificateValid leaf6360Box leaf6360Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk89ValidityFacts chi325ValidityFacts
    leaf6360LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6360CoverageChecked :
    coverageCheck (innerAD leaf6360Box) leaf6360InnerLog = true := by
  rfl'

private theorem leaf6360InnerLogValid :
    leaf6360InnerLog.Valid 8 (innerAD leaf6360Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint93PositiveFacts.valid leaf6360CoverageChecked

private noncomputable def leaf6360InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814797/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6360InputLogOnePlusV_eq :
    leaf6360InputLogOnePlusV = outerEnclosure 24
      (leaf6360Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6360RoundedFacts : LeafRoundedFacts 8
    leaf6360Certificate.logOnePlusV leaf6360InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6360InputLogOnePlusV_eq }

private noncomputable def leaf6360Inputs : Inputs :=
  inputsOfCaches globalInput sk89RoundedInputs
    chi325InputQChi innerPair346Input
    leaf6360InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6360LowerChecked :
    lowerCheck 24 leaf6360Box leaf6360Inputs = true := by
  rfl'

private theorem leaf6360CoversExact : CoversExact 8
    leaf6360Box leaf6360Certificate leaf6360InnerLog leaf6360Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk89RoundedFacts chi325RoundedFacts
    innerPair346RoundedFacts leaf6360RoundedFacts (by rfl)

private theorem leaf6360FlatSound : Sound leaf6360Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6360CertificateValid
    leaf6360InnerLogValid leaf6360CoversExact leaf6360LowerChecked

private noncomputable def leaf6361Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (43/64), chiHi := (11/16) }

private noncomputable def leaf6361Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109033/67108864) }, vSqrt := { lower := (32765/32768), upper := (11452743679/11452014592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (179790969/134217728) }, upper := { exponent := 1, mantissa := (707/512) } }, logOuter := sk89LogOuterCertificate, logK := sk89LogKCertificate, logChi := chi326LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (22904758271/22904029184) } }, logDArg := sk89LogDArgCertificate }

private noncomputable def leaf6361InnerLog : WideLogData :=
  innerPair347Data

set_option maxRecDepth 1000000 in
private theorem leaf6361LocalValidity :
    LeafFacts leaf6361Box leaf6361Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6361Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (11452743679/11452014592) }) = true
      norm_num [leaf6361Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6361CertificateValid :
    WideCertificateValid leaf6361Box leaf6361Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk89ValidityFacts chi326ValidityFacts
    leaf6361LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6361CoverageChecked :
    coverageCheck (innerAD leaf6361Box) leaf6361InnerLog = true := by
  rfl'

private theorem leaf6361InnerLogValid :
    leaf6361InnerLog.Valid 8 (innerAD leaf6361Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint96PositiveFacts.valid leaf6361CoverageChecked

private noncomputable def leaf6361InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629615/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6361InputLogOnePlusV_eq :
    leaf6361InputLogOnePlusV = outerEnclosure 24
      (leaf6361Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6361RoundedFacts : LeafRoundedFacts 8
    leaf6361Certificate.logOnePlusV leaf6361InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6361InputLogOnePlusV_eq }

private noncomputable def leaf6361Inputs : Inputs :=
  inputsOfCaches globalInput sk89RoundedInputs
    chi326InputQChi innerPair347Input
    leaf6361InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6361LowerChecked :
    lowerCheck 24 leaf6361Box leaf6361Inputs = true := by
  rfl'

private theorem leaf6361CoversExact : CoversExact 8
    leaf6361Box leaf6361Certificate leaf6361InnerLog leaf6361Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk89RoundedFacts chi326RoundedFacts
    innerPair347RoundedFacts leaf6361RoundedFacts (by rfl)

private theorem leaf6361FlatSound : Sound leaf6361Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6361CertificateValid
    leaf6361InnerLogValid leaf6361CoversExact leaf6361LowerChecked

private noncomputable def leaf6362Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (21/32), chiHi := (43/64) }

private noncomputable def leaf6362Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109033/67108864) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34356039680) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (179922033/134217728) }, upper := { exponent := 1, mantissa := (1415/1024) } }, logOuter := sk90LogOuterCertificate, logK := sk90LogKCertificate, logChi := chi325LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714270717/68712079360) } }, logDArg := sk90LogDArgCertificate }

private noncomputable def leaf6362InnerLog : WideLogData :=
  innerPair347Data

set_option maxRecDepth 1000000 in
private theorem leaf6362LocalValidity :
    LeafFacts leaf6362Box leaf6362Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6362Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34356039680) }) = true
      norm_num [leaf6362Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6362CertificateValid :
    WideCertificateValid leaf6362Box leaf6362Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk90ValidityFacts chi325ValidityFacts
    leaf6362LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6362CoverageChecked :
    coverageCheck (innerAD leaf6362Box) leaf6362InnerLog = true := by
  rfl'

private theorem leaf6362InnerLogValid :
    leaf6362InnerLog.Valid 8 (innerAD leaf6362Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint96PositiveFacts.valid leaf6362CoverageChecked

private noncomputable def leaf6362InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (726851/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf6362InputLogOnePlusV_eq :
    leaf6362InputLogOnePlusV = outerEnclosure 24
      (leaf6362Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6362RoundedFacts : LeafRoundedFacts 8
    leaf6362Certificate.logOnePlusV leaf6362InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6362InputLogOnePlusV_eq }

private noncomputable def leaf6362Inputs : Inputs :=
  inputsOfCaches globalInput sk90RoundedInputs
    chi325InputQChi innerPair347Input
    leaf6362InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6362LowerChecked :
    lowerCheck 24 leaf6362Box leaf6362Inputs = true := by
  rfl'

private theorem leaf6362CoversExact : CoversExact 8
    leaf6362Box leaf6362Certificate leaf6362InnerLog leaf6362Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk90RoundedFacts chi325RoundedFacts
    innerPair347RoundedFacts leaf6362RoundedFacts (by rfl)

private theorem leaf6362FlatSound : Sound leaf6362Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6362CertificateValid
    leaf6362InnerLogValid leaf6362CoversExact leaf6362LowerChecked

private noncomputable def leaf6363Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (43/64), chiHi := (11/16) }

private noncomputable def leaf6363Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109035/67108864) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34355953664) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (182608843/134217728) }, upper := { exponent := 1, mantissa := (359/256) } }, logOuter := sk90LogOuterCertificate, logK := sk90LogKCertificate, logChi := chi326LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714184701/68711907328) } }, logDArg := sk90LogDArgCertificate }

private noncomputable def leaf6363InnerLog : WideLogData :=
  innerPair353Data

set_option maxRecDepth 1000000 in
private theorem leaf6363LocalValidity :
    LeafFacts leaf6363Box leaf6363Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6363Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34355953664) }) = true
      norm_num [leaf6363Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6363CertificateValid :
    WideCertificateValid leaf6363Box leaf6363Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk90ValidityFacts chi326ValidityFacts
    leaf6363LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6363CoverageChecked :
    coverageCheck (innerAD leaf6363Box) leaf6363InnerLog = true := by
  rfl'

private theorem leaf6363InnerLogValid :
    leaf6363InnerLog.Valid 8 (innerAD leaf6363Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint96PositiveFacts.valid leaf6363CoverageChecked

private noncomputable def leaf6363InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629637/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6363InputLogOnePlusV_eq :
    leaf6363InputLogOnePlusV = outerEnclosure 24
      (leaf6363Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6363RoundedFacts : LeafRoundedFacts 8
    leaf6363Certificate.logOnePlusV leaf6363InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6363InputLogOnePlusV_eq }

private noncomputable def leaf6363Inputs : Inputs :=
  inputsOfCaches globalInput sk90RoundedInputs
    chi326InputQChi innerPair353Input
    leaf6363InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6363LowerChecked :
    lowerCheck 24 leaf6363Box leaf6363Inputs = true := by
  rfl'

private theorem leaf6363CoversExact : CoversExact 8
    leaf6363Box leaf6363Certificate leaf6363InnerLog leaf6363Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk90RoundedFacts chi326RoundedFacts
    innerPair353RoundedFacts leaf6363RoundedFacts (by rfl)

private theorem leaf6363FlatSound : Sound leaf6363Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6363CertificateValid
    leaf6363InnerLogValid leaf6363CoversExact leaf6363LowerChecked

private noncomputable def leaf6364Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (5/8), chiHi := (41/64) }

private noncomputable def leaf6364Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109031/67108864) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34356127744) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (177169691/134217728) }, upper := { exponent := 1, mantissa := (2787/2048) } }, logOuter := sk91LogOuterCertificate, logK := sk91LogKCertificate, logChi := chi323LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714358781/68712255488) } }, logDArg := sk91LogDArgCertificate }

private noncomputable def leaf6364InnerLog : WideLogData :=
  innerPair346Data

set_option maxRecDepth 1000000 in
private theorem leaf6364LocalValidity :
    LeafFacts leaf6364Box leaf6364Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6364Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34356127744) }) = true
      norm_num [leaf6364Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6364CertificateValid :
    WideCertificateValid leaf6364Box leaf6364Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk91ValidityFacts chi323ValidityFacts
    leaf6364LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6364CoverageChecked :
    coverageCheck (innerAD leaf6364Box) leaf6364InnerLog = true := by
  rfl'

private theorem leaf6364InnerLogValid :
    leaf6364InnerLog.Valid 8 (innerAD leaf6364Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint93PositiveFacts.valid leaf6364CoverageChecked

private noncomputable def leaf6364InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814797/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6364InputLogOnePlusV_eq :
    leaf6364InputLogOnePlusV = outerEnclosure 24
      (leaf6364Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6364RoundedFacts : LeafRoundedFacts 8
    leaf6364Certificate.logOnePlusV leaf6364InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6364InputLogOnePlusV_eq }

private noncomputable def leaf6364Inputs : Inputs :=
  inputsOfCaches globalInput sk91RoundedInputs
    chi323InputQChi innerPair346Input
    leaf6364InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6364LowerChecked :
    lowerCheck 24 leaf6364Box leaf6364Inputs = true := by
  rfl'

private theorem leaf6364CoversExact : CoversExact 8
    leaf6364Box leaf6364Certificate leaf6364InnerLog leaf6364Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk91RoundedFacts chi323RoundedFacts
    innerPair346RoundedFacts leaf6364RoundedFacts (by rfl)

private theorem leaf6364FlatSound : Sound leaf6364Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6364CertificateValid
    leaf6364InnerLogValid leaf6364CoversExact leaf6364LowerChecked

private noncomputable def leaf6365Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (41/64), chiHi := (21/32) }

private noncomputable def leaf6365Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109033/67108864) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34356039680) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (179922033/134217728) }, upper := { exponent := 1, mantissa := (1415/1024) } }, logOuter := sk91LogOuterCertificate, logK := sk91LogKCertificate, logChi := chi324LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714270717/68712079360) } }, logDArg := sk91LogDArgCertificate }

private noncomputable def leaf6365InnerLog : WideLogData :=
  innerPair347Data

set_option maxRecDepth 1000000 in
private theorem leaf6365LocalValidity :
    LeafFacts leaf6365Box leaf6365Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6365Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34356039680) }) = true
      norm_num [leaf6365Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6365CertificateValid :
    WideCertificateValid leaf6365Box leaf6365Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk91ValidityFacts chi324ValidityFacts
    leaf6365LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6365CoverageChecked :
    coverageCheck (innerAD leaf6365Box) leaf6365InnerLog = true := by
  rfl'

private theorem leaf6365InnerLogValid :
    leaf6365InnerLog.Valid 8 (innerAD leaf6365Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint96PositiveFacts.valid leaf6365CoverageChecked

private noncomputable def leaf6365InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (726851/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf6365InputLogOnePlusV_eq :
    leaf6365InputLogOnePlusV = outerEnclosure 24
      (leaf6365Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6365RoundedFacts : LeafRoundedFacts 8
    leaf6365Certificate.logOnePlusV leaf6365InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6365InputLogOnePlusV_eq }

private noncomputable def leaf6365Inputs : Inputs :=
  inputsOfCaches globalInput sk91RoundedInputs
    chi324InputQChi innerPair347Input
    leaf6365InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6365LowerChecked :
    lowerCheck 24 leaf6365Box leaf6365Inputs = true := by
  rfl'

private theorem leaf6365CoversExact : CoversExact 8
    leaf6365Box leaf6365Certificate leaf6365InnerLog leaf6365Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk91RoundedFacts chi324RoundedFacts
    innerPair347RoundedFacts leaf6365RoundedFacts (by rfl)

private theorem leaf6365FlatSound : Sound leaf6365Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6365CertificateValid
    leaf6365InnerLogValid leaf6365CoversExact leaf6365LowerChecked

private noncomputable def leaf6366Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (5/8), chiHi := (41/64) }

private noncomputable def leaf6366Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109033/67108864) }, vSqrt := { lower := (32765/32768), upper := (11452743679/11452014592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (179790969/134217728) }, upper := { exponent := 1, mantissa := (707/512) } }, logOuter := sk92LogOuterCertificate, logK := sk92LogKCertificate, logChi := chi323LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (22904758271/22904029184) } }, logDArg := sk92LogDArgCertificate }

private noncomputable def leaf6366InnerLog : WideLogData :=
  innerPair347Data

set_option maxRecDepth 1000000 in
private theorem leaf6366LocalValidity :
    LeafFacts leaf6366Box leaf6366Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6366Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (11452743679/11452014592) }) = true
      norm_num [leaf6366Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6366CertificateValid :
    WideCertificateValid leaf6366Box leaf6366Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk92ValidityFacts chi323ValidityFacts
    leaf6366LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6366CoverageChecked :
    coverageCheck (innerAD leaf6366Box) leaf6366InnerLog = true := by
  rfl'

private theorem leaf6366InnerLogValid :
    leaf6366InnerLog.Valid 8 (innerAD leaf6366Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint96PositiveFacts.valid leaf6366CoverageChecked

private noncomputable def leaf6366InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629615/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6366InputLogOnePlusV_eq :
    leaf6366InputLogOnePlusV = outerEnclosure 24
      (leaf6366Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6366RoundedFacts : LeafRoundedFacts 8
    leaf6366Certificate.logOnePlusV leaf6366InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6366InputLogOnePlusV_eq }

private noncomputable def leaf6366Inputs : Inputs :=
  inputsOfCaches globalInput sk92RoundedInputs
    chi323InputQChi innerPair347Input
    leaf6366InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6366LowerChecked :
    lowerCheck 24 leaf6366Box leaf6366Inputs = true := by
  rfl'

private theorem leaf6366CoversExact : CoversExact 8
    leaf6366Box leaf6366Certificate leaf6366InnerLog leaf6366Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk92RoundedFacts chi323RoundedFacts
    innerPair347RoundedFacts leaf6366RoundedFacts (by rfl)

private theorem leaf6366FlatSound : Sound leaf6366Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6366CertificateValid
    leaf6366InnerLogValid leaf6366CoversExact leaf6366LowerChecked

private noncomputable def leaf6367Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (41/64), chiHi := (21/32) }

private noncomputable def leaf6367Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109035/67108864) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34355953664) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (182608843/134217728) }, upper := { exponent := 1, mantissa := (359/256) } }, logOuter := sk92LogOuterCertificate, logK := sk92LogKCertificate, logChi := chi324LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714184701/68711907328) } }, logDArg := sk92LogDArgCertificate }

private noncomputable def leaf6367InnerLog : WideLogData :=
  innerPair353Data

set_option maxRecDepth 1000000 in
private theorem leaf6367LocalValidity :
    LeafFacts leaf6367Box leaf6367Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6367Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34355953664) }) = true
      norm_num [leaf6367Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6367CertificateValid :
    WideCertificateValid leaf6367Box leaf6367Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk92ValidityFacts chi324ValidityFacts
    leaf6367LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6367CoverageChecked :
    coverageCheck (innerAD leaf6367Box) leaf6367InnerLog = true := by
  rfl'

private theorem leaf6367InnerLogValid :
    leaf6367InnerLog.Valid 8 (innerAD leaf6367Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint96PositiveFacts.valid leaf6367CoverageChecked

private noncomputable def leaf6367InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629637/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6367InputLogOnePlusV_eq :
    leaf6367InputLogOnePlusV = outerEnclosure 24
      (leaf6367Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6367RoundedFacts : LeafRoundedFacts 8
    leaf6367Certificate.logOnePlusV leaf6367InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6367InputLogOnePlusV_eq }

private noncomputable def leaf6367Inputs : Inputs :=
  inputsOfCaches globalInput sk92RoundedInputs
    chi324InputQChi innerPair353Input
    leaf6367InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6367LowerChecked :
    lowerCheck 24 leaf6367Box leaf6367Inputs = true := by
  rfl'

private theorem leaf6367CoversExact : CoversExact 8
    leaf6367Box leaf6367Certificate leaf6367InnerLog leaf6367Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk92RoundedFacts chi324RoundedFacts
    innerPair353RoundedFacts leaf6367RoundedFacts (by rfl)

private theorem leaf6367FlatSound : Sound leaf6367Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6367CertificateValid
    leaf6367InnerLogValid leaf6367CoversExact leaf6367LowerChecked

private noncomputable def leaf6368Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (21/32), chiHi := (43/64) }

private noncomputable def leaf6368Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109035/67108864) }, vSqrt := { lower := (32765/32768), upper := (11452743679/11451983872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (182674375/134217728) }, upper := { exponent := 1, mantissa := (2873/2048) } }, logOuter := sk91LogOuterCertificate, logK := sk91LogKCertificate, logChi := chi325LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (22904727551/22903967744) } }, logDArg := sk91LogDArgCertificate }

private noncomputable def leaf6368InnerLog : WideLogData :=
  innerPair353Data

set_option maxRecDepth 1000000 in
private theorem leaf6368LocalValidity :
    LeafFacts leaf6368Box leaf6368Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6368Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (11452743679/11451983872) }) = true
      norm_num [leaf6368Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6368CertificateValid :
    WideCertificateValid leaf6368Box leaf6368Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk91ValidityFacts chi325ValidityFacts
    leaf6368LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6368CoverageChecked :
    coverageCheck (innerAD leaf6368Box) leaf6368InnerLog = true := by
  rfl'

private theorem leaf6368InnerLogValid :
    leaf6368InnerLog.Valid 8 (innerAD leaf6368Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint96PositiveFacts.valid leaf6368CoverageChecked

private noncomputable def leaf6368InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629637/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6368InputLogOnePlusV_eq :
    leaf6368InputLogOnePlusV = outerEnclosure 24
      (leaf6368Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6368RoundedFacts : LeafRoundedFacts 8
    leaf6368Certificate.logOnePlusV leaf6368InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6368InputLogOnePlusV_eq }

private noncomputable def leaf6368Inputs : Inputs :=
  inputsOfCaches globalInput sk91RoundedInputs
    chi325InputQChi innerPair353Input
    leaf6368InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6368LowerChecked :
    lowerCheck 24 leaf6368Box leaf6368Inputs = true := by
  rfl'

private theorem leaf6368CoversExact : CoversExact 8
    leaf6368Box leaf6368Certificate leaf6368InnerLog leaf6368Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk91RoundedFacts chi325RoundedFacts
    innerPair353RoundedFacts leaf6368RoundedFacts (by rfl)

private theorem leaf6368FlatSound : Sound leaf6368Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6368CertificateValid
    leaf6368InnerLogValid leaf6368CoversExact leaf6368LowerChecked

private noncomputable def leaf6369Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (43/64), chiHi := (11/16) }

private noncomputable def leaf6369Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109037/67108864) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34355863552) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (185426717/134217728) }, upper := { exponent := 1, mantissa := (729/512) } }, logOuter := sk91LogOuterCertificate, logK := sk91LogKCertificate, logChi := chi326LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714094589/68711727104) } }, logDArg := sk91LogDArgCertificate }

private noncomputable def leaf6369InnerLog : WideLogData :=
  innerPair357Data

set_option maxRecDepth 1000000 in
private theorem leaf6369LocalValidity :
    LeafFacts leaf6369Box leaf6369Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6369Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34355863552) }) = true
      norm_num [leaf6369Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6369CertificateValid :
    WideCertificateValid leaf6369Box leaf6369Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk91ValidityFacts chi326ValidityFacts
    leaf6369LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6369CoverageChecked :
    coverageCheck (innerAD leaf6369Box) leaf6369InnerLog = true := by
  rfl'

private theorem leaf6369InnerLogValid :
    leaf6369InnerLog.Valid 8 (innerAD leaf6369Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint97PositiveFacts.valid leaf6369CoverageChecked

private noncomputable def leaf6369InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629659/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6369InputLogOnePlusV_eq :
    leaf6369InputLogOnePlusV = outerEnclosure 24
      (leaf6369Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6369RoundedFacts : LeafRoundedFacts 8
    leaf6369Certificate.logOnePlusV leaf6369InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6369InputLogOnePlusV_eq }

private noncomputable def leaf6369Inputs : Inputs :=
  inputsOfCaches globalInput sk91RoundedInputs
    chi326InputQChi innerPair357Input
    leaf6369InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6369LowerChecked :
    lowerCheck 24 leaf6369Box leaf6369Inputs = true := by
  rfl'

private theorem leaf6369CoversExact : CoversExact 8
    leaf6369Box leaf6369Certificate leaf6369InnerLog leaf6369Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk91RoundedFacts chi326RoundedFacts
    innerPair357RoundedFacts leaf6369RoundedFacts (by rfl)

private theorem leaf6369FlatSound : Sound leaf6369Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6369CertificateValid
    leaf6369InnerLogValid leaf6369CoversExact leaf6369LowerChecked

private noncomputable def leaf6370Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (21/32), chiHi := (43/64) }

private noncomputable def leaf6370Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109037/67108864) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34355863552) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (185426717/134217728) }, upper := { exponent := 1, mantissa := (729/512) } }, logOuter := sk92LogOuterCertificate, logK := sk92LogKCertificate, logChi := chi325LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714094589/68711727104) } }, logDArg := sk92LogDArgCertificate }

private noncomputable def leaf6370InnerLog : WideLogData :=
  innerPair357Data

set_option maxRecDepth 1000000 in
private theorem leaf6370LocalValidity :
    LeafFacts leaf6370Box leaf6370Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6370Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34355863552) }) = true
      norm_num [leaf6370Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6370CertificateValid :
    WideCertificateValid leaf6370Box leaf6370Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk92ValidityFacts chi325ValidityFacts
    leaf6370LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6370CoverageChecked :
    coverageCheck (innerAD leaf6370Box) leaf6370InnerLog = true := by
  rfl'

private theorem leaf6370InnerLogValid :
    leaf6370InnerLog.Valid 8 (innerAD leaf6370Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint97PositiveFacts.valid leaf6370CoverageChecked

private noncomputable def leaf6370InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629659/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6370InputLogOnePlusV_eq :
    leaf6370InputLogOnePlusV = outerEnclosure 24
      (leaf6370Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6370RoundedFacts : LeafRoundedFacts 8
    leaf6370Certificate.logOnePlusV leaf6370InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6370InputLogOnePlusV_eq }

private noncomputable def leaf6370Inputs : Inputs :=
  inputsOfCaches globalInput sk92RoundedInputs
    chi325InputQChi innerPair357Input
    leaf6370InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6370LowerChecked :
    lowerCheck 24 leaf6370Box leaf6370Inputs = true := by
  rfl'

private theorem leaf6370CoversExact : CoversExact 8
    leaf6370Box leaf6370Certificate leaf6370InnerLog leaf6370Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk92RoundedFacts chi325RoundedFacts
    innerPair357RoundedFacts leaf6370RoundedFacts (by rfl)

private theorem leaf6370FlatSound : Sound leaf6370Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6370CertificateValid
    leaf6370InnerLogValid leaf6370CoversExact leaf6370LowerChecked

private noncomputable def leaf6371Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (43/64), chiHi := (11/16) }

private noncomputable def leaf6371Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109039/67108864) }, vSqrt := { lower := (32765/32768), upper := (11452743679/11451924480) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (188244591/134217728) }, upper := { exponent := 1, mantissa := (185/128) } }, logOuter := sk92LogOuterCertificate, logK := sk92LogKCertificate, logChi := chi326LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (22904668159/22903848960) } }, logDArg := sk92LogDArgCertificate }

private noncomputable def leaf6371InnerLog : WideLogData :=
  innerPair358Data

set_option maxRecDepth 1000000 in
private theorem leaf6371LocalValidity :
    LeafFacts leaf6371Box leaf6371Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6371Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (11452743679/11451924480) }) = true
      norm_num [leaf6371Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6371CertificateValid :
    WideCertificateValid leaf6371Box leaf6371Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk92ValidityFacts chi326ValidityFacts
    leaf6371LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6371CoverageChecked :
    coverageCheck (innerAD leaf6371Box) leaf6371InnerLog = true := by
  rfl'

private theorem leaf6371InnerLogValid :
    leaf6371InnerLog.Valid 8 (innerAD leaf6371Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint98PositiveFacts.valid leaf6371CoverageChecked

private noncomputable def leaf6371InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629681/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6371InputLogOnePlusV_eq :
    leaf6371InputLogOnePlusV = outerEnclosure 24
      (leaf6371Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6371RoundedFacts : LeafRoundedFacts 8
    leaf6371Certificate.logOnePlusV leaf6371InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6371InputLogOnePlusV_eq }

private noncomputable def leaf6371Inputs : Inputs :=
  inputsOfCaches globalInput sk92RoundedInputs
    chi326InputQChi innerPair358Input
    leaf6371InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6371LowerChecked :
    lowerCheck 24 leaf6371Box leaf6371Inputs = true := by
  rfl'

private theorem leaf6371CoversExact : CoversExact 8
    leaf6371Box leaf6371Certificate leaf6371InnerLog leaf6371Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk92RoundedFacts chi326RoundedFacts
    innerPair358RoundedFacts leaf6371RoundedFacts (by rfl)

private theorem leaf6371FlatSound : Sound leaf6371Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6371CertificateValid
    leaf6371InnerLogValid leaf6371CoversExact leaf6371LowerChecked

private noncomputable def leaf6372Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (11/16), chiHi := (45/64) }

private noncomputable def leaf6372Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109035/67108864) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34355959808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (182412247/134217728) }, upper := { exponent := 1, mantissa := (2869/2048) } }, logOuter := sk89LogOuterCertificate, logK := sk89LogKCertificate, logChi := chi341LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714190845/68711919616) } }, logDArg := sk89LogDArgCertificate }

private noncomputable def leaf6372InnerLog : WideLogData :=
  innerPair353Data

set_option maxRecDepth 1000000 in
private theorem leaf6372LocalValidity :
    LeafFacts leaf6372Box leaf6372Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6372Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34355959808) }) = true
      norm_num [leaf6372Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6372CertificateValid :
    WideCertificateValid leaf6372Box leaf6372Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk89ValidityFacts chi341ValidityFacts
    leaf6372LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6372CoverageChecked :
    coverageCheck (innerAD leaf6372Box) leaf6372InnerLog = true := by
  rfl'

private theorem leaf6372InnerLogValid :
    leaf6372InnerLog.Valid 8 (innerAD leaf6372Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint96PositiveFacts.valid leaf6372CoverageChecked

private noncomputable def leaf6372InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629635/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6372InputLogOnePlusV_eq :
    leaf6372InputLogOnePlusV = outerEnclosure 24
      (leaf6372Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6372RoundedFacts : LeafRoundedFacts 8
    leaf6372Certificate.logOnePlusV leaf6372InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6372InputLogOnePlusV_eq }

private noncomputable def leaf6372Inputs : Inputs :=
  inputsOfCaches globalInput sk89RoundedInputs
    chi341InputQChi innerPair353Input
    leaf6372InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6372LowerChecked :
    lowerCheck 24 leaf6372Box leaf6372Inputs = true := by
  rfl'

private theorem leaf6372CoversExact : CoversExact 8
    leaf6372Box leaf6372Certificate leaf6372InnerLog leaf6372Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk89RoundedFacts chi341RoundedFacts
    innerPair353RoundedFacts leaf6372RoundedFacts (by rfl)

private theorem leaf6372FlatSound : Sound leaf6372Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6372CertificateValid
    leaf6372InnerLogValid leaf6372CoversExact leaf6372LowerChecked

private noncomputable def leaf6373Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (45/64), chiHi := (23/32) }

private noncomputable def leaf6373Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109037/67108864) }, vSqrt := { lower := (32765/32768), upper := (2642940849/2642759680) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (185033525/134217728) }, upper := { exponent := 1, mantissa := (1455/1024) } }, logOuter := sk89LogOuterCertificate, logK := sk89LogKCertificate, logChi := chi342LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (5285700529/5285519360) } }, logDArg := sk89LogDArgCertificate }

private noncomputable def leaf6373InnerLog : WideLogData :=
  innerPair357Data

set_option maxRecDepth 1000000 in
private theorem leaf6373LocalValidity :
    LeafFacts leaf6373Box leaf6373Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6373Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (2642940849/2642759680) }) = true
      norm_num [leaf6373Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6373CertificateValid :
    WideCertificateValid leaf6373Box leaf6373Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk89ValidityFacts chi342ValidityFacts
    leaf6373LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6373CoverageChecked :
    coverageCheck (innerAD leaf6373Box) leaf6373InnerLog = true := by
  rfl'

private theorem leaf6373InnerLogValid :
    leaf6373InnerLog.Valid 8 (innerAD leaf6373Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint97PositiveFacts.valid leaf6373CoverageChecked

private noncomputable def leaf6373InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453707/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf6373InputLogOnePlusV_eq :
    leaf6373InputLogOnePlusV = outerEnclosure 24
      (leaf6373Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6373RoundedFacts : LeafRoundedFacts 8
    leaf6373Certificate.logOnePlusV leaf6373InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6373InputLogOnePlusV_eq }

private noncomputable def leaf6373Inputs : Inputs :=
  inputsOfCaches globalInput sk89RoundedInputs
    chi342InputQChi innerPair357Input
    leaf6373InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6373LowerChecked :
    lowerCheck 24 leaf6373Box leaf6373Inputs = true := by
  rfl'

private theorem leaf6373CoversExact : CoversExact 8
    leaf6373Box leaf6373Certificate leaf6373InnerLog leaf6373Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk89RoundedFacts chi342RoundedFacts
    innerPair357RoundedFacts leaf6373RoundedFacts (by rfl)

private theorem leaf6373FlatSound : Sound leaf6373Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6373CertificateValid
    leaf6373InnerLogValid leaf6373CoversExact leaf6373LowerChecked

private noncomputable def leaf6374Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (11/16), chiHi := (45/64) }

private noncomputable def leaf6374Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109037/67108864) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34355867648) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (185295653/134217728) }, upper := { exponent := 1, mantissa := (1457/1024) } }, logOuter := sk90LogOuterCertificate, logK := sk90LogKCertificate, logChi := chi341LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714098685/68711735296) } }, logDArg := sk90LogDArgCertificate }

private noncomputable def leaf6374InnerLog : WideLogData :=
  innerPair357Data

set_option maxRecDepth 1000000 in
private theorem leaf6374LocalValidity :
    LeafFacts leaf6374Box leaf6374Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6374Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34355867648) }) = true
      norm_num [leaf6374Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6374CertificateValid :
    WideCertificateValid leaf6374Box leaf6374Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk90ValidityFacts chi341ValidityFacts
    leaf6374LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6374CoverageChecked :
    coverageCheck (innerAD leaf6374Box) leaf6374InnerLog = true := by
  rfl'

private theorem leaf6374InnerLogValid :
    leaf6374InnerLog.Valid 8 (innerAD leaf6374Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint97PositiveFacts.valid leaf6374CoverageChecked

private noncomputable def leaf6374InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814829/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6374InputLogOnePlusV_eq :
    leaf6374InputLogOnePlusV = outerEnclosure 24
      (leaf6374Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6374RoundedFacts : LeafRoundedFacts 8
    leaf6374Certificate.logOnePlusV leaf6374InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6374InputLogOnePlusV_eq }

private noncomputable def leaf6374Inputs : Inputs :=
  inputsOfCaches globalInput sk90RoundedInputs
    chi341InputQChi innerPair357Input
    leaf6374InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6374LowerChecked :
    lowerCheck 24 leaf6374Box leaf6374Inputs = true := by
  rfl'

private theorem leaf6374CoversExact : CoversExact 8
    leaf6374Box leaf6374Certificate leaf6374InnerLog leaf6374Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk90RoundedFacts chi341RoundedFacts
    innerPair357RoundedFacts leaf6374RoundedFacts (by rfl)

private theorem leaf6374FlatSound : Sound leaf6374Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6374CertificateValid
    leaf6374InnerLogValid leaf6374CoversExact leaf6374LowerChecked

private noncomputable def leaf6375Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (45/64), chiHi := (23/32) }

private noncomputable def leaf6375Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109039/67108864) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34355781632) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (187982463/134217728) }, upper := { exponent := 1, mantissa := (739/512) } }, logOuter := sk90LogOuterCertificate, logK := sk90LogKCertificate, logChi := chi342LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714012669/68711563264) } }, logDArg := sk90LogDArgCertificate }

private noncomputable def leaf6375InnerLog : WideLogData :=
  innerPair358Data

set_option maxRecDepth 1000000 in
private theorem leaf6375LocalValidity :
    LeafFacts leaf6375Box leaf6375Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6375Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34355781632) }) = true
      norm_num [leaf6375Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6375CertificateValid :
    WideCertificateValid leaf6375Box leaf6375Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk90ValidityFacts chi342ValidityFacts
    leaf6375LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6375CoverageChecked :
    coverageCheck (innerAD leaf6375Box) leaf6375InnerLog = true := by
  rfl'

private theorem leaf6375InnerLogValid :
    leaf6375InnerLog.Valid 8 (innerAD leaf6375Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint98PositiveFacts.valid leaf6375CoverageChecked

private noncomputable def leaf6375InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629679/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6375InputLogOnePlusV_eq :
    leaf6375InputLogOnePlusV = outerEnclosure 24
      (leaf6375Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6375RoundedFacts : LeafRoundedFacts 8
    leaf6375Certificate.logOnePlusV leaf6375InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6375InputLogOnePlusV_eq }

private noncomputable def leaf6375Inputs : Inputs :=
  inputsOfCaches globalInput sk90RoundedInputs
    chi342InputQChi innerPair358Input
    leaf6375InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6375LowerChecked :
    lowerCheck 24 leaf6375Box leaf6375Inputs = true := by
  rfl'

private theorem leaf6375CoversExact : CoversExact 8
    leaf6375Box leaf6375Certificate leaf6375InnerLog leaf6375Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk90RoundedFacts chi342RoundedFacts
    innerPair358RoundedFacts leaf6375RoundedFacts (by rfl)

private theorem leaf6375FlatSound : Sound leaf6375Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6375CertificateValid
    leaf6375InnerLogValid leaf6375CoversExact leaf6375LowerChecked

private noncomputable def leaf6376Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (23/32), chiHi := (3/4) }

private noncomputable def leaf6376Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554561/33554432) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34355707904) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (93810977/67108864) }, upper := { exponent := 1, mantissa := (187/128) } }, logOuter := sk89LogOuterCertificate, logK := sk89LogKCertificate, logChi := chi81LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68713938941/68711415808) } }, logDArg := sk89LogDArgCertificate }

private noncomputable def leaf6376InnerLog : WideLogData :=
  innerPair358Data

set_option maxRecDepth 1000000 in
private theorem leaf6376LocalValidity :
    LeafFacts leaf6376Box leaf6376Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6376Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34355707904) }) = true
      norm_num [leaf6376Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6376CertificateValid :
    WideCertificateValid leaf6376Box leaf6376Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk89ValidityFacts chi81ValidityFacts
    leaf6376LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6376CoverageChecked :
    coverageCheck (innerAD leaf6376Box) leaf6376InnerLog = true := by
  rfl'

private theorem leaf6376InnerLogValid :
    leaf6376InnerLog.Valid 8 (innerAD leaf6376Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint98PositiveFacts.valid leaf6376CoverageChecked

private noncomputable def leaf6376InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629697/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6376InputLogOnePlusV_eq :
    leaf6376InputLogOnePlusV = outerEnclosure 24
      (leaf6376Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6376RoundedFacts : LeafRoundedFacts 8
    leaf6376Certificate.logOnePlusV leaf6376InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6376InputLogOnePlusV_eq }

private noncomputable def leaf6376Inputs : Inputs :=
  inputsOfCaches globalInput sk89RoundedInputs
    chi81InputQChi innerPair358Input
    leaf6376InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6376LowerChecked :
    lowerCheck 24 leaf6376Box leaf6376Inputs = true := by
  rfl'

private theorem leaf6376CoversExact : CoversExact 8
    leaf6376Box leaf6376Certificate leaf6376InnerLog leaf6376Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk89RoundedFacts chi81RoundedFacts
    innerPair358RoundedFacts leaf6376RoundedFacts (by rfl)

private theorem leaf6376FlatSound : Sound leaf6376Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6376CertificateValid
    leaf6376InnerLogValid leaf6376CoversExact leaf6376LowerChecked

private noncomputable def leaf6377Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (23/32), chiHi := (3/4) }

private noncomputable def leaf6377Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554563/33554432) }, vSqrt := { lower := (32765/32768), upper := (8589426687/8588902400) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (95318211/67108864) }, upper := { exponent := 1, mantissa := (95/64) } }, logOuter := sk90LogOuterCertificate, logK := sk90LogKCertificate, logChi := chi81LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (17178329087/17177804800) } }, logDArg := sk90LogDArgCertificate }

private noncomputable def leaf6377InnerLog : WideLogData :=
  innerPair728Data

set_option maxRecDepth 1000000 in
private theorem leaf6377LocalValidity :
    LeafFacts leaf6377Box leaf6377Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6377Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8589426687/8588902400) }) = true
      norm_num [leaf6377Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6377CertificateValid :
    WideCertificateValid leaf6377Box leaf6377Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk90ValidityFacts chi81ValidityFacts
    leaf6377LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6377CoverageChecked :
    coverageCheck (innerAD leaf6377Box) leaf6377InnerLog = true := by
  rfl'

private theorem leaf6377InnerLogValid :
    leaf6377InnerLog.Valid 8 (innerAD leaf6377Box) :=
  wideLogDataValid_of_cachedCheck endpoint464PositiveFacts
    endpoint481PositiveFacts.valid leaf6377CoverageChecked

private noncomputable def leaf6377InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629593/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6377InputLogOnePlusV_eq :
    leaf6377InputLogOnePlusV = outerEnclosure 24
      (leaf6377Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6377RoundedFacts : LeafRoundedFacts 8
    leaf6377Certificate.logOnePlusV leaf6377InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6377InputLogOnePlusV_eq }

private noncomputable def leaf6377Inputs : Inputs :=
  inputsOfCaches globalInput sk90RoundedInputs
    chi81InputQChi innerPair728Input
    leaf6377InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6377LowerChecked :
    lowerCheck 24 leaf6377Box leaf6377Inputs = true := by
  rfl'

private theorem leaf6377CoversExact : CoversExact 8
    leaf6377Box leaf6377Certificate leaf6377InnerLog leaf6377Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk90RoundedFacts chi81RoundedFacts
    innerPair728RoundedFacts leaf6377RoundedFacts (by rfl)

private theorem leaf6377FlatSound : Sound leaf6377Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6377CertificateValid
    leaf6377InnerLogValid leaf6377CoversExact leaf6377LowerChecked

private noncomputable def leaf6378Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (11/16), chiHi := (45/64) }

private noncomputable def leaf6378Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109039/67108864) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34355775488) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (188179059/134217728) }, upper := { exponent := 1, mantissa := (2959/2048) } }, logOuter := sk91LogOuterCertificate, logK := sk91LogKCertificate, logChi := chi341LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714006525/68711550976) } }, logDArg := sk91LogDArgCertificate }

private noncomputable def leaf6378InnerLog : WideLogData :=
  innerPair358Data

set_option maxRecDepth 1000000 in
private theorem leaf6378LocalValidity :
    LeafFacts leaf6378Box leaf6378Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6378Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34355775488) }) = true
      norm_num [leaf6378Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6378CertificateValid :
    WideCertificateValid leaf6378Box leaf6378Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk91ValidityFacts chi341ValidityFacts
    leaf6378LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6378CoverageChecked :
    coverageCheck (innerAD leaf6378Box) leaf6378InnerLog = true := by
  rfl'

private theorem leaf6378InnerLogValid :
    leaf6378InnerLog.Valid 8 (innerAD leaf6378Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint98PositiveFacts.valid leaf6378CoverageChecked

private noncomputable def leaf6378InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (726855/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf6378InputLogOnePlusV_eq :
    leaf6378InputLogOnePlusV = outerEnclosure 24
      (leaf6378Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6378RoundedFacts : LeafRoundedFacts 8
    leaf6378Certificate.logOnePlusV leaf6378InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6378InputLogOnePlusV_eq }

private noncomputable def leaf6378Inputs : Inputs :=
  inputsOfCaches globalInput sk91RoundedInputs
    chi341InputQChi innerPair358Input
    leaf6378InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6378LowerChecked :
    lowerCheck 24 leaf6378Box leaf6378Inputs = true := by
  rfl'

private theorem leaf6378CoversExact : CoversExact 8
    leaf6378Box leaf6378Certificate leaf6378InnerLog leaf6378Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk91RoundedFacts chi341RoundedFacts
    innerPair358RoundedFacts leaf6378RoundedFacts (by rfl)

private theorem leaf6378FlatSound : Sound leaf6378Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6378CertificateValid
    leaf6378InnerLogValid leaf6378CoversExact leaf6378LowerChecked

private noncomputable def leaf6379Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (45/64), chiHi := (23/32) }

private noncomputable def leaf6379Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109041/67108864) }, vSqrt := { lower := (32765/32768), upper := (11452743679/11451895808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (190931401/134217728) }, upper := { exponent := 1, mantissa := (1501/1024) } }, logOuter := sk91LogOuterCertificate, logK := sk91LogKCertificate, logChi := chi342LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (22904639487/22903791616) } }, logDArg := sk91LogDArgCertificate }

private noncomputable def leaf6379InnerLog : WideLogData :=
  innerPair368Data

set_option maxRecDepth 1000000 in
private theorem leaf6379LocalValidity :
    LeafFacts leaf6379Box leaf6379Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6379Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (11452743679/11451895808) }) = true
      norm_num [leaf6379Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6379CertificateValid :
    WideCertificateValid leaf6379Box leaf6379Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk91ValidityFacts chi342ValidityFacts
    leaf6379LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6379CoverageChecked :
    coverageCheck (innerAD leaf6379Box) leaf6379InnerLog = true := by
  rfl'

private theorem leaf6379InnerLogValid :
    leaf6379InnerLog.Valid 8 (innerAD leaf6379Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint98PositiveFacts.valid leaf6379CoverageChecked

private noncomputable def leaf6379InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814851/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6379InputLogOnePlusV_eq :
    leaf6379InputLogOnePlusV = outerEnclosure 24
      (leaf6379Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6379RoundedFacts : LeafRoundedFacts 8
    leaf6379Certificate.logOnePlusV leaf6379InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6379InputLogOnePlusV_eq }

private noncomputable def leaf6379Inputs : Inputs :=
  inputsOfCaches globalInput sk91RoundedInputs
    chi342InputQChi innerPair368Input
    leaf6379InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6379LowerChecked :
    lowerCheck 24 leaf6379Box leaf6379Inputs = true := by
  rfl'

private theorem leaf6379CoversExact : CoversExact 8
    leaf6379Box leaf6379Certificate leaf6379InnerLog leaf6379Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk91RoundedFacts chi342RoundedFacts
    innerPair368RoundedFacts leaf6379RoundedFacts (by rfl)

private theorem leaf6379FlatSound : Sound leaf6379Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6379CertificateValid
    leaf6379InnerLogValid leaf6379CoversExact leaf6379LowerChecked

private noncomputable def leaf6380Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (11/16), chiHi := (45/64) }

private noncomputable def leaf6380Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109041/67108864) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34355683328) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (191062465/134217728) }, upper := { exponent := 1, mantissa := (751/512) } }, logOuter := sk92LogOuterCertificate, logK := sk92LogKCertificate, logChi := chi341LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68713914365/68711366656) } }, logDArg := sk92LogDArgCertificate }

private noncomputable def leaf6380InnerLog : WideLogData :=
  innerPair368Data

set_option maxRecDepth 1000000 in
private theorem leaf6380LocalValidity :
    LeafFacts leaf6380Box leaf6380Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6380Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34355683328) }) = true
      norm_num [leaf6380Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6380CertificateValid :
    WideCertificateValid leaf6380Box leaf6380Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk92ValidityFacts chi341ValidityFacts
    leaf6380LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6380CoverageChecked :
    coverageCheck (innerAD leaf6380Box) leaf6380InnerLog = true := by
  rfl'

private theorem leaf6380InnerLogValid :
    leaf6380InnerLog.Valid 8 (innerAD leaf6380Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint98PositiveFacts.valid leaf6380CoverageChecked

private noncomputable def leaf6380InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629703/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6380InputLogOnePlusV_eq :
    leaf6380InputLogOnePlusV = outerEnclosure 24
      (leaf6380Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6380RoundedFacts : LeafRoundedFacts 8
    leaf6380Certificate.logOnePlusV leaf6380InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6380InputLogOnePlusV_eq }

private noncomputable def leaf6380Inputs : Inputs :=
  inputsOfCaches globalInput sk92RoundedInputs
    chi341InputQChi innerPair368Input
    leaf6380InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6380LowerChecked :
    lowerCheck 24 leaf6380Box leaf6380Inputs = true := by
  rfl'

private theorem leaf6380CoversExact : CoversExact 8
    leaf6380Box leaf6380Certificate leaf6380InnerLog leaf6380Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk92RoundedFacts chi341RoundedFacts
    innerPair368RoundedFacts leaf6380RoundedFacts (by rfl)

private theorem leaf6380FlatSound : Sound leaf6380Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6380CertificateValid
    leaf6380InnerLogValid leaf6380CoversExact leaf6380LowerChecked

private noncomputable def leaf6381Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (45/64), chiHi := (23/32) }

private noncomputable def leaf6381Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109043/67108864) }, vSqrt := { lower := (32765/32768), upper := (8589426687/8588898304) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (193880339/134217728) }, upper := { exponent := 1, mantissa := (381/256) } }, logOuter := sk92LogOuterCertificate, logK := sk92LogKCertificate, logChi := chi342LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (17178324991/17177796608) } }, logDArg := sk92LogDArgCertificate }

private noncomputable def leaf6381InnerLog : WideLogData :=
  innerPair372Data

set_option maxRecDepth 1000000 in
private theorem leaf6381LocalValidity :
    LeafFacts leaf6381Box leaf6381Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6381Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8589426687/8588898304) }) = true
      norm_num [leaf6381Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6381CertificateValid :
    WideCertificateValid leaf6381Box leaf6381Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk92ValidityFacts chi342ValidityFacts
    leaf6381LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6381CoverageChecked :
    coverageCheck (innerAD leaf6381Box) leaf6381InnerLog = true := by
  rfl'

private theorem leaf6381InnerLogValid :
    leaf6381InnerLog.Valid 8 (innerAD leaf6381Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint99PositiveFacts.valid leaf6381CoverageChecked

private noncomputable def leaf6381InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629597/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6381InputLogOnePlusV_eq :
    leaf6381InputLogOnePlusV = outerEnclosure 24
      (leaf6381Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6381RoundedFacts : LeafRoundedFacts 8
    leaf6381Certificate.logOnePlusV leaf6381InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6381InputLogOnePlusV_eq }

private noncomputable def leaf6381Inputs : Inputs :=
  inputsOfCaches globalInput sk92RoundedInputs
    chi342InputQChi innerPair372Input
    leaf6381InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6381LowerChecked :
    lowerCheck 24 leaf6381Box leaf6381Inputs = true := by
  rfl'

private theorem leaf6381CoversExact : CoversExact 8
    leaf6381Box leaf6381Certificate leaf6381InnerLog leaf6381Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk92RoundedFacts chi342RoundedFacts
    innerPair372RoundedFacts leaf6381RoundedFacts (by rfl)

private theorem leaf6381FlatSound : Sound leaf6381Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6381CertificateValid
    leaf6381InnerLogValid leaf6381CoversExact leaf6381LowerChecked

private noncomputable def leaf6382Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (23/32), chiHi := (47/64) }

private noncomputable def leaf6382Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109043/67108864) }, vSqrt := { lower := (32765/32768), upper := (8589426687/8588899840) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (193683743/134217728) }, upper := { exponent := 1, mantissa := (3045/2048) } }, logOuter := sk91LogOuterCertificate, logK := sk91LogKCertificate, logChi := chi343LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (17178326527/17177799680) } }, logDArg := sk91LogDArgCertificate }

private noncomputable def leaf6382InnerLog : WideLogData :=
  innerPair372Data

set_option maxRecDepth 1000000 in
private theorem leaf6382LocalValidity :
    LeafFacts leaf6382Box leaf6382Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6382Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8589426687/8588899840) }) = true
      norm_num [leaf6382Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6382CertificateValid :
    WideCertificateValid leaf6382Box leaf6382Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk91ValidityFacts chi343ValidityFacts
    leaf6382LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6382CoverageChecked :
    coverageCheck (innerAD leaf6382Box) leaf6382InnerLog = true := by
  rfl'

private theorem leaf6382InnerLogValid :
    leaf6382InnerLog.Valid 8 (innerAD leaf6382Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint99PositiveFacts.valid leaf6382CoverageChecked

private noncomputable def leaf6382InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629595/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6382InputLogOnePlusV_eq :
    leaf6382InputLogOnePlusV = outerEnclosure 24
      (leaf6382Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6382RoundedFacts : LeafRoundedFacts 8
    leaf6382Certificate.logOnePlusV leaf6382InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6382InputLogOnePlusV_eq }

private noncomputable def leaf6382Inputs : Inputs :=
  inputsOfCaches globalInput sk91RoundedInputs
    chi343InputQChi innerPair372Input
    leaf6382InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6382LowerChecked :
    lowerCheck 24 leaf6382Box leaf6382Inputs = true := by
  rfl'

private theorem leaf6382CoversExact : CoversExact 8
    leaf6382Box leaf6382Certificate leaf6382InnerLog leaf6382Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk91RoundedFacts chi343RoundedFacts
    innerPair372RoundedFacts leaf6382RoundedFacts (by rfl)

private theorem leaf6382FlatSound : Sound leaf6382Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6382CertificateValid
    leaf6382InnerLogValid leaf6382CoversExact leaf6382LowerChecked

private noncomputable def leaf6383Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (47/64), chiHi := (3/4) }

private noncomputable def leaf6383Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109045/67108864) }, vSqrt := { lower := (32765/32768), upper := (8589426687/8588877824) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (196436085/134217728) }, upper := { exponent := 1, mantissa := (193/128) } }, logOuter := sk91LogOuterCertificate, logK := sk91LogKCertificate, logChi := chi344LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (17178304511/17177755648) } }, logDArg := sk91LogDArgCertificate }

private noncomputable def leaf6383InnerLog : WideLogData :=
  innerPair374Data

set_option maxRecDepth 1000000 in
private theorem leaf6383LocalValidity :
    LeafFacts leaf6383Box leaf6383Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6383Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8589426687/8588877824) }) = true
      norm_num [leaf6383Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6383CertificateValid :
    WideCertificateValid leaf6383Box leaf6383Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk91ValidityFacts chi344ValidityFacts
    leaf6383LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6383CoverageChecked :
    coverageCheck (innerAD leaf6383Box) leaf6383InnerLog = true := by
  rfl'

private theorem leaf6383InnerLogValid :
    leaf6383InnerLog.Valid 8 (innerAD leaf6383Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint482PositiveFacts.valid leaf6383CoverageChecked

private noncomputable def leaf6383InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629617/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6383InputLogOnePlusV_eq :
    leaf6383InputLogOnePlusV = outerEnclosure 24
      (leaf6383Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6383RoundedFacts : LeafRoundedFacts 8
    leaf6383Certificate.logOnePlusV leaf6383InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6383InputLogOnePlusV_eq }

private noncomputable def leaf6383Inputs : Inputs :=
  inputsOfCaches globalInput sk91RoundedInputs
    chi344InputQChi innerPair374Input
    leaf6383InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6383LowerChecked :
    lowerCheck 24 leaf6383Box leaf6383Inputs = true := by
  rfl'

private theorem leaf6383CoversExact : CoversExact 8
    leaf6383Box leaf6383Certificate leaf6383InnerLog leaf6383Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk91RoundedFacts chi344RoundedFacts
    innerPair374RoundedFacts leaf6383RoundedFacts (by rfl)

private theorem leaf6383FlatSound : Sound leaf6383Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6383CertificateValid
    leaf6383InnerLogValid leaf6383CoversExact leaf6383LowerChecked

private noncomputable def leaf6384Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (23/32), chiHi := (47/64) }

private noncomputable def leaf6384Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109045/67108864) }, vSqrt := { lower := (32765/32768), upper := (2863142229/2862958592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (196698213/134217728) }, upper := { exponent := 1, mantissa := (773/512) } }, logOuter := sk92LogOuterCertificate, logK := sk92LogKCertificate, logChi := chi343LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (5726100821/5725917184) } }, logDArg := sk92LogDArgCertificate }

private noncomputable def leaf6384InnerLog : WideLogData :=
  innerPair374Data

set_option maxRecDepth 1000000 in
private theorem leaf6384LocalValidity :
    LeafFacts leaf6384Box leaf6384Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6384Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (2863142229/2862958592) }) = true
      norm_num [leaf6384Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6384CertificateValid :
    WideCertificateValid leaf6384Box leaf6384Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk92ValidityFacts chi343ValidityFacts
    leaf6384LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6384CoverageChecked :
    coverageCheck (innerAD leaf6384Box) leaf6384InnerLog = true := by
  rfl'

private theorem leaf6384InnerLogValid :
    leaf6384InnerLog.Valid 8 (innerAD leaf6384Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint482PositiveFacts.valid leaf6384CoverageChecked

private noncomputable def leaf6384InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629619/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6384InputLogOnePlusV_eq :
    leaf6384InputLogOnePlusV = outerEnclosure 24
      (leaf6384Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6384RoundedFacts : LeafRoundedFacts 8
    leaf6384Certificate.logOnePlusV leaf6384InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6384InputLogOnePlusV_eq }

private noncomputable def leaf6384Inputs : Inputs :=
  inputsOfCaches globalInput sk92RoundedInputs
    chi343InputQChi innerPair374Input
    leaf6384InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6384LowerChecked :
    lowerCheck 24 leaf6384Box leaf6384Inputs = true := by
  rfl'

private theorem leaf6384CoversExact : CoversExact 8
    leaf6384Box leaf6384Certificate leaf6384InnerLog leaf6384Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk92RoundedFacts chi343RoundedFacts
    innerPair374RoundedFacts leaf6384RoundedFacts (by rfl)

private theorem leaf6384FlatSound : Sound leaf6384Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6384CertificateValid
    leaf6384InnerLogValid leaf6384CoversExact leaf6384LowerChecked

private noncomputable def leaf6385Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (47/64), chiHi := (3/4) }

private noncomputable def leaf6385Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109047/67108864) }, vSqrt := { lower := (32765/32768), upper := (8589426687/8588853248) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (199516087/134217728) }, upper := { exponent := 1, mantissa := (49/32) } }, logOuter := sk92LogOuterCertificate, logK := sk92LogKCertificate, logChi := chi344LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (17178279935/17177706496) } }, logDArg := sk92LogDArgCertificate }

private noncomputable def leaf6385InnerLog : WideLogData :=
  innerPair376Data

set_option maxRecDepth 1000000 in
private theorem leaf6385LocalValidity :
    LeafFacts leaf6385Box leaf6385Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6385Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8589426687/8588853248) }) = true
      norm_num [leaf6385Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6385CertificateValid :
    WideCertificateValid leaf6385Box leaf6385Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk92ValidityFacts chi344ValidityFacts
    leaf6385LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6385CoverageChecked :
    coverageCheck (innerAD leaf6385Box) leaf6385InnerLog = true := by
  rfl'

private theorem leaf6385InnerLogValid :
    leaf6385InnerLog.Valid 8 (innerAD leaf6385Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint482PositiveFacts.valid leaf6385CoverageChecked

private noncomputable def leaf6385InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629641/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6385InputLogOnePlusV_eq :
    leaf6385InputLogOnePlusV = outerEnclosure 24
      (leaf6385Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6385RoundedFacts : LeafRoundedFacts 8
    leaf6385Certificate.logOnePlusV leaf6385InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6385InputLogOnePlusV_eq }

private noncomputable def leaf6385Inputs : Inputs :=
  inputsOfCaches globalInput sk92RoundedInputs
    chi344InputQChi innerPair376Input
    leaf6385InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6385LowerChecked :
    lowerCheck 24 leaf6385Box leaf6385Inputs = true := by
  rfl'

private theorem leaf6385CoversExact : CoversExact 8
    leaf6385Box leaf6385Certificate leaf6385InnerLog leaf6385Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk92RoundedFacts chi344RoundedFacts
    innerPair376RoundedFacts leaf6385RoundedFacts (by rfl)

private theorem leaf6385FlatSound : Sound leaf6385Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6385CertificateValid
    leaf6385InnerLogValid leaf6385CoversExact leaf6385LowerChecked

private noncomputable def leaf6386Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (5/8), chiHi := (41/64) }

private noncomputable def leaf6386Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109035/67108864) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34355959808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (182412247/134217728) }, upper := { exponent := 1, mantissa := (2869/2048) } }, logOuter := sk95LogOuterCertificate, logK := sk95LogKCertificate, logChi := chi323LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714190845/68711919616) } }, logDArg := sk95LogDArgCertificate }

private noncomputable def leaf6386InnerLog : WideLogData :=
  innerPair353Data

set_option maxRecDepth 1000000 in
private theorem leaf6386LocalValidity :
    LeafFacts leaf6386Box leaf6386Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6386Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34355959808) }) = true
      norm_num [leaf6386Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6386CertificateValid :
    WideCertificateValid leaf6386Box leaf6386Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk95ValidityFacts chi323ValidityFacts
    leaf6386LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6386CoverageChecked :
    coverageCheck (innerAD leaf6386Box) leaf6386InnerLog = true := by
  rfl'

private theorem leaf6386InnerLogValid :
    leaf6386InnerLog.Valid 8 (innerAD leaf6386Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint96PositiveFacts.valid leaf6386CoverageChecked

private noncomputable def leaf6386InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629635/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6386InputLogOnePlusV_eq :
    leaf6386InputLogOnePlusV = outerEnclosure 24
      (leaf6386Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6386RoundedFacts : LeafRoundedFacts 8
    leaf6386Certificate.logOnePlusV leaf6386InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6386InputLogOnePlusV_eq }

private noncomputable def leaf6386Inputs : Inputs :=
  inputsOfCaches globalInput sk95RoundedInputs
    chi323InputQChi innerPair353Input
    leaf6386InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6386LowerChecked :
    lowerCheck 24 leaf6386Box leaf6386Inputs = true := by
  rfl'

private theorem leaf6386CoversExact : CoversExact 8
    leaf6386Box leaf6386Certificate leaf6386InnerLog leaf6386Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk95RoundedFacts chi323RoundedFacts
    innerPair353RoundedFacts leaf6386RoundedFacts (by rfl)

private theorem leaf6386FlatSound : Sound leaf6386Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6386CertificateValid
    leaf6386InnerLogValid leaf6386CoversExact leaf6386LowerChecked

private noncomputable def leaf6387Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (41/64), chiHi := (21/32) }

private noncomputable def leaf6387Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109037/67108864) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34355867648) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (185295653/134217728) }, upper := { exponent := 1, mantissa := (1457/1024) } }, logOuter := sk95LogOuterCertificate, logK := sk95LogKCertificate, logChi := chi324LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714098685/68711735296) } }, logDArg := sk95LogDArgCertificate }

private noncomputable def leaf6387InnerLog : WideLogData :=
  innerPair357Data

set_option maxRecDepth 1000000 in
private theorem leaf6387LocalValidity :
    LeafFacts leaf6387Box leaf6387Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6387Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34355867648) }) = true
      norm_num [leaf6387Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6387CertificateValid :
    WideCertificateValid leaf6387Box leaf6387Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk95ValidityFacts chi324ValidityFacts
    leaf6387LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6387CoverageChecked :
    coverageCheck (innerAD leaf6387Box) leaf6387InnerLog = true := by
  rfl'

private theorem leaf6387InnerLogValid :
    leaf6387InnerLog.Valid 8 (innerAD leaf6387Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint97PositiveFacts.valid leaf6387CoverageChecked

private noncomputable def leaf6387InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814829/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6387InputLogOnePlusV_eq :
    leaf6387InputLogOnePlusV = outerEnclosure 24
      (leaf6387Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6387RoundedFacts : LeafRoundedFacts 8
    leaf6387Certificate.logOnePlusV leaf6387InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6387InputLogOnePlusV_eq }

private noncomputable def leaf6387Inputs : Inputs :=
  inputsOfCaches globalInput sk95RoundedInputs
    chi324InputQChi innerPair357Input
    leaf6387InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6387LowerChecked :
    lowerCheck 24 leaf6387Box leaf6387Inputs = true := by
  rfl'

private theorem leaf6387CoversExact : CoversExact 8
    leaf6387Box leaf6387Certificate leaf6387InnerLog leaf6387Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk95RoundedFacts chi324RoundedFacts
    innerPair357RoundedFacts leaf6387RoundedFacts (by rfl)

private theorem leaf6387FlatSound : Sound leaf6387Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6387CertificateValid
    leaf6387InnerLogValid leaf6387CoversExact leaf6387LowerChecked

private noncomputable def leaf6388Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (5/8), chiHi := (41/64) }

private noncomputable def leaf6388Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109037/67108864) }, vSqrt := { lower := (32765/32768), upper := (2642940849/2642759680) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (185033525/134217728) }, upper := { exponent := 1, mantissa := (1455/1024) } }, logOuter := sk96LogOuterCertificate, logK := sk96LogKCertificate, logChi := chi323LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (5285700529/5285519360) } }, logDArg := sk96LogDArgCertificate }

private noncomputable def leaf6388InnerLog : WideLogData :=
  innerPair357Data

set_option maxRecDepth 1000000 in
private theorem leaf6388LocalValidity :
    LeafFacts leaf6388Box leaf6388Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6388Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (2642940849/2642759680) }) = true
      norm_num [leaf6388Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6388CertificateValid :
    WideCertificateValid leaf6388Box leaf6388Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk96ValidityFacts chi323ValidityFacts
    leaf6388LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6388CoverageChecked :
    coverageCheck (innerAD leaf6388Box) leaf6388InnerLog = true := by
  rfl'

private theorem leaf6388InnerLogValid :
    leaf6388InnerLog.Valid 8 (innerAD leaf6388Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint97PositiveFacts.valid leaf6388CoverageChecked

private noncomputable def leaf6388InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453707/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf6388InputLogOnePlusV_eq :
    leaf6388InputLogOnePlusV = outerEnclosure 24
      (leaf6388Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6388RoundedFacts : LeafRoundedFacts 8
    leaf6388Certificate.logOnePlusV leaf6388InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6388InputLogOnePlusV_eq }

private noncomputable def leaf6388Inputs : Inputs :=
  inputsOfCaches globalInput sk96RoundedInputs
    chi323InputQChi innerPair357Input
    leaf6388InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6388LowerChecked :
    lowerCheck 24 leaf6388Box leaf6388Inputs = true := by
  rfl'

private theorem leaf6388CoversExact : CoversExact 8
    leaf6388Box leaf6388Certificate leaf6388InnerLog leaf6388Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk96RoundedFacts chi323RoundedFacts
    innerPair357RoundedFacts leaf6388RoundedFacts (by rfl)

private theorem leaf6388FlatSound : Sound leaf6388Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6388CertificateValid
    leaf6388InnerLogValid leaf6388CoversExact leaf6388LowerChecked

private noncomputable def leaf6389Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (41/64), chiHi := (21/32) }

private noncomputable def leaf6389Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109039/67108864) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34355781632) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (187982463/134217728) }, upper := { exponent := 1, mantissa := (739/512) } }, logOuter := sk96LogOuterCertificate, logK := sk96LogKCertificate, logChi := chi324LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714012669/68711563264) } }, logDArg := sk96LogDArgCertificate }

private noncomputable def leaf6389InnerLog : WideLogData :=
  innerPair358Data

set_option maxRecDepth 1000000 in
private theorem leaf6389LocalValidity :
    LeafFacts leaf6389Box leaf6389Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6389Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34355781632) }) = true
      norm_num [leaf6389Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6389CertificateValid :
    WideCertificateValid leaf6389Box leaf6389Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk96ValidityFacts chi324ValidityFacts
    leaf6389LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6389CoverageChecked :
    coverageCheck (innerAD leaf6389Box) leaf6389InnerLog = true := by
  rfl'

private theorem leaf6389InnerLogValid :
    leaf6389InnerLog.Valid 8 (innerAD leaf6389Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint98PositiveFacts.valid leaf6389CoverageChecked

private noncomputable def leaf6389InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629679/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6389InputLogOnePlusV_eq :
    leaf6389InputLogOnePlusV = outerEnclosure 24
      (leaf6389Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6389RoundedFacts : LeafRoundedFacts 8
    leaf6389Certificate.logOnePlusV leaf6389InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6389InputLogOnePlusV_eq }

private noncomputable def leaf6389Inputs : Inputs :=
  inputsOfCaches globalInput sk96RoundedInputs
    chi324InputQChi innerPair358Input
    leaf6389InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6389LowerChecked :
    lowerCheck 24 leaf6389Box leaf6389Inputs = true := by
  rfl'

private theorem leaf6389CoversExact : CoversExact 8
    leaf6389Box leaf6389Certificate leaf6389InnerLog leaf6389Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk96RoundedFacts chi324RoundedFacts
    innerPair358RoundedFacts leaf6389RoundedFacts (by rfl)

private theorem leaf6389FlatSound : Sound leaf6389Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6389CertificateValid
    leaf6389InnerLogValid leaf6389CoversExact leaf6389LowerChecked

private noncomputable def leaf6390Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (21/32), chiHi := (43/64) }

private noncomputable def leaf6390Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109039/67108864) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34355775488) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (188179059/134217728) }, upper := { exponent := 1, mantissa := (2959/2048) } }, logOuter := sk95LogOuterCertificate, logK := sk95LogKCertificate, logChi := chi325LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714006525/68711550976) } }, logDArg := sk95LogDArgCertificate }

private noncomputable def leaf6390InnerLog : WideLogData :=
  innerPair358Data

set_option maxRecDepth 1000000 in
private theorem leaf6390LocalValidity :
    LeafFacts leaf6390Box leaf6390Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6390Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34355775488) }) = true
      norm_num [leaf6390Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6390CertificateValid :
    WideCertificateValid leaf6390Box leaf6390Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk95ValidityFacts chi325ValidityFacts
    leaf6390LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6390CoverageChecked :
    coverageCheck (innerAD leaf6390Box) leaf6390InnerLog = true := by
  rfl'

private theorem leaf6390InnerLogValid :
    leaf6390InnerLog.Valid 8 (innerAD leaf6390Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint98PositiveFacts.valid leaf6390CoverageChecked

private noncomputable def leaf6390InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (726855/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf6390InputLogOnePlusV_eq :
    leaf6390InputLogOnePlusV = outerEnclosure 24
      (leaf6390Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6390RoundedFacts : LeafRoundedFacts 8
    leaf6390Certificate.logOnePlusV leaf6390InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6390InputLogOnePlusV_eq }

private noncomputable def leaf6390Inputs : Inputs :=
  inputsOfCaches globalInput sk95RoundedInputs
    chi325InputQChi innerPair358Input
    leaf6390InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6390LowerChecked :
    lowerCheck 24 leaf6390Box leaf6390Inputs = true := by
  rfl'

private theorem leaf6390CoversExact : CoversExact 8
    leaf6390Box leaf6390Certificate leaf6390InnerLog leaf6390Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk95RoundedFacts chi325RoundedFacts
    innerPair358RoundedFacts leaf6390RoundedFacts (by rfl)

private theorem leaf6390FlatSound : Sound leaf6390Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6390CertificateValid
    leaf6390InnerLogValid leaf6390CoversExact leaf6390LowerChecked

private noncomputable def leaf6391Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (43/64), chiHi := (11/16) }

private noncomputable def leaf6391Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109041/67108864) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34355683328) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (191062465/134217728) }, upper := { exponent := 1, mantissa := (751/512) } }, logOuter := sk95LogOuterCertificate, logK := sk95LogKCertificate, logChi := chi326LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68713914365/68711366656) } }, logDArg := sk95LogDArgCertificate }

private noncomputable def leaf6391InnerLog : WideLogData :=
  innerPair368Data

set_option maxRecDepth 1000000 in
private theorem leaf6391LocalValidity :
    LeafFacts leaf6391Box leaf6391Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6391Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34355683328) }) = true
      norm_num [leaf6391Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6391CertificateValid :
    WideCertificateValid leaf6391Box leaf6391Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk95ValidityFacts chi326ValidityFacts
    leaf6391LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6391CoverageChecked :
    coverageCheck (innerAD leaf6391Box) leaf6391InnerLog = true := by
  rfl'

private theorem leaf6391InnerLogValid :
    leaf6391InnerLog.Valid 8 (innerAD leaf6391Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint98PositiveFacts.valid leaf6391CoverageChecked

private noncomputable def leaf6391InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629703/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6391InputLogOnePlusV_eq :
    leaf6391InputLogOnePlusV = outerEnclosure 24
      (leaf6391Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6391RoundedFacts : LeafRoundedFacts 8
    leaf6391Certificate.logOnePlusV leaf6391InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6391InputLogOnePlusV_eq }

private noncomputable def leaf6391Inputs : Inputs :=
  inputsOfCaches globalInput sk95RoundedInputs
    chi326InputQChi innerPair368Input
    leaf6391InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6391LowerChecked :
    lowerCheck 24 leaf6391Box leaf6391Inputs = true := by
  rfl'

private theorem leaf6391CoversExact : CoversExact 8
    leaf6391Box leaf6391Certificate leaf6391InnerLog leaf6391Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk95RoundedFacts chi326RoundedFacts
    innerPair368RoundedFacts leaf6391RoundedFacts (by rfl)

private theorem leaf6391FlatSound : Sound leaf6391Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6391CertificateValid
    leaf6391InnerLogValid leaf6391CoversExact leaf6391LowerChecked

private noncomputable def leaf6392Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (21/32), chiHi := (43/64) }

private noncomputable def leaf6392Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109041/67108864) }, vSqrt := { lower := (32765/32768), upper := (11452743679/11451895808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (190931401/134217728) }, upper := { exponent := 1, mantissa := (1501/1024) } }, logOuter := sk96LogOuterCertificate, logK := sk96LogKCertificate, logChi := chi325LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (22904639487/22903791616) } }, logDArg := sk96LogDArgCertificate }

private noncomputable def leaf6392InnerLog : WideLogData :=
  innerPair368Data

set_option maxRecDepth 1000000 in
private theorem leaf6392LocalValidity :
    LeafFacts leaf6392Box leaf6392Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6392Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (11452743679/11451895808) }) = true
      norm_num [leaf6392Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6392CertificateValid :
    WideCertificateValid leaf6392Box leaf6392Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk96ValidityFacts chi325ValidityFacts
    leaf6392LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6392CoverageChecked :
    coverageCheck (innerAD leaf6392Box) leaf6392InnerLog = true := by
  rfl'

private theorem leaf6392InnerLogValid :
    leaf6392InnerLog.Valid 8 (innerAD leaf6392Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint98PositiveFacts.valid leaf6392CoverageChecked

private noncomputable def leaf6392InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814851/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6392InputLogOnePlusV_eq :
    leaf6392InputLogOnePlusV = outerEnclosure 24
      (leaf6392Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6392RoundedFacts : LeafRoundedFacts 8
    leaf6392Certificate.logOnePlusV leaf6392InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6392InputLogOnePlusV_eq }

private noncomputable def leaf6392Inputs : Inputs :=
  inputsOfCaches globalInput sk96RoundedInputs
    chi325InputQChi innerPair368Input
    leaf6392InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6392LowerChecked :
    lowerCheck 24 leaf6392Box leaf6392Inputs = true := by
  rfl'

private theorem leaf6392CoversExact : CoversExact 8
    leaf6392Box leaf6392Certificate leaf6392InnerLog leaf6392Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk96RoundedFacts chi325RoundedFacts
    innerPair368RoundedFacts leaf6392RoundedFacts (by rfl)

private theorem leaf6392FlatSound : Sound leaf6392Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6392CertificateValid
    leaf6392InnerLogValid leaf6392CoversExact leaf6392LowerChecked

private noncomputable def leaf6393Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (43/64), chiHi := (11/16) }

private noncomputable def leaf6393Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109043/67108864) }, vSqrt := { lower := (32765/32768), upper := (8589426687/8588898304) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (193880339/134217728) }, upper := { exponent := 1, mantissa := (381/256) } }, logOuter := sk96LogOuterCertificate, logK := sk96LogKCertificate, logChi := chi326LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (17178324991/17177796608) } }, logDArg := sk96LogDArgCertificate }

private noncomputable def leaf6393InnerLog : WideLogData :=
  innerPair372Data

set_option maxRecDepth 1000000 in
private theorem leaf6393LocalValidity :
    LeafFacts leaf6393Box leaf6393Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6393Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8589426687/8588898304) }) = true
      norm_num [leaf6393Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6393CertificateValid :
    WideCertificateValid leaf6393Box leaf6393Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk96ValidityFacts chi326ValidityFacts
    leaf6393LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6393CoverageChecked :
    coverageCheck (innerAD leaf6393Box) leaf6393InnerLog = true := by
  rfl'

private theorem leaf6393InnerLogValid :
    leaf6393InnerLog.Valid 8 (innerAD leaf6393Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint99PositiveFacts.valid leaf6393CoverageChecked

private noncomputable def leaf6393InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629597/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6393InputLogOnePlusV_eq :
    leaf6393InputLogOnePlusV = outerEnclosure 24
      (leaf6393Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6393RoundedFacts : LeafRoundedFacts 8
    leaf6393Certificate.logOnePlusV leaf6393InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6393InputLogOnePlusV_eq }

private noncomputable def leaf6393Inputs : Inputs :=
  inputsOfCaches globalInput sk96RoundedInputs
    chi326InputQChi innerPair372Input
    leaf6393InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6393LowerChecked :
    lowerCheck 24 leaf6393Box leaf6393Inputs = true := by
  rfl'

private theorem leaf6393CoversExact : CoversExact 8
    leaf6393Box leaf6393Certificate leaf6393InnerLog leaf6393Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk96RoundedFacts chi326RoundedFacts
    innerPair372RoundedFacts leaf6393RoundedFacts (by rfl)

private theorem leaf6393FlatSound : Sound leaf6393Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6393CertificateValid
    leaf6393InnerLogValid leaf6393CoversExact leaf6393LowerChecked

private noncomputable def leaf6394Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (5/8), chiHi := (41/64) }

private noncomputable def leaf6394Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109039/67108864) }, vSqrt := { lower := (32765/32768), upper := (11452743679/11451930624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (187654803/134217728) }, upper := { exponent := 1, mantissa := (2951/2048) } }, logOuter := sk97LogOuterCertificate, logK := sk97LogKCertificate, logChi := chi323LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (22904674303/22903861248) } }, logDArg := sk97LogDArgCertificate }

private noncomputable def leaf6394InnerLog : WideLogData :=
  innerPair725Data

set_option maxRecDepth 1000000 in
private theorem leaf6394LocalValidity :
    LeafFacts leaf6394Box leaf6394Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6394Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (11452743679/11451930624) }) = true
      norm_num [leaf6394Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6394CertificateValid :
    WideCertificateValid leaf6394Box leaf6394Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk97ValidityFacts chi323ValidityFacts
    leaf6394LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6394CoverageChecked :
    coverageCheck (innerAD leaf6394Box) leaf6394InnerLog = true := by
  rfl'

private theorem leaf6394InnerLogValid :
    leaf6394InnerLog.Valid 8 (innerAD leaf6394Box) :=
  wideLogDataValid_of_cachedCheck endpoint463PositiveFacts
    endpoint470PositiveFacts.valid leaf6394CoverageChecked

private noncomputable def leaf6394InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907419/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6394InputLogOnePlusV_eq :
    leaf6394InputLogOnePlusV = outerEnclosure 24
      (leaf6394Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6394RoundedFacts : LeafRoundedFacts 8
    leaf6394Certificate.logOnePlusV leaf6394InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6394InputLogOnePlusV_eq }

private noncomputable def leaf6394Inputs : Inputs :=
  inputsOfCaches globalInput sk97RoundedInputs
    chi323InputQChi innerPair725Input
    leaf6394InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6394LowerChecked :
    lowerCheck 24 leaf6394Box leaf6394Inputs = true := by
  rfl'

private theorem leaf6394CoversExact : CoversExact 8
    leaf6394Box leaf6394Certificate leaf6394InnerLog leaf6394Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk97RoundedFacts chi323RoundedFacts
    innerPair725RoundedFacts leaf6394RoundedFacts (by rfl)

private theorem leaf6394FlatSound : Sound leaf6394Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6394CertificateValid
    leaf6394InnerLogValid leaf6394CoversExact leaf6394LowerChecked

private noncomputable def leaf6395Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (41/64), chiHi := (21/32) }

private noncomputable def leaf6395Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109041/67108864) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34355695616) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (190669273/134217728) }, upper := { exponent := 1, mantissa := (1499/1024) } }, logOuter := sk97LogOuterCertificate, logK := sk97LogKCertificate, logChi := chi324LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68713926653/68711391232) } }, logDArg := sk97LogDArgCertificate }

private noncomputable def leaf6395InnerLog : WideLogData :=
  innerPair368Data

set_option maxRecDepth 1000000 in
private theorem leaf6395LocalValidity :
    LeafFacts leaf6395Box leaf6395Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6395Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34355695616) }) = true
      norm_num [leaf6395Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6395CertificateValid :
    WideCertificateValid leaf6395Box leaf6395Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk97ValidityFacts chi324ValidityFacts
    leaf6395LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6395CoverageChecked :
    coverageCheck (innerAD leaf6395Box) leaf6395InnerLog = true := by
  rfl'

private theorem leaf6395InnerLogValid :
    leaf6395InnerLog.Valid 8 (innerAD leaf6395Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint98PositiveFacts.valid leaf6395CoverageChecked

private noncomputable def leaf6395InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907425/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6395InputLogOnePlusV_eq :
    leaf6395InputLogOnePlusV = outerEnclosure 24
      (leaf6395Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6395RoundedFacts : LeafRoundedFacts 8
    leaf6395Certificate.logOnePlusV leaf6395InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6395InputLogOnePlusV_eq }

private noncomputable def leaf6395Inputs : Inputs :=
  inputsOfCaches globalInput sk97RoundedInputs
    chi324InputQChi innerPair368Input
    leaf6395InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6395LowerChecked :
    lowerCheck 24 leaf6395Box leaf6395Inputs = true := by
  rfl'

private theorem leaf6395CoversExact : CoversExact 8
    leaf6395Box leaf6395Certificate leaf6395InnerLog leaf6395Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk97RoundedFacts chi324RoundedFacts
    innerPair368RoundedFacts leaf6395RoundedFacts (by rfl)

private theorem leaf6395FlatSound : Sound leaf6395Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6395CertificateValid
    leaf6395InnerLogValid leaf6395CoversExact leaf6395LowerChecked

private noncomputable def leaf6396Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (5/8), chiHi := (41/64) }

private noncomputable def leaf6396Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109041/67108864) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34355707904) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (190276081/134217728) }, upper := { exponent := 1, mantissa := (187/128) } }, logOuter := sk98LogOuterCertificate, logK := sk98LogKCertificate, logChi := chi323LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68713938941/68711415808) } }, logDArg := sk98LogDArgCertificate }

private noncomputable def leaf6396InnerLog : WideLogData :=
  innerPair368Data

set_option maxRecDepth 1000000 in
private theorem leaf6396LocalValidity :
    LeafFacts leaf6396Box leaf6396Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6396Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34355707904) }) = true
      norm_num [leaf6396Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6396CertificateValid :
    WideCertificateValid leaf6396Box leaf6396Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk98ValidityFacts chi323ValidityFacts
    leaf6396LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6396CoverageChecked :
    coverageCheck (innerAD leaf6396Box) leaf6396InnerLog = true := by
  rfl'

private theorem leaf6396InnerLogValid :
    leaf6396InnerLog.Valid 8 (innerAD leaf6396Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint98PositiveFacts.valid leaf6396CoverageChecked

private noncomputable def leaf6396InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629697/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6396InputLogOnePlusV_eq :
    leaf6396InputLogOnePlusV = outerEnclosure 24
      (leaf6396Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6396RoundedFacts : LeafRoundedFacts 8
    leaf6396Certificate.logOnePlusV leaf6396InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6396InputLogOnePlusV_eq }

private noncomputable def leaf6396Inputs : Inputs :=
  inputsOfCaches globalInput sk98RoundedInputs
    chi323InputQChi innerPair368Input
    leaf6396InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6396LowerChecked :
    lowerCheck 24 leaf6396Box leaf6396Inputs = true := by
  rfl'

private theorem leaf6396CoversExact : CoversExact 8
    leaf6396Box leaf6396Certificate leaf6396InnerLog leaf6396Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk98RoundedFacts chi323RoundedFacts
    innerPair368RoundedFacts leaf6396RoundedFacts (by rfl)

private theorem leaf6396FlatSound : Sound leaf6396Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6396CertificateValid
    leaf6396InnerLogValid leaf6396CoversExact leaf6396LowerChecked

private noncomputable def leaf6397Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (41/64), chiHi := (21/32) }

private noncomputable def leaf6397Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109043/67108864) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588902400) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (193356083/134217728) }, upper := { exponent := 1, mantissa := (95/64) } }, logOuter := sk98LogOuterCertificate, logK := sk98LogKCertificate, logChi := chi324LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178329087/17177804800) } }, logDArg := sk98LogDArgCertificate }

private noncomputable def leaf6397InnerLog : WideLogData :=
  innerPair372Data

set_option maxRecDepth 1000000 in
private theorem leaf6397LocalValidity :
    LeafFacts leaf6397Box leaf6397Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6397Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588902400) }) = true
      norm_num [leaf6397Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6397CertificateValid :
    WideCertificateValid leaf6397Box leaf6397Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk98ValidityFacts chi324ValidityFacts
    leaf6397LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6397CoverageChecked :
    coverageCheck (innerAD leaf6397Box) leaf6397InnerLog = true := by
  rfl'

private theorem leaf6397InnerLogValid :
    leaf6397InnerLog.Valid 8 (innerAD leaf6397Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint99PositiveFacts.valid leaf6397CoverageChecked

private noncomputable def leaf6397InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629593/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6397InputLogOnePlusV_eq :
    leaf6397InputLogOnePlusV = outerEnclosure 24
      (leaf6397Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6397RoundedFacts : LeafRoundedFacts 8
    leaf6397Certificate.logOnePlusV leaf6397InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6397InputLogOnePlusV_eq }

private noncomputable def leaf6397Inputs : Inputs :=
  inputsOfCaches globalInput sk98RoundedInputs
    chi324InputQChi innerPair372Input
    leaf6397InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6397LowerChecked :
    lowerCheck 24 leaf6397Box leaf6397Inputs = true := by
  rfl'

private theorem leaf6397CoversExact : CoversExact 8
    leaf6397Box leaf6397Certificate leaf6397InnerLog leaf6397Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk98RoundedFacts chi324RoundedFacts
    innerPair372RoundedFacts leaf6397RoundedFacts (by rfl)

private theorem leaf6397FlatSound : Sound leaf6397Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6397CertificateValid
    leaf6397InnerLogValid leaf6397CoversExact leaf6397LowerChecked

private noncomputable def leaf6398Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (21/32), chiHi := (43/64) }

private noncomputable def leaf6398Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109043/67108864) }, vSqrt := { lower := (32765/32768), upper := (8589426687/8588899840) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (193683743/134217728) }, upper := { exponent := 1, mantissa := (3045/2048) } }, logOuter := sk97LogOuterCertificate, logK := sk97LogKCertificate, logChi := chi325LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (17178326527/17177799680) } }, logDArg := sk97LogDArgCertificate }

private noncomputable def leaf6398InnerLog : WideLogData :=
  innerPair372Data

set_option maxRecDepth 1000000 in
private theorem leaf6398LocalValidity :
    LeafFacts leaf6398Box leaf6398Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6398Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8589426687/8588899840) }) = true
      norm_num [leaf6398Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6398CertificateValid :
    WideCertificateValid leaf6398Box leaf6398Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk97ValidityFacts chi325ValidityFacts
    leaf6398LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6398CoverageChecked :
    coverageCheck (innerAD leaf6398Box) leaf6398InnerLog = true := by
  rfl'

private theorem leaf6398InnerLogValid :
    leaf6398InnerLog.Valid 8 (innerAD leaf6398Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint99PositiveFacts.valid leaf6398CoverageChecked

private noncomputable def leaf6398InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629595/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6398InputLogOnePlusV_eq :
    leaf6398InputLogOnePlusV = outerEnclosure 24
      (leaf6398Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6398RoundedFacts : LeafRoundedFacts 8
    leaf6398Certificate.logOnePlusV leaf6398InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6398InputLogOnePlusV_eq }

private noncomputable def leaf6398Inputs : Inputs :=
  inputsOfCaches globalInput sk97RoundedInputs
    chi325InputQChi innerPair372Input
    leaf6398InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6398LowerChecked :
    lowerCheck 24 leaf6398Box leaf6398Inputs = true := by
  rfl'

private theorem leaf6398CoversExact : CoversExact 8
    leaf6398Box leaf6398Certificate leaf6398InnerLog leaf6398Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk97RoundedFacts chi325RoundedFacts
    innerPair372RoundedFacts leaf6398RoundedFacts (by rfl)

private theorem leaf6398FlatSound : Sound leaf6398Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6398CertificateValid
    leaf6398InnerLogValid leaf6398CoversExact leaf6398LowerChecked

private noncomputable def leaf6399Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (43/64), chiHi := (11/16) }

private noncomputable def leaf6399Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109045/67108864) }, vSqrt := { lower := (32765/32768), upper := (2863142229/2862958592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (196698213/134217728) }, upper := { exponent := 1, mantissa := (773/512) } }, logOuter := sk97LogOuterCertificate, logK := sk97LogKCertificate, logChi := chi326LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (5726100821/5725917184) } }, logDArg := sk97LogDArgCertificate }

private noncomputable def leaf6399InnerLog : WideLogData :=
  innerPair374Data

set_option maxRecDepth 1000000 in
private theorem leaf6399LocalValidity :
    LeafFacts leaf6399Box leaf6399Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6399Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (2863142229/2862958592) }) = true
      norm_num [leaf6399Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6399CertificateValid :
    WideCertificateValid leaf6399Box leaf6399Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk97ValidityFacts chi326ValidityFacts
    leaf6399LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6399CoverageChecked :
    coverageCheck (innerAD leaf6399Box) leaf6399InnerLog = true := by
  rfl'

private theorem leaf6399InnerLogValid :
    leaf6399InnerLog.Valid 8 (innerAD leaf6399Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint482PositiveFacts.valid leaf6399CoverageChecked

private noncomputable def leaf6399InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629619/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6399InputLogOnePlusV_eq :
    leaf6399InputLogOnePlusV = outerEnclosure 24
      (leaf6399Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6399RoundedFacts : LeafRoundedFacts 8
    leaf6399Certificate.logOnePlusV leaf6399InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6399InputLogOnePlusV_eq }

private noncomputable def leaf6399Inputs : Inputs :=
  inputsOfCaches globalInput sk97RoundedInputs
    chi326InputQChi innerPair374Input
    leaf6399InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6399LowerChecked :
    lowerCheck 24 leaf6399Box leaf6399Inputs = true := by
  rfl'

private theorem leaf6399CoversExact : CoversExact 8
    leaf6399Box leaf6399Certificate leaf6399InnerLog leaf6399Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk97RoundedFacts chi326RoundedFacts
    innerPair374RoundedFacts leaf6399RoundedFacts (by rfl)

private theorem leaf6399FlatSound : Sound leaf6399Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6399CertificateValid
    leaf6399InnerLogValid leaf6399CoversExact leaf6399LowerChecked

private noncomputable def leaf6400Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (21/32), chiHi := (43/64) }

private noncomputable def leaf6400Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109045/67108864) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588877824) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (196436085/134217728) }, upper := { exponent := 1, mantissa := (193/128) } }, logOuter := sk98LogOuterCertificate, logK := sk98LogKCertificate, logChi := chi325LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178304511/17177755648) } }, logDArg := sk98LogDArgCertificate }

private noncomputable def leaf6400InnerLog : WideLogData :=
  innerPair374Data

set_option maxRecDepth 1000000 in
private theorem leaf6400LocalValidity :
    LeafFacts leaf6400Box leaf6400Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6400Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588877824) }) = true
      norm_num [leaf6400Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6400CertificateValid :
    WideCertificateValid leaf6400Box leaf6400Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk98ValidityFacts chi325ValidityFacts
    leaf6400LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6400CoverageChecked :
    coverageCheck (innerAD leaf6400Box) leaf6400InnerLog = true := by
  rfl'

private theorem leaf6400InnerLogValid :
    leaf6400InnerLog.Valid 8 (innerAD leaf6400Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint482PositiveFacts.valid leaf6400CoverageChecked

private noncomputable def leaf6400InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629617/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6400InputLogOnePlusV_eq :
    leaf6400InputLogOnePlusV = outerEnclosure 24
      (leaf6400Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6400RoundedFacts : LeafRoundedFacts 8
    leaf6400Certificate.logOnePlusV leaf6400InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6400InputLogOnePlusV_eq }

private noncomputable def leaf6400Inputs : Inputs :=
  inputsOfCaches globalInput sk98RoundedInputs
    chi325InputQChi innerPair374Input
    leaf6400InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6400LowerChecked :
    lowerCheck 24 leaf6400Box leaf6400Inputs = true := by
  rfl'

private theorem leaf6400CoversExact : CoversExact 8
    leaf6400Box leaf6400Certificate leaf6400InnerLog leaf6400Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk98RoundedFacts chi325RoundedFacts
    innerPair374RoundedFacts leaf6400RoundedFacts (by rfl)

private theorem leaf6400FlatSound : Sound leaf6400Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6400CertificateValid
    leaf6400InnerLogValid leaf6400CoversExact leaf6400LowerChecked

private noncomputable def leaf6401Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (43/64), chiHi := (11/16) }

private noncomputable def leaf6401Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109047/67108864) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588853248) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (199516087/134217728) }, upper := { exponent := 1, mantissa := (49/32) } }, logOuter := sk98LogOuterCertificate, logK := sk98LogKCertificate, logChi := chi326LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178279935/17177706496) } }, logDArg := sk98LogDArgCertificate }

private noncomputable def leaf6401InnerLog : WideLogData :=
  innerPair376Data

set_option maxRecDepth 1000000 in
private theorem leaf6401LocalValidity :
    LeafFacts leaf6401Box leaf6401Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6401Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588853248) }) = true
      norm_num [leaf6401Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6401CertificateValid :
    WideCertificateValid leaf6401Box leaf6401Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk98ValidityFacts chi326ValidityFacts
    leaf6401LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6401CoverageChecked :
    coverageCheck (innerAD leaf6401Box) leaf6401InnerLog = true := by
  rfl'

private theorem leaf6401InnerLogValid :
    leaf6401InnerLog.Valid 8 (innerAD leaf6401Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint482PositiveFacts.valid leaf6401CoverageChecked

private noncomputable def leaf6401InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629641/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6401InputLogOnePlusV_eq :
    leaf6401InputLogOnePlusV = outerEnclosure 24
      (leaf6401Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6401RoundedFacts : LeafRoundedFacts 8
    leaf6401Certificate.logOnePlusV leaf6401InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6401InputLogOnePlusV_eq }

private noncomputable def leaf6401Inputs : Inputs :=
  inputsOfCaches globalInput sk98RoundedInputs
    chi326InputQChi innerPair376Input
    leaf6401InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6401LowerChecked :
    lowerCheck 24 leaf6401Box leaf6401Inputs = true := by
  rfl'

private theorem leaf6401CoversExact : CoversExact 8
    leaf6401Box leaf6401Certificate leaf6401InnerLog leaf6401Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk98RoundedFacts chi326RoundedFacts
    innerPair376RoundedFacts leaf6401RoundedFacts (by rfl)

private theorem leaf6401FlatSound : Sound leaf6401Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6401CertificateValid
    leaf6401InnerLogValid leaf6401CoversExact leaf6401LowerChecked

private noncomputable def leaf6402Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (11/16), chiHi := (45/64) }

private noncomputable def leaf6402Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109043/67108864) }, vSqrt := { lower := (32765/32768), upper := (8589426687/8588897792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (193945871/134217728) }, upper := { exponent := 1, mantissa := (3049/2048) } }, logOuter := sk95LogOuterCertificate, logK := sk95LogKCertificate, logChi := chi341LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (17178324479/17177795584) } }, logDArg := sk95LogDArgCertificate }

private noncomputable def leaf6402InnerLog : WideLogData :=
  innerPair372Data

set_option maxRecDepth 1000000 in
private theorem leaf6402LocalValidity :
    LeafFacts leaf6402Box leaf6402Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6402Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8589426687/8588897792) }) = true
      norm_num [leaf6402Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6402CertificateValid :
    WideCertificateValid leaf6402Box leaf6402Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk95ValidityFacts chi341ValidityFacts
    leaf6402LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6402CoverageChecked :
    coverageCheck (innerAD leaf6402Box) leaf6402InnerLog = true := by
  rfl'

private theorem leaf6402InnerLogValid :
    leaf6402InnerLog.Valid 8 (innerAD leaf6402Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint99PositiveFacts.valid leaf6402CoverageChecked

private noncomputable def leaf6402InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629597/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6402InputLogOnePlusV_eq :
    leaf6402InputLogOnePlusV = outerEnclosure 24
      (leaf6402Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6402RoundedFacts : LeafRoundedFacts 8
    leaf6402Certificate.logOnePlusV leaf6402InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6402InputLogOnePlusV_eq }

private noncomputable def leaf6402Inputs : Inputs :=
  inputsOfCaches globalInput sk95RoundedInputs
    chi341InputQChi innerPair372Input
    leaf6402InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6402LowerChecked :
    lowerCheck 24 leaf6402Box leaf6402Inputs = true := by
  rfl'

private theorem leaf6402CoversExact : CoversExact 8
    leaf6402Box leaf6402Certificate leaf6402InnerLog leaf6402Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk95RoundedFacts chi341RoundedFacts
    innerPair372RoundedFacts leaf6402RoundedFacts (by rfl)

private theorem leaf6402FlatSound : Sound leaf6402Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6402CertificateValid
    leaf6402InnerLogValid leaf6402CoversExact leaf6402LowerChecked

private noncomputable def leaf6403Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (45/64), chiHi := (23/32) }

private noncomputable def leaf6403Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109045/67108864) }, vSqrt := { lower := (32765/32768), upper := (8589426687/8588874752) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (196829277/134217728) }, upper := { exponent := 1, mantissa := (1547/1024) } }, logOuter := sk95LogOuterCertificate, logK := sk95LogKCertificate, logChi := chi342LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (17178301439/17177749504) } }, logDArg := sk95LogDArgCertificate }

private noncomputable def leaf6403InnerLog : WideLogData :=
  innerPair374Data

set_option maxRecDepth 1000000 in
private theorem leaf6403LocalValidity :
    LeafFacts leaf6403Box leaf6403Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6403Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8589426687/8588874752) }) = true
      norm_num [leaf6403Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6403CertificateValid :
    WideCertificateValid leaf6403Box leaf6403Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk95ValidityFacts chi342ValidityFacts
    leaf6403LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6403CoverageChecked :
    coverageCheck (innerAD leaf6403Box) leaf6403InnerLog = true := by
  rfl'

private theorem leaf6403InnerLogValid :
    leaf6403InnerLog.Valid 8 (innerAD leaf6403Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint482PositiveFacts.valid leaf6403CoverageChecked

private noncomputable def leaf6403InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907405/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6403InputLogOnePlusV_eq :
    leaf6403InputLogOnePlusV = outerEnclosure 24
      (leaf6403Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6403RoundedFacts : LeafRoundedFacts 8
    leaf6403Certificate.logOnePlusV leaf6403InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6403InputLogOnePlusV_eq }

private noncomputable def leaf6403Inputs : Inputs :=
  inputsOfCaches globalInput sk95RoundedInputs
    chi342InputQChi innerPair374Input
    leaf6403InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6403LowerChecked :
    lowerCheck 24 leaf6403Box leaf6403Inputs = true := by
  rfl'

private theorem leaf6403CoversExact : CoversExact 8
    leaf6403Box leaf6403Certificate leaf6403InnerLog leaf6403Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk95RoundedFacts chi342RoundedFacts
    innerPair374RoundedFacts leaf6403RoundedFacts (by rfl)

private theorem leaf6403FlatSound : Sound leaf6403Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6403CertificateValid
    leaf6403InnerLogValid leaf6403CoversExact leaf6403LowerChecked

private noncomputable def leaf6404Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (11/16), chiHi := (45/64) }

private noncomputable def leaf6404Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109045/67108864) }, vSqrt := { lower := (32765/32768), upper := (8589426687/8588874752) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (196829277/134217728) }, upper := { exponent := 1, mantissa := (1547/1024) } }, logOuter := sk96LogOuterCertificate, logK := sk96LogKCertificate, logChi := chi341LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (17178301439/17177749504) } }, logDArg := sk96LogDArgCertificate }

private noncomputable def leaf6404InnerLog : WideLogData :=
  innerPair374Data

set_option maxRecDepth 1000000 in
private theorem leaf6404LocalValidity :
    LeafFacts leaf6404Box leaf6404Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6404Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8589426687/8588874752) }) = true
      norm_num [leaf6404Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6404CertificateValid :
    WideCertificateValid leaf6404Box leaf6404Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk96ValidityFacts chi341ValidityFacts
    leaf6404LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6404CoverageChecked :
    coverageCheck (innerAD leaf6404Box) leaf6404InnerLog = true := by
  rfl'

private theorem leaf6404InnerLogValid :
    leaf6404InnerLog.Valid 8 (innerAD leaf6404Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint482PositiveFacts.valid leaf6404CoverageChecked

private noncomputable def leaf6404InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907405/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6404InputLogOnePlusV_eq :
    leaf6404InputLogOnePlusV = outerEnclosure 24
      (leaf6404Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6404RoundedFacts : LeafRoundedFacts 8
    leaf6404Certificate.logOnePlusV leaf6404InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6404InputLogOnePlusV_eq }

private noncomputable def leaf6404Inputs : Inputs :=
  inputsOfCaches globalInput sk96RoundedInputs
    chi341InputQChi innerPair374Input
    leaf6404InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6404LowerChecked :
    lowerCheck 24 leaf6404Box leaf6404Inputs = true := by
  rfl'

private theorem leaf6404CoversExact : CoversExact 8
    leaf6404Box leaf6404Certificate leaf6404InnerLog leaf6404Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk96RoundedFacts chi341RoundedFacts
    innerPair374RoundedFacts leaf6404RoundedFacts (by rfl)

private theorem leaf6404FlatSound : Sound leaf6404Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6404CertificateValid
    leaf6404InnerLogValid leaf6404CoversExact leaf6404LowerChecked

private noncomputable def leaf6405Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (45/64), chiHi := (23/32) }

private noncomputable def leaf6405Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109047/67108864) }, vSqrt := { lower := (32765/32768), upper := (954380743/954316800) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (199778215/134217728) }, upper := { exponent := 1, mantissa := (785/512) } }, logOuter := sk96LogOuterCertificate, logK := sk96LogKCertificate, logChi := chi342LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (1908697543/1908633600) } }, logDArg := sk96LogDArgCertificate }

private noncomputable def leaf6405InnerLog : WideLogData :=
  innerPair377Data

set_option maxRecDepth 1000000 in
private theorem leaf6405LocalValidity :
    LeafFacts leaf6405Box leaf6405Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6405Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (954380743/954316800) }) = true
      norm_num [leaf6405Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6405CertificateValid :
    WideCertificateValid leaf6405Box leaf6405Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk96ValidityFacts chi342ValidityFacts
    leaf6405LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6405CoverageChecked :
    coverageCheck (innerAD leaf6405Box) leaf6405InnerLog = true := by
  rfl'

private theorem leaf6405InnerLogValid :
    leaf6405InnerLog.Valid 8 (innerAD leaf6405Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint483PositiveFacts.valid leaf6405CoverageChecked

private noncomputable def leaf6405InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629643/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6405InputLogOnePlusV_eq :
    leaf6405InputLogOnePlusV = outerEnclosure 24
      (leaf6405Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6405RoundedFacts : LeafRoundedFacts 8
    leaf6405Certificate.logOnePlusV leaf6405InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6405InputLogOnePlusV_eq }

private noncomputable def leaf6405Inputs : Inputs :=
  inputsOfCaches globalInput sk96RoundedInputs
    chi342InputQChi innerPair377Input
    leaf6405InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6405LowerChecked :
    lowerCheck 24 leaf6405Box leaf6405Inputs = true := by
  rfl'

private theorem leaf6405CoversExact : CoversExact 8
    leaf6405Box leaf6405Certificate leaf6405InnerLog leaf6405Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk96RoundedFacts chi342RoundedFacts
    innerPair377RoundedFacts leaf6405RoundedFacts (by rfl)

private theorem leaf6405FlatSound : Sound leaf6405Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6405CertificateValid
    leaf6405InnerLogValid leaf6405CoversExact leaf6405LowerChecked

private noncomputable def leaf6406Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (23/32), chiHi := (47/64) }

private noncomputable def leaf6406Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109047/67108864) }, vSqrt := { lower := (32765/32768), upper := (8589426687/8588851712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (199712683/134217728) }, upper := { exponent := 1, mantissa := (3139/2048) } }, logOuter := sk95LogOuterCertificate, logK := sk95LogKCertificate, logChi := chi343LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (17178278399/17177703424) } }, logDArg := sk95LogDArgCertificate }

private noncomputable def leaf6406InnerLog : WideLogData :=
  innerPair377Data

set_option maxRecDepth 1000000 in
private theorem leaf6406LocalValidity :
    LeafFacts leaf6406Box leaf6406Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6406Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8589426687/8588851712) }) = true
      norm_num [leaf6406Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6406CertificateValid :
    WideCertificateValid leaf6406Box leaf6406Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk95ValidityFacts chi343ValidityFacts
    leaf6406LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6406CoverageChecked :
    coverageCheck (innerAD leaf6406Box) leaf6406InnerLog = true := by
  rfl'

private theorem leaf6406InnerLogValid :
    leaf6406InnerLog.Valid 8 (innerAD leaf6406Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint483PositiveFacts.valid leaf6406CoverageChecked

private noncomputable def leaf6406InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814821/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6406InputLogOnePlusV_eq :
    leaf6406InputLogOnePlusV = outerEnclosure 24
      (leaf6406Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6406RoundedFacts : LeafRoundedFacts 8
    leaf6406Certificate.logOnePlusV leaf6406InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6406InputLogOnePlusV_eq }

private noncomputable def leaf6406Inputs : Inputs :=
  inputsOfCaches globalInput sk95RoundedInputs
    chi343InputQChi innerPair377Input
    leaf6406InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6406LowerChecked :
    lowerCheck 24 leaf6406Box leaf6406Inputs = true := by
  rfl'

private theorem leaf6406CoversExact : CoversExact 8
    leaf6406Box leaf6406Certificate leaf6406InnerLog leaf6406Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk95RoundedFacts chi343RoundedFacts
    innerPair377RoundedFacts leaf6406RoundedFacts (by rfl)

private theorem leaf6406FlatSound : Sound leaf6406Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6406CertificateValid
    leaf6406InnerLogValid leaf6406CoversExact leaf6406LowerChecked

private noncomputable def leaf6407Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (47/64), chiHi := (3/4) }

private noncomputable def leaf6407Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109049/67108864) }, vSqrt := { lower := (32765/32768), upper := (8589426687/8588828672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (202596089/134217728) }, upper := { exponent := 1, mantissa := (199/128) } }, logOuter := sk95LogOuterCertificate, logK := sk95LogKCertificate, logChi := chi344LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (17178255359/17177657344) } }, logDArg := sk95LogDArgCertificate }

private noncomputable def leaf6407InnerLog : WideLogData :=
  innerPair382Data

set_option maxRecDepth 1000000 in
private theorem leaf6407LocalValidity :
    LeafFacts leaf6407Box leaf6407Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6407Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8589426687/8588828672) }) = true
      norm_num [leaf6407Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6407CertificateValid :
    WideCertificateValid leaf6407Box leaf6407Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk95ValidityFacts chi344ValidityFacts
    leaf6407LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6407CoverageChecked :
    coverageCheck (innerAD leaf6407Box) leaf6407InnerLog = true := by
  rfl'

private theorem leaf6407InnerLogValid :
    leaf6407InnerLog.Valid 8 (innerAD leaf6407Box) :=
  wideLogDataValid_of_cachedCheck endpoint99PositiveFacts
    endpoint483PositiveFacts.valid leaf6407CoverageChecked

private noncomputable def leaf6407InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629665/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6407InputLogOnePlusV_eq :
    leaf6407InputLogOnePlusV = outerEnclosure 24
      (leaf6407Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6407RoundedFacts : LeafRoundedFacts 8
    leaf6407Certificate.logOnePlusV leaf6407InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6407InputLogOnePlusV_eq }

private noncomputable def leaf6407Inputs : Inputs :=
  inputsOfCaches globalInput sk95RoundedInputs
    chi344InputQChi innerPair382Input
    leaf6407InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6407LowerChecked :
    lowerCheck 24 leaf6407Box leaf6407Inputs = true := by
  rfl'

private theorem leaf6407CoversExact : CoversExact 8
    leaf6407Box leaf6407Certificate leaf6407InnerLog leaf6407Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk95RoundedFacts chi344RoundedFacts
    innerPair382RoundedFacts leaf6407RoundedFacts (by rfl)

private theorem leaf6407FlatSound : Sound leaf6407Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6407CertificateValid
    leaf6407InnerLogValid leaf6407CoversExact leaf6407LowerChecked

private noncomputable def leaf6408Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (23/32), chiHi := (47/64) }

private noncomputable def leaf6408Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109049/67108864) }, vSqrt := { lower := (32765/32768), upper := (8589426687/8588827648) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (202727153/134217728) }, upper := { exponent := 1, mantissa := (1593/1024) } }, logOuter := sk96LogOuterCertificate, logK := sk96LogKCertificate, logChi := chi343LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (17178254335/17177655296) } }, logDArg := sk96LogDArgCertificate }

private noncomputable def leaf6408InnerLog : WideLogData :=
  innerPair382Data

set_option maxRecDepth 1000000 in
private theorem leaf6408LocalValidity :
    LeafFacts leaf6408Box leaf6408Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6408Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8589426687/8588827648) }) = true
      norm_num [leaf6408Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6408CertificateValid :
    WideCertificateValid leaf6408Box leaf6408Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk96ValidityFacts chi343ValidityFacts
    leaf6408LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6408CoverageChecked :
    coverageCheck (innerAD leaf6408Box) leaf6408InnerLog = true := by
  rfl'

private theorem leaf6408InnerLogValid :
    leaf6408InnerLog.Valid 8 (innerAD leaf6408Box) :=
  wideLogDataValid_of_cachedCheck endpoint99PositiveFacts
    endpoint483PositiveFacts.valid leaf6408CoverageChecked

private noncomputable def leaf6408InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814833/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6408InputLogOnePlusV_eq :
    leaf6408InputLogOnePlusV = outerEnclosure 24
      (leaf6408Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6408RoundedFacts : LeafRoundedFacts 8
    leaf6408Certificate.logOnePlusV leaf6408InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6408InputLogOnePlusV_eq }

private noncomputable def leaf6408Inputs : Inputs :=
  inputsOfCaches globalInput sk96RoundedInputs
    chi343InputQChi innerPair382Input
    leaf6408InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6408LowerChecked :
    lowerCheck 24 leaf6408Box leaf6408Inputs = true := by
  rfl'

private theorem leaf6408CoversExact : CoversExact 8
    leaf6408Box leaf6408Certificate leaf6408InnerLog leaf6408Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk96RoundedFacts chi343RoundedFacts
    innerPair382RoundedFacts leaf6408RoundedFacts (by rfl)

private theorem leaf6408FlatSound : Sound leaf6408Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6408CertificateValid
    leaf6408InnerLogValid leaf6408CoversExact leaf6408LowerChecked

private noncomputable def leaf6409Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (47/64), chiHi := (3/4) }

private noncomputable def leaf6409Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109051/67108864) }, vSqrt := { lower := (32765/32768), upper := (8589426687/8588804096) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (205676091/134217728) }, upper := { exponent := 1, mantissa := (101/64) } }, logOuter := sk96LogOuterCertificate, logK := sk96LogKCertificate, logChi := chi344LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (17178230783/17177608192) } }, logDArg := sk96LogDArgCertificate }

private noncomputable def leaf6409InnerLog : WideLogData :=
  innerPair744Data

set_option maxRecDepth 1000000 in
private theorem leaf6409LocalValidity :
    LeafFacts leaf6409Box leaf6409Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6409Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8589426687/8588804096) }) = true
      norm_num [leaf6409Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6409CertificateValid :
    WideCertificateValid leaf6409Box leaf6409Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk96ValidityFacts chi344ValidityFacts
    leaf6409LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6409CoverageChecked :
    coverageCheck (innerAD leaf6409Box) leaf6409InnerLog = true := by
  rfl'

private theorem leaf6409InnerLogValid :
    leaf6409InnerLog.Valid 8 (innerAD leaf6409Box) :=
  wideLogDataValid_of_cachedCheck endpoint482PositiveFacts
    endpoint484PositiveFacts.valid leaf6409CoverageChecked

private noncomputable def leaf6409InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629689/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6409InputLogOnePlusV_eq :
    leaf6409InputLogOnePlusV = outerEnclosure 24
      (leaf6409Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6409RoundedFacts : LeafRoundedFacts 8
    leaf6409Certificate.logOnePlusV leaf6409InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6409InputLogOnePlusV_eq }

private noncomputable def leaf6409Inputs : Inputs :=
  inputsOfCaches globalInput sk96RoundedInputs
    chi344InputQChi innerPair744Input
    leaf6409InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6409LowerChecked :
    lowerCheck 24 leaf6409Box leaf6409Inputs = true := by
  rfl'

private theorem leaf6409CoversExact : CoversExact 8
    leaf6409Box leaf6409Certificate leaf6409InnerLog leaf6409Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk96RoundedFacts chi344RoundedFacts
    innerPair744RoundedFacts leaf6409RoundedFacts (by rfl)

private theorem leaf6409FlatSound : Sound leaf6409Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6409CertificateValid
    leaf6409InnerLogValid leaf6409CoversExact leaf6409LowerChecked

private noncomputable def leaf6410Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (11/16), chiHi := (45/64) }

private noncomputable def leaf6410Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109047/67108864) }, vSqrt := { lower := (32765/32768), upper := (8589426687/8588851712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (199712683/134217728) }, upper := { exponent := 1, mantissa := (3139/2048) } }, logOuter := sk97LogOuterCertificate, logK := sk97LogKCertificate, logChi := chi341LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (17178278399/17177703424) } }, logDArg := sk97LogDArgCertificate }

private noncomputable def leaf6410InnerLog : WideLogData :=
  innerPair377Data

set_option maxRecDepth 1000000 in
private theorem leaf6410LocalValidity :
    LeafFacts leaf6410Box leaf6410Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6410Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8589426687/8588851712) }) = true
      norm_num [leaf6410Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6410CertificateValid :
    WideCertificateValid leaf6410Box leaf6410Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk97ValidityFacts chi341ValidityFacts
    leaf6410LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6410CoverageChecked :
    coverageCheck (innerAD leaf6410Box) leaf6410InnerLog = true := by
  rfl'

private theorem leaf6410InnerLogValid :
    leaf6410InnerLog.Valid 8 (innerAD leaf6410Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint483PositiveFacts.valid leaf6410CoverageChecked

private noncomputable def leaf6410InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814821/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6410InputLogOnePlusV_eq :
    leaf6410InputLogOnePlusV = outerEnclosure 24
      (leaf6410Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6410RoundedFacts : LeafRoundedFacts 8
    leaf6410Certificate.logOnePlusV leaf6410InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6410InputLogOnePlusV_eq }

private noncomputable def leaf6410Inputs : Inputs :=
  inputsOfCaches globalInput sk97RoundedInputs
    chi341InputQChi innerPair377Input
    leaf6410InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6410LowerChecked :
    lowerCheck 24 leaf6410Box leaf6410Inputs = true := by
  rfl'

private theorem leaf6410CoversExact : CoversExact 8
    leaf6410Box leaf6410Certificate leaf6410InnerLog leaf6410Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk97RoundedFacts chi341RoundedFacts
    innerPair377RoundedFacts leaf6410RoundedFacts (by rfl)

private theorem leaf6410FlatSound : Sound leaf6410Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6410CertificateValid
    leaf6410InnerLogValid leaf6410CoversExact leaf6410LowerChecked

private noncomputable def leaf6411Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (45/64), chiHi := (23/32) }

private noncomputable def leaf6411Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109049/67108864) }, vSqrt := { lower := (32765/32768), upper := (8589426687/8588827648) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (202727153/134217728) }, upper := { exponent := 1, mantissa := (1593/1024) } }, logOuter := sk97LogOuterCertificate, logK := sk97LogKCertificate, logChi := chi342LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (17178254335/17177655296) } }, logDArg := sk97LogDArgCertificate }

private noncomputable def leaf6411InnerLog : WideLogData :=
  innerPair382Data

set_option maxRecDepth 1000000 in
private theorem leaf6411LocalValidity :
    LeafFacts leaf6411Box leaf6411Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6411Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8589426687/8588827648) }) = true
      norm_num [leaf6411Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6411CertificateValid :
    WideCertificateValid leaf6411Box leaf6411Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk97ValidityFacts chi342ValidityFacts
    leaf6411LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6411CoverageChecked :
    coverageCheck (innerAD leaf6411Box) leaf6411InnerLog = true := by
  rfl'

private theorem leaf6411InnerLogValid :
    leaf6411InnerLog.Valid 8 (innerAD leaf6411Box) :=
  wideLogDataValid_of_cachedCheck endpoint99PositiveFacts
    endpoint483PositiveFacts.valid leaf6411CoverageChecked

private noncomputable def leaf6411InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814833/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6411InputLogOnePlusV_eq :
    leaf6411InputLogOnePlusV = outerEnclosure 24
      (leaf6411Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6411RoundedFacts : LeafRoundedFacts 8
    leaf6411Certificate.logOnePlusV leaf6411InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6411InputLogOnePlusV_eq }

private noncomputable def leaf6411Inputs : Inputs :=
  inputsOfCaches globalInput sk97RoundedInputs
    chi342InputQChi innerPair382Input
    leaf6411InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6411LowerChecked :
    lowerCheck 24 leaf6411Box leaf6411Inputs = true := by
  rfl'

private theorem leaf6411CoversExact : CoversExact 8
    leaf6411Box leaf6411Certificate leaf6411InnerLog leaf6411Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk97RoundedFacts chi342RoundedFacts
    innerPair382RoundedFacts leaf6411RoundedFacts (by rfl)

private theorem leaf6411FlatSound : Sound leaf6411Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6411CertificateValid
    leaf6411InnerLogValid leaf6411CoversExact leaf6411LowerChecked

private noncomputable def leaf6412Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (11/16), chiHi := (45/64) }

private noncomputable def leaf6412Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109049/67108864) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588828672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (202596089/134217728) }, upper := { exponent := 1, mantissa := (199/128) } }, logOuter := sk98LogOuterCertificate, logK := sk98LogKCertificate, logChi := chi341LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178255359/17177657344) } }, logDArg := sk98LogDArgCertificate }

private noncomputable def leaf6412InnerLog : WideLogData :=
  innerPair382Data

set_option maxRecDepth 1000000 in
private theorem leaf6412LocalValidity :
    LeafFacts leaf6412Box leaf6412Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6412Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588828672) }) = true
      norm_num [leaf6412Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6412CertificateValid :
    WideCertificateValid leaf6412Box leaf6412Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk98ValidityFacts chi341ValidityFacts
    leaf6412LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6412CoverageChecked :
    coverageCheck (innerAD leaf6412Box) leaf6412InnerLog = true := by
  rfl'

private theorem leaf6412InnerLogValid :
    leaf6412InnerLog.Valid 8 (innerAD leaf6412Box) :=
  wideLogDataValid_of_cachedCheck endpoint99PositiveFacts
    endpoint483PositiveFacts.valid leaf6412CoverageChecked

private noncomputable def leaf6412InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629665/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6412InputLogOnePlusV_eq :
    leaf6412InputLogOnePlusV = outerEnclosure 24
      (leaf6412Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6412RoundedFacts : LeafRoundedFacts 8
    leaf6412Certificate.logOnePlusV leaf6412InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6412InputLogOnePlusV_eq }

private noncomputable def leaf6412Inputs : Inputs :=
  inputsOfCaches globalInput sk98RoundedInputs
    chi341InputQChi innerPair382Input
    leaf6412InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6412LowerChecked :
    lowerCheck 24 leaf6412Box leaf6412Inputs = true := by
  rfl'

private theorem leaf6412CoversExact : CoversExact 8
    leaf6412Box leaf6412Certificate leaf6412InnerLog leaf6412Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk98RoundedFacts chi341RoundedFacts
    innerPair382RoundedFacts leaf6412RoundedFacts (by rfl)

private theorem leaf6412FlatSound : Sound leaf6412Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6412CertificateValid
    leaf6412InnerLogValid leaf6412CoversExact leaf6412LowerChecked

private noncomputable def leaf6413Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (45/64), chiHi := (23/32) }

private noncomputable def leaf6413Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109051/67108864) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588804096) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (205676091/134217728) }, upper := { exponent := 1, mantissa := (101/64) } }, logOuter := sk98LogOuterCertificate, logK := sk98LogKCertificate, logChi := chi342LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178230783/17177608192) } }, logDArg := sk98LogDArgCertificate }

private noncomputable def leaf6413InnerLog : WideLogData :=
  innerPair744Data

set_option maxRecDepth 1000000 in
private theorem leaf6413LocalValidity :
    LeafFacts leaf6413Box leaf6413Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6413Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588804096) }) = true
      norm_num [leaf6413Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6413CertificateValid :
    WideCertificateValid leaf6413Box leaf6413Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk98ValidityFacts chi342ValidityFacts
    leaf6413LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6413CoverageChecked :
    coverageCheck (innerAD leaf6413Box) leaf6413InnerLog = true := by
  rfl'

private theorem leaf6413InnerLogValid :
    leaf6413InnerLog.Valid 8 (innerAD leaf6413Box) :=
  wideLogDataValid_of_cachedCheck endpoint482PositiveFacts
    endpoint484PositiveFacts.valid leaf6413CoverageChecked

private noncomputable def leaf6413InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629689/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6413InputLogOnePlusV_eq :
    leaf6413InputLogOnePlusV = outerEnclosure 24
      (leaf6413Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6413RoundedFacts : LeafRoundedFacts 8
    leaf6413Certificate.logOnePlusV leaf6413InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6413InputLogOnePlusV_eq }

private noncomputable def leaf6413Inputs : Inputs :=
  inputsOfCaches globalInput sk98RoundedInputs
    chi342InputQChi innerPair744Input
    leaf6413InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6413LowerChecked :
    lowerCheck 24 leaf6413Box leaf6413Inputs = true := by
  rfl'

private theorem leaf6413CoversExact : CoversExact 8
    leaf6413Box leaf6413Certificate leaf6413InnerLog leaf6413Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk98RoundedFacts chi342RoundedFacts
    innerPair744RoundedFacts leaf6413RoundedFacts (by rfl)

private theorem leaf6413FlatSound : Sound leaf6413Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6413CertificateValid
    leaf6413InnerLogValid leaf6413CoversExact leaf6413LowerChecked

private noncomputable def leaf6414Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (23/32), chiHi := (47/64) }

private noncomputable def leaf6414Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109051/67108864) }, vSqrt := { lower := (32765/32768), upper := (2863142229/2862934528) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (205741623/134217728) }, upper := { exponent := 1, mantissa := (3233/2048) } }, logOuter := sk97LogOuterCertificate, logK := sk97LogKCertificate, logChi := chi343LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (5726076757/5725869056) } }, logDArg := sk97LogDArgCertificate }

private noncomputable def leaf6414InnerLog : WideLogData :=
  innerPair744Data

set_option maxRecDepth 1000000 in
private theorem leaf6414LocalValidity :
    LeafFacts leaf6414Box leaf6414Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6414Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (2863142229/2862934528) }) = true
      norm_num [leaf6414Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6414CertificateValid :
    WideCertificateValid leaf6414Box leaf6414Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk97ValidityFacts chi343ValidityFacts
    leaf6414LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6414CoverageChecked :
    coverageCheck (innerAD leaf6414Box) leaf6414InnerLog = true := by
  rfl'

private theorem leaf6414InnerLogValid :
    leaf6414InnerLog.Valid 8 (innerAD leaf6414Box) :=
  wideLogDataValid_of_cachedCheck endpoint482PositiveFacts
    endpoint484PositiveFacts.valid leaf6414CoverageChecked

private noncomputable def leaf6414InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629689/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6414InputLogOnePlusV_eq :
    leaf6414InputLogOnePlusV = outerEnclosure 24
      (leaf6414Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6414RoundedFacts : LeafRoundedFacts 8
    leaf6414Certificate.logOnePlusV leaf6414InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6414InputLogOnePlusV_eq }

private noncomputable def leaf6414Inputs : Inputs :=
  inputsOfCaches globalInput sk97RoundedInputs
    chi343InputQChi innerPair744Input
    leaf6414InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6414LowerChecked :
    lowerCheck 24 leaf6414Box leaf6414Inputs = true := by
  rfl'

private theorem leaf6414CoversExact : CoversExact 8
    leaf6414Box leaf6414Certificate leaf6414InnerLog leaf6414Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk97RoundedFacts chi343RoundedFacts
    innerPair744RoundedFacts leaf6414RoundedFacts (by rfl)

private theorem leaf6414FlatSound : Sound leaf6414Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6414CertificateValid
    leaf6414InnerLogValid leaf6414CoversExact leaf6414LowerChecked

private noncomputable def leaf6415Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (47/64), chiHi := (3/4) }

private noncomputable def leaf6415Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109053/67108864) }, vSqrt := { lower := (32765/32768), upper := (8589426687/8588779520) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (208756093/134217728) }, upper := { exponent := 1, mantissa := (205/128) } }, logOuter := sk97LogOuterCertificate, logK := sk97LogKCertificate, logChi := chi344LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (17178206207/17177559040) } }, logDArg := sk97LogDArgCertificate }

private noncomputable def leaf6415InnerLog : WideLogData :=
  innerPair745Data

set_option maxRecDepth 1000000 in
private theorem leaf6415LocalValidity :
    LeafFacts leaf6415Box leaf6415Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6415Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8589426687/8588779520) }) = true
      norm_num [leaf6415Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6415CertificateValid :
    WideCertificateValid leaf6415Box leaf6415Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk97ValidityFacts chi344ValidityFacts
    leaf6415LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6415CoverageChecked :
    coverageCheck (innerAD leaf6415Box) leaf6415InnerLog = true := by
  rfl'

private theorem leaf6415InnerLogValid :
    leaf6415InnerLog.Valid 8 (innerAD leaf6415Box) :=
  wideLogDataValid_of_cachedCheck endpoint482PositiveFacts
    endpoint485PositiveFacts.valid leaf6415CoverageChecked

private noncomputable def leaf6415InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629713/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6415InputLogOnePlusV_eq :
    leaf6415InputLogOnePlusV = outerEnclosure 24
      (leaf6415Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6415RoundedFacts : LeafRoundedFacts 8
    leaf6415Certificate.logOnePlusV leaf6415InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6415InputLogOnePlusV_eq }

private noncomputable def leaf6415Inputs : Inputs :=
  inputsOfCaches globalInput sk97RoundedInputs
    chi344InputQChi innerPair745Input
    leaf6415InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6415LowerChecked :
    lowerCheck 24 leaf6415Box leaf6415Inputs = true := by
  rfl'

private theorem leaf6415CoversExact : CoversExact 8
    leaf6415Box leaf6415Certificate leaf6415InnerLog leaf6415Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk97RoundedFacts chi344RoundedFacts
    innerPair745RoundedFacts leaf6415RoundedFacts (by rfl)

private theorem leaf6415FlatSound : Sound leaf6415Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6415CertificateValid
    leaf6415InnerLogValid leaf6415CoversExact leaf6415LowerChecked

private noncomputable def leaf6416Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (23/32), chiHi := (47/64) }

private noncomputable def leaf6416Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109053/67108864) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588779520) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (208756093/134217728) }, upper := { exponent := 1, mantissa := (205/128) } }, logOuter := sk98LogOuterCertificate, logK := sk98LogKCertificate, logChi := chi343LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178206207/17177559040) } }, logDArg := sk98LogDArgCertificate }

private noncomputable def leaf6416InnerLog : WideLogData :=
  innerPair745Data

set_option maxRecDepth 1000000 in
private theorem leaf6416LocalValidity :
    LeafFacts leaf6416Box leaf6416Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6416Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588779520) }) = true
      norm_num [leaf6416Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6416CertificateValid :
    WideCertificateValid leaf6416Box leaf6416Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk98ValidityFacts chi343ValidityFacts
    leaf6416LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6416CoverageChecked :
    coverageCheck (innerAD leaf6416Box) leaf6416InnerLog = true := by
  rfl'

private theorem leaf6416InnerLogValid :
    leaf6416InnerLog.Valid 8 (innerAD leaf6416Box) :=
  wideLogDataValid_of_cachedCheck endpoint482PositiveFacts
    endpoint485PositiveFacts.valid leaf6416CoverageChecked

private noncomputable def leaf6416InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629713/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6416InputLogOnePlusV_eq :
    leaf6416InputLogOnePlusV = outerEnclosure 24
      (leaf6416Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6416RoundedFacts : LeafRoundedFacts 8
    leaf6416Certificate.logOnePlusV leaf6416InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6416InputLogOnePlusV_eq }

private noncomputable def leaf6416Inputs : Inputs :=
  inputsOfCaches globalInput sk98RoundedInputs
    chi343InputQChi innerPair745Input
    leaf6416InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6416LowerChecked :
    lowerCheck 24 leaf6416Box leaf6416Inputs = true := by
  rfl'

private theorem leaf6416CoversExact : CoversExact 8
    leaf6416Box leaf6416Certificate leaf6416InnerLog leaf6416Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk98RoundedFacts chi343RoundedFacts
    innerPair745RoundedFacts leaf6416RoundedFacts (by rfl)

private theorem leaf6416FlatSound : Sound leaf6416Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6416CertificateValid
    leaf6416InnerLogValid leaf6416CoversExact leaf6416LowerChecked

private noncomputable def leaf6417Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (47/64), chiHi := (3/4) }

private noncomputable def leaf6417Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109055/67108864) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588754944) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (211836095/134217728) }, upper := { exponent := 1, mantissa := (13/8) } }, logOuter := sk98LogOuterCertificate, logK := sk98LogKCertificate, logChi := chi344LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178181631/17177509888) } }, logDArg := sk98LogDArgCertificate }

private noncomputable def leaf6417InnerLog : WideLogData :=
  innerPair749Data

set_option maxRecDepth 1000000 in
private theorem leaf6417LocalValidity :
    LeafFacts leaf6417Box leaf6417Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6417Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588754944) }) = true
      norm_num [leaf6417Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6417CertificateValid :
    WideCertificateValid leaf6417Box leaf6417Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk98ValidityFacts chi344ValidityFacts
    leaf6417LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6417CoverageChecked :
    coverageCheck (innerAD leaf6417Box) leaf6417InnerLog = true := by
  rfl'

private theorem leaf6417InnerLogValid :
    leaf6417InnerLog.Valid 8 (innerAD leaf6417Box) :=
  wideLogDataValid_of_cachedCheck endpoint483PositiveFacts
    endpoint485PositiveFacts.valid leaf6417CoverageChecked

private noncomputable def leaf6417InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629737/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6417InputLogOnePlusV_eq :
    leaf6417InputLogOnePlusV = outerEnclosure 24
      (leaf6417Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6417RoundedFacts : LeafRoundedFacts 8
    leaf6417Certificate.logOnePlusV leaf6417InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6417InputLogOnePlusV_eq }

private noncomputable def leaf6417Inputs : Inputs :=
  inputsOfCaches globalInput sk98RoundedInputs
    chi344InputQChi innerPair749Input
    leaf6417InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6417LowerChecked :
    lowerCheck 24 leaf6417Box leaf6417Inputs = true := by
  rfl'

private theorem leaf6417CoversExact : CoversExact 8
    leaf6417Box leaf6417Certificate leaf6417InnerLog leaf6417Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk98RoundedFacts chi344RoundedFacts
    innerPair749RoundedFacts leaf6417RoundedFacts (by rfl)

private theorem leaf6417FlatSound : Sound leaf6417Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6417CertificateValid
    leaf6417InnerLogValid leaf6417CoversExact leaf6417LowerChecked

private noncomputable def component128Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (5/8), chiHi := (21/32) }

set_option maxRecDepth 1000000 in
private theorem component128Node0_sound : Sound component128Node0Box :=
  sound_of_literal_split component128Node0Box leaf6356Box leaf6357Box
    .chi (41/64) (by rfl) (by rfl)
    leaf6356FlatSound leaf6357FlatSound

private noncomputable def component128Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (5/8), chiHi := (21/32) }

set_option maxRecDepth 1000000 in
private theorem component128Node1_sound : Sound component128Node1Box :=
  sound_of_literal_split component128Node1Box leaf6358Box leaf6359Box
    .chi (41/64) (by rfl) (by rfl)
    leaf6358FlatSound leaf6359FlatSound

private noncomputable def component128Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (5/8), chiHi := (21/32) }

set_option maxRecDepth 1000000 in
private theorem component128Node2_sound : Sound component128Node2Box :=
  sound_of_literal_split component128Node2Box component128Node0Box component128Node1Box
    .k (41/16) (by rfl) (by rfl)
    component128Node0_sound component128Node1_sound

private noncomputable def component128Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (21/32), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component128Node3_sound : Sound component128Node3Box :=
  sound_of_literal_split component128Node3Box leaf6360Box leaf6361Box
    .chi (43/64) (by rfl) (by rfl)
    leaf6360FlatSound leaf6361FlatSound

private noncomputable def component128Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (21/32), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component128Node4_sound : Sound component128Node4Box :=
  sound_of_literal_split component128Node4Box leaf6362Box leaf6363Box
    .chi (43/64) (by rfl) (by rfl)
    leaf6362FlatSound leaf6363FlatSound

private noncomputable def component128Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (21/32), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component128Node5_sound : Sound component128Node5Box :=
  sound_of_literal_split component128Node5Box component128Node3Box component128Node4Box
    .k (41/16) (by rfl) (by rfl)
    component128Node3_sound component128Node4_sound

private noncomputable def component128Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (5/8), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component128Node6_sound : Sound component128Node6Box :=
  sound_of_literal_split component128Node6Box component128Node2Box component128Node5Box
    .chi (21/32) (by rfl) (by rfl)
    component128Node2_sound component128Node5_sound

private noncomputable def component128Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (5/8), chiHi := (21/32) }

set_option maxRecDepth 1000000 in
private theorem component128Node7_sound : Sound component128Node7Box :=
  sound_of_literal_split component128Node7Box leaf6364Box leaf6365Box
    .chi (41/64) (by rfl) (by rfl)
    leaf6364FlatSound leaf6365FlatSound

private noncomputable def component128Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (5/8), chiHi := (21/32) }

set_option maxRecDepth 1000000 in
private theorem component128Node8_sound : Sound component128Node8Box :=
  sound_of_literal_split component128Node8Box leaf6366Box leaf6367Box
    .chi (41/64) (by rfl) (by rfl)
    leaf6366FlatSound leaf6367FlatSound

private noncomputable def component128Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (5/8), chiHi := (21/32) }

set_option maxRecDepth 1000000 in
private theorem component128Node9_sound : Sound component128Node9Box :=
  sound_of_literal_split component128Node9Box component128Node7Box component128Node8Box
    .k (43/16) (by rfl) (by rfl)
    component128Node7_sound component128Node8_sound

private noncomputable def component128Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (21/32), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component128Node10_sound : Sound component128Node10Box :=
  sound_of_literal_split component128Node10Box leaf6368Box leaf6369Box
    .chi (43/64) (by rfl) (by rfl)
    leaf6368FlatSound leaf6369FlatSound

private noncomputable def component128Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (21/32), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component128Node11_sound : Sound component128Node11Box :=
  sound_of_literal_split component128Node11Box leaf6370Box leaf6371Box
    .chi (43/64) (by rfl) (by rfl)
    leaf6370FlatSound leaf6371FlatSound

private noncomputable def component128Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (21/32), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component128Node12_sound : Sound component128Node12Box :=
  sound_of_literal_split component128Node12Box component128Node10Box component128Node11Box
    .k (43/16) (by rfl) (by rfl)
    component128Node10_sound component128Node11_sound

private noncomputable def component128Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (5/8), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component128Node13_sound : Sound component128Node13Box :=
  sound_of_literal_split component128Node13Box component128Node9Box component128Node12Box
    .chi (21/32) (by rfl) (by rfl)
    component128Node9_sound component128Node12_sound

private noncomputable def component128Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (11/4), chiLo := (5/8), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component128Node14_sound : Sound component128Node14Box :=
  sound_of_literal_split component128Node14Box component128Node6Box component128Node13Box
    .k (21/8) (by rfl) (by rfl)
    component128Node6_sound component128Node13_sound

private noncomputable def component128Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (11/16), chiHi := (23/32) }

set_option maxRecDepth 1000000 in
private theorem component128Node15_sound : Sound component128Node15Box :=
  sound_of_literal_split component128Node15Box leaf6372Box leaf6373Box
    .chi (45/64) (by rfl) (by rfl)
    leaf6372FlatSound leaf6373FlatSound

private noncomputable def component128Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (11/16), chiHi := (23/32) }

set_option maxRecDepth 1000000 in
private theorem component128Node16_sound : Sound component128Node16Box :=
  sound_of_literal_split component128Node16Box leaf6374Box leaf6375Box
    .chi (45/64) (by rfl) (by rfl)
    leaf6374FlatSound leaf6375FlatSound

private noncomputable def component128Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (11/16), chiHi := (23/32) }

set_option maxRecDepth 1000000 in
private theorem component128Node17_sound : Sound component128Node17Box :=
  sound_of_literal_split component128Node17Box component128Node15Box component128Node16Box
    .k (41/16) (by rfl) (by rfl)
    component128Node15_sound component128Node16_sound

private noncomputable def component128Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (23/32), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component128Node18_sound : Sound component128Node18Box :=
  sound_of_literal_split component128Node18Box leaf6376Box leaf6377Box
    .k (41/16) (by rfl) (by rfl)
    leaf6376FlatSound leaf6377FlatSound

private noncomputable def component128Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (11/16), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component128Node19_sound : Sound component128Node19Box :=
  sound_of_literal_split component128Node19Box component128Node17Box component128Node18Box
    .chi (23/32) (by rfl) (by rfl)
    component128Node17_sound component128Node18_sound

private noncomputable def component128Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (11/16), chiHi := (23/32) }

set_option maxRecDepth 1000000 in
private theorem component128Node20_sound : Sound component128Node20Box :=
  sound_of_literal_split component128Node20Box leaf6378Box leaf6379Box
    .chi (45/64) (by rfl) (by rfl)
    leaf6378FlatSound leaf6379FlatSound

private noncomputable def component128Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (11/16), chiHi := (23/32) }

set_option maxRecDepth 1000000 in
private theorem component128Node21_sound : Sound component128Node21Box :=
  sound_of_literal_split component128Node21Box leaf6380Box leaf6381Box
    .chi (45/64) (by rfl) (by rfl)
    leaf6380FlatSound leaf6381FlatSound

private noncomputable def component128Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (11/16), chiHi := (23/32) }

set_option maxRecDepth 1000000 in
private theorem component128Node22_sound : Sound component128Node22Box :=
  sound_of_literal_split component128Node22Box component128Node20Box component128Node21Box
    .k (43/16) (by rfl) (by rfl)
    component128Node20_sound component128Node21_sound

private noncomputable def component128Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (23/32), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component128Node23_sound : Sound component128Node23Box :=
  sound_of_literal_split component128Node23Box leaf6382Box leaf6383Box
    .chi (47/64) (by rfl) (by rfl)
    leaf6382FlatSound leaf6383FlatSound

private noncomputable def component128Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (23/32), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component128Node24_sound : Sound component128Node24Box :=
  sound_of_literal_split component128Node24Box leaf6384Box leaf6385Box
    .chi (47/64) (by rfl) (by rfl)
    leaf6384FlatSound leaf6385FlatSound

private noncomputable def component128Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (23/32), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component128Node25_sound : Sound component128Node25Box :=
  sound_of_literal_split component128Node25Box component128Node23Box component128Node24Box
    .k (43/16) (by rfl) (by rfl)
    component128Node23_sound component128Node24_sound

private noncomputable def component128Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (11/16), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component128Node26_sound : Sound component128Node26Box :=
  sound_of_literal_split component128Node26Box component128Node22Box component128Node25Box
    .chi (23/32) (by rfl) (by rfl)
    component128Node22_sound component128Node25_sound

private noncomputable def component128Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (11/4), chiLo := (11/16), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component128Node27_sound : Sound component128Node27Box :=
  sound_of_literal_split component128Node27Box component128Node19Box component128Node26Box
    .k (21/8) (by rfl) (by rfl)
    component128Node19_sound component128Node26_sound

private noncomputable def component128Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (11/4), chiLo := (5/8), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component128Node28_sound : Sound component128Node28Box :=
  sound_of_literal_split component128Node28Box component128Node14Box component128Node27Box
    .chi (11/16) (by rfl) (by rfl)
    component128Node14_sound component128Node27_sound

private noncomputable def component128Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (5/8), chiHi := (21/32) }

set_option maxRecDepth 1000000 in
private theorem component128Node29_sound : Sound component128Node29Box :=
  sound_of_literal_split component128Node29Box leaf6386Box leaf6387Box
    .chi (41/64) (by rfl) (by rfl)
    leaf6386FlatSound leaf6387FlatSound

private noncomputable def component128Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (5/8), chiHi := (21/32) }

set_option maxRecDepth 1000000 in
private theorem component128Node30_sound : Sound component128Node30Box :=
  sound_of_literal_split component128Node30Box leaf6388Box leaf6389Box
    .chi (41/64) (by rfl) (by rfl)
    leaf6388FlatSound leaf6389FlatSound

private noncomputable def component128Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (5/8), chiHi := (21/32) }

set_option maxRecDepth 1000000 in
private theorem component128Node31_sound : Sound component128Node31Box :=
  sound_of_literal_split component128Node31Box component128Node29Box component128Node30Box
    .k (45/16) (by rfl) (by rfl)
    component128Node29_sound component128Node30_sound

private noncomputable def component128Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (21/32), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component128Node32_sound : Sound component128Node32Box :=
  sound_of_literal_split component128Node32Box leaf6390Box leaf6391Box
    .chi (43/64) (by rfl) (by rfl)
    leaf6390FlatSound leaf6391FlatSound

private noncomputable def component128Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (21/32), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component128Node33_sound : Sound component128Node33Box :=
  sound_of_literal_split component128Node33Box leaf6392Box leaf6393Box
    .chi (43/64) (by rfl) (by rfl)
    leaf6392FlatSound leaf6393FlatSound

private noncomputable def component128Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (21/32), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component128Node34_sound : Sound component128Node34Box :=
  sound_of_literal_split component128Node34Box component128Node32Box component128Node33Box
    .k (45/16) (by rfl) (by rfl)
    component128Node32_sound component128Node33_sound

private noncomputable def component128Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (5/8), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component128Node35_sound : Sound component128Node35Box :=
  sound_of_literal_split component128Node35Box component128Node31Box component128Node34Box
    .chi (21/32) (by rfl) (by rfl)
    component128Node31_sound component128Node34_sound

private noncomputable def component128Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (5/8), chiHi := (21/32) }

set_option maxRecDepth 1000000 in
private theorem component128Node36_sound : Sound component128Node36Box :=
  sound_of_literal_split component128Node36Box leaf6394Box leaf6395Box
    .chi (41/64) (by rfl) (by rfl)
    leaf6394FlatSound leaf6395FlatSound

private noncomputable def component128Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (5/8), chiHi := (21/32) }

set_option maxRecDepth 1000000 in
private theorem component128Node37_sound : Sound component128Node37Box :=
  sound_of_literal_split component128Node37Box leaf6396Box leaf6397Box
    .chi (41/64) (by rfl) (by rfl)
    leaf6396FlatSound leaf6397FlatSound

private noncomputable def component128Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (5/8), chiHi := (21/32) }

set_option maxRecDepth 1000000 in
private theorem component128Node38_sound : Sound component128Node38Box :=
  sound_of_literal_split component128Node38Box component128Node36Box component128Node37Box
    .k (47/16) (by rfl) (by rfl)
    component128Node36_sound component128Node37_sound

private noncomputable def component128Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (21/32), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component128Node39_sound : Sound component128Node39Box :=
  sound_of_literal_split component128Node39Box leaf6398Box leaf6399Box
    .chi (43/64) (by rfl) (by rfl)
    leaf6398FlatSound leaf6399FlatSound

private noncomputable def component128Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (21/32), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component128Node40_sound : Sound component128Node40Box :=
  sound_of_literal_split component128Node40Box leaf6400Box leaf6401Box
    .chi (43/64) (by rfl) (by rfl)
    leaf6400FlatSound leaf6401FlatSound

private noncomputable def component128Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (21/32), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component128Node41_sound : Sound component128Node41Box :=
  sound_of_literal_split component128Node41Box component128Node39Box component128Node40Box
    .k (47/16) (by rfl) (by rfl)
    component128Node39_sound component128Node40_sound

private noncomputable def component128Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (5/8), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component128Node42_sound : Sound component128Node42Box :=
  sound_of_literal_split component128Node42Box component128Node38Box component128Node41Box
    .chi (21/32) (by rfl) (by rfl)
    component128Node38_sound component128Node41_sound

private noncomputable def component128Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (3), chiLo := (5/8), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component128Node43_sound : Sound component128Node43Box :=
  sound_of_literal_split component128Node43Box component128Node35Box component128Node42Box
    .k (23/8) (by rfl) (by rfl)
    component128Node35_sound component128Node42_sound

private noncomputable def component128Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (11/16), chiHi := (23/32) }

set_option maxRecDepth 1000000 in
private theorem component128Node44_sound : Sound component128Node44Box :=
  sound_of_literal_split component128Node44Box leaf6402Box leaf6403Box
    .chi (45/64) (by rfl) (by rfl)
    leaf6402FlatSound leaf6403FlatSound

private noncomputable def component128Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (11/16), chiHi := (23/32) }

set_option maxRecDepth 1000000 in
private theorem component128Node45_sound : Sound component128Node45Box :=
  sound_of_literal_split component128Node45Box leaf6404Box leaf6405Box
    .chi (45/64) (by rfl) (by rfl)
    leaf6404FlatSound leaf6405FlatSound

private noncomputable def component128Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (11/16), chiHi := (23/32) }

set_option maxRecDepth 1000000 in
private theorem component128Node46_sound : Sound component128Node46Box :=
  sound_of_literal_split component128Node46Box component128Node44Box component128Node45Box
    .k (45/16) (by rfl) (by rfl)
    component128Node44_sound component128Node45_sound

private noncomputable def component128Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (23/32), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component128Node47_sound : Sound component128Node47Box :=
  sound_of_literal_split component128Node47Box leaf6406Box leaf6407Box
    .chi (47/64) (by rfl) (by rfl)
    leaf6406FlatSound leaf6407FlatSound

private noncomputable def component128Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (23/32), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component128Node48_sound : Sound component128Node48Box :=
  sound_of_literal_split component128Node48Box leaf6408Box leaf6409Box
    .chi (47/64) (by rfl) (by rfl)
    leaf6408FlatSound leaf6409FlatSound

private noncomputable def component128Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (23/32), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component128Node49_sound : Sound component128Node49Box :=
  sound_of_literal_split component128Node49Box component128Node47Box component128Node48Box
    .k (45/16) (by rfl) (by rfl)
    component128Node47_sound component128Node48_sound

private noncomputable def component128Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (11/16), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component128Node50_sound : Sound component128Node50Box :=
  sound_of_literal_split component128Node50Box component128Node46Box component128Node49Box
    .chi (23/32) (by rfl) (by rfl)
    component128Node46_sound component128Node49_sound

private noncomputable def component128Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (11/16), chiHi := (23/32) }

set_option maxRecDepth 1000000 in
private theorem component128Node51_sound : Sound component128Node51Box :=
  sound_of_literal_split component128Node51Box leaf6410Box leaf6411Box
    .chi (45/64) (by rfl) (by rfl)
    leaf6410FlatSound leaf6411FlatSound

private noncomputable def component128Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (11/16), chiHi := (23/32) }

set_option maxRecDepth 1000000 in
private theorem component128Node52_sound : Sound component128Node52Box :=
  sound_of_literal_split component128Node52Box leaf6412Box leaf6413Box
    .chi (45/64) (by rfl) (by rfl)
    leaf6412FlatSound leaf6413FlatSound

private noncomputable def component128Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (11/16), chiHi := (23/32) }

set_option maxRecDepth 1000000 in
private theorem component128Node53_sound : Sound component128Node53Box :=
  sound_of_literal_split component128Node53Box component128Node51Box component128Node52Box
    .k (47/16) (by rfl) (by rfl)
    component128Node51_sound component128Node52_sound

private noncomputable def component128Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (23/32), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component128Node54_sound : Sound component128Node54Box :=
  sound_of_literal_split component128Node54Box leaf6414Box leaf6415Box
    .chi (47/64) (by rfl) (by rfl)
    leaf6414FlatSound leaf6415FlatSound

private noncomputable def component128Node55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (23/32), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component128Node55_sound : Sound component128Node55Box :=
  sound_of_literal_split component128Node55Box leaf6416Box leaf6417Box
    .chi (47/64) (by rfl) (by rfl)
    leaf6416FlatSound leaf6417FlatSound

private noncomputable def component128Node56Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (23/32), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component128Node56_sound : Sound component128Node56Box :=
  sound_of_literal_split component128Node56Box component128Node54Box component128Node55Box
    .k (47/16) (by rfl) (by rfl)
    component128Node54_sound component128Node55_sound

private noncomputable def component128Node57Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (11/16), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component128Node57_sound : Sound component128Node57Box :=
  sound_of_literal_split component128Node57Box component128Node53Box component128Node56Box
    .chi (23/32) (by rfl) (by rfl)
    component128Node53_sound component128Node56_sound

private noncomputable def component128Node58Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (3), chiLo := (11/16), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component128Node58_sound : Sound component128Node58Box :=
  sound_of_literal_split component128Node58Box component128Node50Box component128Node57Box
    .k (23/8) (by rfl) (by rfl)
    component128Node50_sound component128Node57_sound

private noncomputable def component128Node59Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (3), chiLo := (5/8), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component128Node59_sound : Sound component128Node59Box :=
  sound_of_literal_split component128Node59Box component128Node43Box component128Node58Box
    .chi (11/16) (by rfl) (by rfl)
    component128Node43_sound component128Node58_sound

noncomputable def component128Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (3), chiLo := (5/8), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
theorem component128_sound : Sound component128Box :=
  sound_of_literal_split component128Box component128Node28Box component128Node59Box
    .k (11/4) (by rfl) (by rfl)
    component128Node28_sound component128Node59_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
