import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch2
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

private noncomputable def leaf3596Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (65/32), chiLo := (1/4), chiHi := (17/64) }

private noncomputable def leaf3596Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217891/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68717213696) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (201289567/134217728) }, upper := { exponent := 0, mantissa := (3153/2048) } }, logOuter := sk71LogOuterCertificate, logK := sk71LogKCertificate, logChi := chi54LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435707391/137434427392) } }, logDArg := sk71LogDArgCertificate }

private noncomputable def leaf3596InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf3596LocalValidity :
    LeafFacts leaf3596Box leaf3596Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3596Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68717213696) }) = true
      norm_num [leaf3596Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3596CertificateValid :
    WideCertificateValid leaf3596Box leaf3596Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk71ValidityFacts chi54ValidityFacts
    leaf3596LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3596CoverageChecked :
    coverageCheck (innerAD leaf3596Box) leaf3596InnerLog = true := by
  rfl'

private theorem leaf3596InnerLogValid :
    leaf3596InnerLog.Valid 8 (innerAD leaf3596Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf3596CoverageChecked

private noncomputable def leaf3596InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629237/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3596InputLogOnePlusV_eq :
    leaf3596InputLogOnePlusV = outerEnclosure 24
      (leaf3596Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3596RoundedFacts : LeafRoundedFacts 8
    leaf3596Certificate.logOnePlusV leaf3596InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3596InputLogOnePlusV_eq }

private noncomputable def leaf3596Inputs : Inputs :=
  inputsOfCaches globalInput sk71RoundedInputs
    chi54InputQChi innerPair35Input
    leaf3596InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3596LowerChecked :
    lowerCheck 24 leaf3596Box leaf3596Inputs = true := by
  rfl'

private theorem leaf3596CoversExact : CoversExact 8
    leaf3596Box leaf3596Certificate leaf3596InnerLog leaf3596Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk71RoundedFacts chi54RoundedFacts
    innerPair35RoundedFacts leaf3596RoundedFacts (by rfl)

private theorem leaf3596FlatSound : Sound leaf3596Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3596CertificateValid
    leaf3596InnerLogValid leaf3596CoversExact leaf3596LowerChecked

private noncomputable def leaf3597Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (65/32), kHi := (33/16), chiLo := (1/4), chiHi := (17/64) }

private noncomputable def leaf3597Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217893/134217728) }, vSqrt := { lower := (65531/65536), upper := (13743698739/13743435776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (202338077/134217728) }, upper := { exponent := 0, mantissa := (1585/1024) } }, logOuter := sk72LogOuterCertificate, logK := sk72LogKCertificate, logChi := chi54LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (27487134515/27486871552) } }, logDArg := sk72LogDArgCertificate }

private noncomputable def leaf3597InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf3597LocalValidity :
    LeafFacts leaf3597Box leaf3597Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3597Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (13743698739/13743435776) }) = true
      norm_num [leaf3597Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3597CertificateValid :
    WideCertificateValid leaf3597Box leaf3597Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk72ValidityFacts chi54ValidityFacts
    leaf3597LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3597CoverageChecked :
    coverageCheck (innerAD leaf3597Box) leaf3597InnerLog = true := by
  rfl'

private theorem leaf3597InnerLogValid :
    leaf3597InnerLog.Valid 8 (innerAD leaf3597Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf3597CoverageChecked

private noncomputable def leaf3597InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629241/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3597InputLogOnePlusV_eq :
    leaf3597InputLogOnePlusV = outerEnclosure 24
      (leaf3597Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3597RoundedFacts : LeafRoundedFacts 8
    leaf3597Certificate.logOnePlusV leaf3597InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3597InputLogOnePlusV_eq }

private noncomputable def leaf3597Inputs : Inputs :=
  inputsOfCaches globalInput sk72RoundedInputs
    chi54InputQChi innerPair40Input
    leaf3597InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3597LowerChecked :
    lowerCheck 24 leaf3597Box leaf3597Inputs = true := by
  rfl'

private theorem leaf3597CoversExact : CoversExact 8
    leaf3597Box leaf3597Certificate leaf3597InnerLog leaf3597Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk72RoundedFacts chi54RoundedFacts
    innerPair40RoundedFacts leaf3597RoundedFacts (by rfl)

private theorem leaf3597FlatSound : Sound leaf3597Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3597CertificateValid
    leaf3597InnerLogValid leaf3597CoversExact leaf3597LowerChecked

private noncomputable def leaf3598Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (65/32), chiLo := (17/64), chiHi := (9/32) }

private noncomputable def leaf3598Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217893/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68717080576) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (205483613/134217728) }, upper := { exponent := 0, mantissa := (1609/1024) } }, logOuter := sk71LogOuterCertificate, logK := sk71LogKCertificate, logChi := chi55LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435574271/137434161152) } }, logDArg := sk71LogDArgCertificate }

private noncomputable def leaf3598InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf3598LocalValidity :
    LeafFacts leaf3598Box leaf3598Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3598Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68717080576) }) = true
      norm_num [leaf3598Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3598CertificateValid :
    WideCertificateValid leaf3598Box leaf3598Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk71ValidityFacts chi55ValidityFacts
    leaf3598LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3598CoverageChecked :
    coverageCheck (innerAD leaf3598Box) leaf3598InnerLog = true := by
  rfl'

private theorem leaf3598InnerLogValid :
    leaf3598InnerLog.Valid 8 (innerAD leaf3598Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf3598CoverageChecked

private noncomputable def leaf3598InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629253/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3598InputLogOnePlusV_eq :
    leaf3598InputLogOnePlusV = outerEnclosure 24
      (leaf3598Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3598RoundedFacts : LeafRoundedFacts 8
    leaf3598Certificate.logOnePlusV leaf3598InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3598InputLogOnePlusV_eq }

private noncomputable def leaf3598Inputs : Inputs :=
  inputsOfCaches globalInput sk71RoundedInputs
    chi55InputQChi innerPair41Input
    leaf3598InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3598LowerChecked :
    lowerCheck 24 leaf3598Box leaf3598Inputs = true := by
  rfl'

private theorem leaf3598CoversExact : CoversExact 8
    leaf3598Box leaf3598Certificate leaf3598InnerLog leaf3598Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk71RoundedFacts chi55RoundedFacts
    innerPair41RoundedFacts leaf3598RoundedFacts (by rfl)

private theorem leaf3598FlatSound : Sound leaf3598Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3598CertificateValid
    leaf3598InnerLogValid leaf3598CoversExact leaf3598LowerChecked

private noncomputable def leaf3599Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (65/32), kHi := (33/16), chiLo := (17/64), chiHi := (9/32) }

private noncomputable def leaf3599Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217895/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68717043712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (206597655/134217728) }, upper := { exponent := 0, mantissa := (809/512) } }, logOuter := sk72LogOuterCertificate, logK := sk72LogKCertificate, logChi := chi55LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435537407/137434087424) } }, logDArg := sk72LogDArgCertificate }

private noncomputable def leaf3599InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf3599LocalValidity :
    LeafFacts leaf3599Box leaf3599Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3599Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68717043712) }) = true
      norm_num [leaf3599Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3599CertificateValid :
    WideCertificateValid leaf3599Box leaf3599Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk72ValidityFacts chi55ValidityFacts
    leaf3599LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3599CoverageChecked :
    coverageCheck (innerAD leaf3599Box) leaf3599InnerLog = true := by
  rfl'

private theorem leaf3599InnerLogValid :
    leaf3599InnerLog.Valid 8 (innerAD leaf3599Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf3599CoverageChecked

private noncomputable def leaf3599InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814629/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3599InputLogOnePlusV_eq :
    leaf3599InputLogOnePlusV = outerEnclosure 24
      (leaf3599Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3599RoundedFacts : LeafRoundedFacts 8
    leaf3599Certificate.logOnePlusV leaf3599InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3599InputLogOnePlusV_eq }

private noncomputable def leaf3599Inputs : Inputs :=
  inputsOfCaches globalInput sk72RoundedInputs
    chi55InputQChi innerPair41Input
    leaf3599InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3599LowerChecked :
    lowerCheck 24 leaf3599Box leaf3599Inputs = true := by
  rfl'

private theorem leaf3599CoversExact : CoversExact 8
    leaf3599Box leaf3599Certificate leaf3599InnerLog leaf3599Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk72RoundedFacts chi55RoundedFacts
    innerPair41RoundedFacts leaf3599RoundedFacts (by rfl)

private theorem leaf3599FlatSound : Sound leaf3599Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3599CertificateValid
    leaf3599InnerLogValid leaf3599CoversExact leaf3599LowerChecked

private noncomputable def leaf3600Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (67/32), chiLo := (1/4), chiHi := (17/64) }

private noncomputable def leaf3600Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217895/134217728) }, vSqrt := { lower := (65531/65536), upper := (22906164565/22905714688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (203386587/134217728) }, upper := { exponent := 0, mantissa := (3187/2048) } }, logOuter := sk73LogOuterCertificate, logK := sk73LogKCertificate, logChi := chi54LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (45811879253/45811429376) } }, logDArg := sk73LogDArgCertificate }

private noncomputable def leaf3600InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf3600LocalValidity :
    LeafFacts leaf3600Box leaf3600Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3600Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (22906164565/22905714688) }) = true
      norm_num [leaf3600Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3600CertificateValid :
    WideCertificateValid leaf3600Box leaf3600Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk73ValidityFacts chi54ValidityFacts
    leaf3600LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3600CoverageChecked :
    coverageCheck (innerAD leaf3600Box) leaf3600InnerLog = true := by
  rfl'

private theorem leaf3600InnerLogValid :
    leaf3600InnerLog.Valid 8 (innerAD leaf3600Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf3600CoverageChecked

private noncomputable def leaf3600InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629245/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3600InputLogOnePlusV_eq :
    leaf3600InputLogOnePlusV = outerEnclosure 24
      (leaf3600Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3600RoundedFacts : LeafRoundedFacts 8
    leaf3600Certificate.logOnePlusV leaf3600InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3600InputLogOnePlusV_eq }

private noncomputable def leaf3600Inputs : Inputs :=
  inputsOfCaches globalInput sk73RoundedInputs
    chi54InputQChi innerPair40Input
    leaf3600InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3600LowerChecked :
    lowerCheck 24 leaf3600Box leaf3600Inputs = true := by
  rfl'

private theorem leaf3600CoversExact : CoversExact 8
    leaf3600Box leaf3600Certificate leaf3600InnerLog leaf3600Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk73RoundedFacts chi54RoundedFacts
    innerPair40RoundedFacts leaf3600RoundedFacts (by rfl)

private theorem leaf3600FlatSound : Sound leaf3600Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3600CertificateValid
    leaf3600InnerLogValid leaf3600CoversExact leaf3600LowerChecked

private noncomputable def leaf3601Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (67/32), kHi := (17/8), chiLo := (1/4), chiHi := (17/64) }

private noncomputable def leaf3601Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217897/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68717109248) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (204435097/134217728) }, upper := { exponent := 0, mantissa := (801/512) } }, logOuter := sk74LogOuterCertificate, logK := sk74LogKCertificate, logChi := chi54LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435602943/137434218496) } }, logDArg := sk74LogDArgCertificate }

private noncomputable def leaf3601InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf3601LocalValidity :
    LeafFacts leaf3601Box leaf3601Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3601Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68717109248) }) = true
      norm_num [leaf3601Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3601CertificateValid :
    WideCertificateValid leaf3601Box leaf3601Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk74ValidityFacts chi54ValidityFacts
    leaf3601LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3601CoverageChecked :
    coverageCheck (innerAD leaf3601Box) leaf3601InnerLog = true := by
  rfl'

private theorem leaf3601InnerLogValid :
    leaf3601InnerLog.Valid 8 (innerAD leaf3601Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf3601CoverageChecked

private noncomputable def leaf3601InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814625/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3601InputLogOnePlusV_eq :
    leaf3601InputLogOnePlusV = outerEnclosure 24
      (leaf3601Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3601RoundedFacts : LeafRoundedFacts 8
    leaf3601Certificate.logOnePlusV leaf3601InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3601InputLogOnePlusV_eq }

private noncomputable def leaf3601Inputs : Inputs :=
  inputsOfCaches globalInput sk74RoundedInputs
    chi54InputQChi innerPair41Input
    leaf3601InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3601LowerChecked :
    lowerCheck 24 leaf3601Box leaf3601Inputs = true := by
  rfl'

private theorem leaf3601CoversExact : CoversExact 8
    leaf3601Box leaf3601Certificate leaf3601InnerLog leaf3601Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk74RoundedFacts chi54RoundedFacts
    innerPair41RoundedFacts leaf3601RoundedFacts (by rfl)

private theorem leaf3601FlatSound : Sound leaf3601Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3601CertificateValid
    leaf3601InnerLogValid leaf3601CoversExact leaf3601LowerChecked

private noncomputable def leaf3602Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (67/32), chiLo := (17/64), chiHi := (9/32) }

private noncomputable def leaf3602Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217897/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68717006848) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (207711697/134217728) }, upper := { exponent := 0, mantissa := (1627/1024) } }, logOuter := sk73LogOuterCertificate, logK := sk73LogKCertificate, logChi := chi55LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435500543/137434013696) } }, logDArg := sk73LogDArgCertificate }

private noncomputable def leaf3602InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf3602LocalValidity :
    LeafFacts leaf3602Box leaf3602Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3602Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68717006848) }) = true
      norm_num [leaf3602Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3602CertificateValid :
    WideCertificateValid leaf3602Box leaf3602Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk73ValidityFacts chi55ValidityFacts
    leaf3602LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3602CoverageChecked :
    coverageCheck (innerAD leaf3602Box) leaf3602InnerLog = true := by
  rfl'

private theorem leaf3602InnerLogValid :
    leaf3602InnerLog.Valid 8 (innerAD leaf3602Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf3602CoverageChecked

private noncomputable def leaf3602InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814631/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3602InputLogOnePlusV_eq :
    leaf3602InputLogOnePlusV = outerEnclosure 24
      (leaf3602Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3602RoundedFacts : LeafRoundedFacts 8
    leaf3602Certificate.logOnePlusV leaf3602InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3602InputLogOnePlusV_eq }

private noncomputable def leaf3602Inputs : Inputs :=
  inputsOfCaches globalInput sk73RoundedInputs
    chi55InputQChi innerPair41Input
    leaf3602InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3602LowerChecked :
    lowerCheck 24 leaf3602Box leaf3602Inputs = true := by
  rfl'

private theorem leaf3602CoversExact : CoversExact 8
    leaf3602Box leaf3602Certificate leaf3602InnerLog leaf3602Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk73RoundedFacts chi55RoundedFacts
    innerPair41RoundedFacts leaf3602RoundedFacts (by rfl)

private theorem leaf3602FlatSound : Sound leaf3602Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3602CertificateValid
    leaf3602InnerLogValid leaf3602CoversExact leaf3602LowerChecked

private noncomputable def leaf3603Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (67/32), kHi := (17/8), chiLo := (17/64), chiHi := (9/32) }

private noncomputable def leaf3603Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217899/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716969984) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (208825739/134217728) }, upper := { exponent := 0, mantissa := (409/256) } }, logOuter := sk74LogOuterCertificate, logK := sk74LogKCertificate, logChi := chi55LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435463679/137433939968) } }, logDArg := sk74LogDArgCertificate }

private noncomputable def leaf3603InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf3603LocalValidity :
    LeafFacts leaf3603Box leaf3603Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3603Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716969984) }) = true
      norm_num [leaf3603Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3603CertificateValid :
    WideCertificateValid leaf3603Box leaf3603Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk74ValidityFacts chi55ValidityFacts
    leaf3603LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3603CoverageChecked :
    coverageCheck (innerAD leaf3603Box) leaf3603InnerLog = true := by
  rfl'

private theorem leaf3603InnerLogValid :
    leaf3603InnerLog.Valid 8 (innerAD leaf3603Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf3603CoverageChecked

private noncomputable def leaf3603InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629267/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3603InputLogOnePlusV_eq :
    leaf3603InputLogOnePlusV = outerEnclosure 24
      (leaf3603Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3603RoundedFacts : LeafRoundedFacts 8
    leaf3603Certificate.logOnePlusV leaf3603InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3603InputLogOnePlusV_eq }

private noncomputable def leaf3603Inputs : Inputs :=
  inputsOfCaches globalInput sk74RoundedInputs
    chi55InputQChi innerPair41Input
    leaf3603InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3603LowerChecked :
    lowerCheck 24 leaf3603Box leaf3603Inputs = true := by
  rfl'

private theorem leaf3603CoversExact : CoversExact 8
    leaf3603Box leaf3603Certificate leaf3603InnerLog leaf3603Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk74RoundedFacts chi55RoundedFacts
    innerPair41RoundedFacts leaf3603RoundedFacts (by rfl)

private theorem leaf3603FlatSound : Sound leaf3603Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3603CertificateValid
    leaf3603InnerLogValid leaf3603CoversExact leaf3603LowerChecked

private noncomputable def leaf3604Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (65/32), chiLo := (9/32), chiHi := (19/64) }

private noncomputable def leaf3604Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217895/134217728) }, vSqrt := { lower := (65531/65536), upper := (22906164565/22905649152) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (209677659/134217728) }, upper := { exponent := 0, mantissa := (3283/2048) } }, logOuter := sk71LogOuterCertificate, logK := sk71LogKCertificate, logChi := chi56LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (45811813717/45811298304) } }, logDArg := sk71LogDArgCertificate }

private noncomputable def leaf3604InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf3604LocalValidity :
    LeafFacts leaf3604Box leaf3604Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3604Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (22906164565/22905649152) }) = true
      norm_num [leaf3604Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3604CertificateValid :
    WideCertificateValid leaf3604Box leaf3604Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk71ValidityFacts chi56ValidityFacts
    leaf3604LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3604CoverageChecked :
    coverageCheck (innerAD leaf3604Box) leaf3604InnerLog = true := by
  rfl'

private theorem leaf3604InnerLogValid :
    leaf3604InnerLog.Valid 8 (innerAD leaf3604Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf3604CoverageChecked

private noncomputable def leaf3604InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629269/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3604InputLogOnePlusV_eq :
    leaf3604InputLogOnePlusV = outerEnclosure 24
      (leaf3604Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3604RoundedFacts : LeafRoundedFacts 8
    leaf3604Certificate.logOnePlusV leaf3604InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3604InputLogOnePlusV_eq }

private noncomputable def leaf3604Inputs : Inputs :=
  inputsOfCaches globalInput sk71RoundedInputs
    chi56InputQChi innerPair41Input
    leaf3604InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3604LowerChecked :
    lowerCheck 24 leaf3604Box leaf3604Inputs = true := by
  rfl'

private theorem leaf3604CoversExact : CoversExact 8
    leaf3604Box leaf3604Certificate leaf3604InnerLog leaf3604Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk71RoundedFacts chi56RoundedFacts
    innerPair41RoundedFacts leaf3604RoundedFacts (by rfl)

private theorem leaf3604FlatSound : Sound leaf3604Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3604CertificateValid
    leaf3604InnerLogValid leaf3604CoversExact leaf3604LowerChecked

private noncomputable def leaf3605Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (65/32), kHi := (33/16), chiLo := (9/32), chiHi := (19/64) }

private noncomputable def leaf3605Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217897/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716908544) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (210857233/134217728) }, upper := { exponent := 0, mantissa := (1651/1024) } }, logOuter := sk72LogOuterCertificate, logK := sk72LogKCertificate, logChi := chi56LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435402239/137433817088) } }, logDArg := sk72LogDArgCertificate }

private noncomputable def leaf3605InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf3605LocalValidity :
    LeafFacts leaf3605Box leaf3605Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3605Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716908544) }) = true
      norm_num [leaf3605Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3605CertificateValid :
    WideCertificateValid leaf3605Box leaf3605Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk72ValidityFacts chi56ValidityFacts
    leaf3605LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3605CoverageChecked :
    coverageCheck (innerAD leaf3605Box) leaf3605InnerLog = true := by
  rfl'

private theorem leaf3605InnerLogValid :
    leaf3605InnerLog.Valid 8 (innerAD leaf3605Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf3605CoverageChecked

private noncomputable def leaf3605InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814637/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3605InputLogOnePlusV_eq :
    leaf3605InputLogOnePlusV = outerEnclosure 24
      (leaf3605Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3605RoundedFacts : LeafRoundedFacts 8
    leaf3605Certificate.logOnePlusV leaf3605InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3605InputLogOnePlusV_eq }

private noncomputable def leaf3605Inputs : Inputs :=
  inputsOfCaches globalInput sk72RoundedInputs
    chi56InputQChi innerPair50Input
    leaf3605InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3605LowerChecked :
    lowerCheck 24 leaf3605Box leaf3605Inputs = true := by
  rfl'

private theorem leaf3605CoversExact : CoversExact 8
    leaf3605Box leaf3605Certificate leaf3605InnerLog leaf3605Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk72RoundedFacts chi56RoundedFacts
    innerPair50RoundedFacts leaf3605RoundedFacts (by rfl)

private theorem leaf3605FlatSound : Sound leaf3605Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3605CertificateValid
    leaf3605InnerLogValid leaf3605CoversExact leaf3605LowerChecked

private noncomputable def leaf3606Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (65/32), chiLo := (19/64), chiHi := (5/16) }

private noncomputable def leaf3606Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217897/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716814336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (213871705/134217728) }, upper := { exponent := 0, mantissa := (837/512) } }, logOuter := sk71LogOuterCertificate, logK := sk71LogKCertificate, logChi := chi57LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435308031/137433628672) } }, logDArg := sk71LogDArgCertificate }

private noncomputable def leaf3606InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf3606LocalValidity :
    LeafFacts leaf3606Box leaf3606Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3606Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716814336) }) = true
      norm_num [leaf3606Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3606CertificateValid :
    WideCertificateValid leaf3606Box leaf3606Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk71ValidityFacts chi57ValidityFacts
    leaf3606LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3606CoverageChecked :
    coverageCheck (innerAD leaf3606Box) leaf3606InnerLog = true := by
  rfl'

private theorem leaf3606InnerLogValid :
    leaf3606InnerLog.Valid 8 (innerAD leaf3606Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf3606CoverageChecked

private noncomputable def leaf3606InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814643/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3606InputLogOnePlusV_eq :
    leaf3606InputLogOnePlusV = outerEnclosure 24
      (leaf3606Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3606RoundedFacts : LeafRoundedFacts 8
    leaf3606Certificate.logOnePlusV leaf3606InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3606InputLogOnePlusV_eq }

private noncomputable def leaf3606Inputs : Inputs :=
  inputsOfCaches globalInput sk71RoundedInputs
    chi57InputQChi innerPair51Input
    leaf3606InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3606LowerChecked :
    lowerCheck 24 leaf3606Box leaf3606Inputs = true := by
  rfl'

private theorem leaf3606CoversExact : CoversExact 8
    leaf3606Box leaf3606Certificate leaf3606InnerLog leaf3606Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk71RoundedFacts chi57RoundedFacts
    innerPair51RoundedFacts leaf3606RoundedFacts (by rfl)

private theorem leaf3606FlatSound : Sound leaf3606Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3606CertificateValid
    leaf3606InnerLogValid leaf3606CoversExact leaf3606LowerChecked

private noncomputable def leaf3607Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (65/32), kHi := (33/16), chiLo := (19/64), chiHi := (5/16) }

private noncomputable def leaf3607Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217899/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716773376) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (215116811/134217728) }, upper := { exponent := 0, mantissa := (421/256) } }, logOuter := sk72LogOuterCertificate, logK := sk72LogKCertificate, logChi := chi57LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435267071/137433546752) } }, logDArg := sk72LogDArgCertificate }

private noncomputable def leaf3607InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf3607LocalValidity :
    LeafFacts leaf3607Box leaf3607Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3607Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716773376) }) = true
      norm_num [leaf3607Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3607CertificateValid :
    WideCertificateValid leaf3607Box leaf3607Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk72ValidityFacts chi57ValidityFacts
    leaf3607LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3607CoverageChecked :
    coverageCheck (innerAD leaf3607Box) leaf3607InnerLog = true := by
  rfl'

private theorem leaf3607InnerLogValid :
    leaf3607InnerLog.Valid 8 (innerAD leaf3607Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf3607CoverageChecked

private noncomputable def leaf3607InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629291/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3607InputLogOnePlusV_eq :
    leaf3607InputLogOnePlusV = outerEnclosure 24
      (leaf3607Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3607RoundedFacts : LeafRoundedFacts 8
    leaf3607Certificate.logOnePlusV leaf3607InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3607InputLogOnePlusV_eq }

private noncomputable def leaf3607Inputs : Inputs :=
  inputsOfCaches globalInput sk72RoundedInputs
    chi57InputQChi innerPair51Input
    leaf3607InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3607LowerChecked :
    lowerCheck 24 leaf3607Box leaf3607Inputs = true := by
  rfl'

private theorem leaf3607CoversExact : CoversExact 8
    leaf3607Box leaf3607Certificate leaf3607InnerLog leaf3607Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk72RoundedFacts chi57RoundedFacts
    innerPair51RoundedFacts leaf3607RoundedFacts (by rfl)

private theorem leaf3607FlatSound : Sound leaf3607Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3607CertificateValid
    leaf3607InnerLogValid leaf3607CoversExact leaf3607LowerChecked

private noncomputable def leaf3608Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (67/32), chiLo := (9/32), chiHi := (19/64) }

private noncomputable def leaf3608Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217899/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716869632) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (212036807/134217728) }, upper := { exponent := 0, mantissa := (3321/2048) } }, logOuter := sk73LogOuterCertificate, logK := sk73LogKCertificate, logChi := chi56LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435363327/137433739264) } }, logDArg := sk73LogDArgCertificate }

private noncomputable def leaf3608InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf3608LocalValidity :
    LeafFacts leaf3608Box leaf3608Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3608Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716869632) }) = true
      norm_num [leaf3608Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3608CertificateValid :
    WideCertificateValid leaf3608Box leaf3608Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk73ValidityFacts chi56ValidityFacts
    leaf3608LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3608CoverageChecked :
    coverageCheck (innerAD leaf3608Box) leaf3608InnerLog = true := by
  rfl'

private theorem leaf3608InnerLogValid :
    leaf3608InnerLog.Valid 8 (innerAD leaf3608Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf3608CoverageChecked

private noncomputable def leaf3608InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629279/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3608InputLogOnePlusV_eq :
    leaf3608InputLogOnePlusV = outerEnclosure 24
      (leaf3608Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3608RoundedFacts : LeafRoundedFacts 8
    leaf3608Certificate.logOnePlusV leaf3608InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3608InputLogOnePlusV_eq }

private noncomputable def leaf3608Inputs : Inputs :=
  inputsOfCaches globalInput sk73RoundedInputs
    chi56InputQChi innerPair50Input
    leaf3608InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3608LowerChecked :
    lowerCheck 24 leaf3608Box leaf3608Inputs = true := by
  rfl'

private theorem leaf3608CoversExact : CoversExact 8
    leaf3608Box leaf3608Certificate leaf3608InnerLog leaf3608Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk73RoundedFacts chi56RoundedFacts
    innerPair50RoundedFacts leaf3608RoundedFacts (by rfl)

private theorem leaf3608FlatSound : Sound leaf3608Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3608CertificateValid
    leaf3608InnerLogValid leaf3608CoversExact leaf3608LowerChecked

private noncomputable def leaf3609Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (67/32), kHi := (17/8), chiLo := (9/32), chiHi := (19/64) }

private noncomputable def leaf3609Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217901/134217728) }, vSqrt := { lower := (65531/65536), upper := (4581232913/4581122048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (213216381/134217728) }, upper := { exponent := 0, mantissa := (835/512) } }, logOuter := sk74LogOuterCertificate, logK := sk74LogKCertificate, logChi := chi56LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (9162354961/9162244096) } }, logDArg := sk74LogDArgCertificate }

private noncomputable def leaf3609InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf3609LocalValidity :
    LeafFacts leaf3609Box leaf3609Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3609Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (4581232913/4581122048) }) = true
      norm_num [leaf3609Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3609CertificateValid :
    WideCertificateValid leaf3609Box leaf3609Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk74ValidityFacts chi56ValidityFacts
    leaf3609LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3609CoverageChecked :
    coverageCheck (innerAD leaf3609Box) leaf3609InnerLog = true := by
  rfl'

private theorem leaf3609InnerLogValid :
    leaf3609InnerLog.Valid 8 (innerAD leaf3609Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf3609CoverageChecked

private noncomputable def leaf3609InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907321/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3609InputLogOnePlusV_eq :
    leaf3609InputLogOnePlusV = outerEnclosure 24
      (leaf3609Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3609RoundedFacts : LeafRoundedFacts 8
    leaf3609Certificate.logOnePlusV leaf3609InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3609InputLogOnePlusV_eq }

private noncomputable def leaf3609Inputs : Inputs :=
  inputsOfCaches globalInput sk74RoundedInputs
    chi56InputQChi innerPair51Input
    leaf3609InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3609LowerChecked :
    lowerCheck 24 leaf3609Box leaf3609Inputs = true := by
  rfl'

private theorem leaf3609CoversExact : CoversExact 8
    leaf3609Box leaf3609Certificate leaf3609InnerLog leaf3609Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk74RoundedFacts chi56RoundedFacts
    innerPair51RoundedFacts leaf3609RoundedFacts (by rfl)

private theorem leaf3609FlatSound : Sound leaf3609Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3609CertificateValid
    leaf3609InnerLogValid leaf3609CoversExact leaf3609LowerChecked

private noncomputable def leaf3610Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (67/32), chiLo := (19/64), chiHi := (5/16) }

private noncomputable def leaf3610Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217901/134217728) }, vSqrt := { lower := (65531/65536), upper := (22906164565/22905577472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (216361917/134217728) }, upper := { exponent := 0, mantissa := (847/512) } }, logOuter := sk73LogOuterCertificate, logK := sk73LogKCertificate, logChi := chi57LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (45811742037/45811154944) } }, logDArg := sk73LogDArgCertificate }

private noncomputable def leaf3610InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf3610LocalValidity :
    LeafFacts leaf3610Box leaf3610Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3610Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (22906164565/22905577472) }) = true
      norm_num [leaf3610Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3610CertificateValid :
    WideCertificateValid leaf3610Box leaf3610Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk73ValidityFacts chi57ValidityFacts
    leaf3610LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3610CoverageChecked :
    coverageCheck (innerAD leaf3610Box) leaf3610InnerLog = true := by
  rfl'

private theorem leaf3610InnerLogValid :
    leaf3610InnerLog.Valid 8 (innerAD leaf3610Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf3610CoverageChecked

private noncomputable def leaf3610InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (726831/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf3610InputLogOnePlusV_eq :
    leaf3610InputLogOnePlusV = outerEnclosure 24
      (leaf3610Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3610RoundedFacts : LeafRoundedFacts 8
    leaf3610Certificate.logOnePlusV leaf3610InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3610InputLogOnePlusV_eq }

private noncomputable def leaf3610Inputs : Inputs :=
  inputsOfCaches globalInput sk73RoundedInputs
    chi57InputQChi innerPair51Input
    leaf3610InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3610LowerChecked :
    lowerCheck 24 leaf3610Box leaf3610Inputs = true := by
  rfl'

private theorem leaf3610CoversExact : CoversExact 8
    leaf3610Box leaf3610Certificate leaf3610InnerLog leaf3610Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk73RoundedFacts chi57RoundedFacts
    innerPair51RoundedFacts leaf3610RoundedFacts (by rfl)

private theorem leaf3610FlatSound : Sound leaf3610Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3610CertificateValid
    leaf3610InnerLogValid leaf3610CoversExact leaf3610LowerChecked

private noncomputable def leaf3611Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (67/32), kHi := (17/8), chiLo := (19/64), chiHi := (5/16) }

private noncomputable def leaf3611Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217903/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716691456) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (217607023/134217728) }, upper := { exponent := 0, mantissa := (213/128) } }, logOuter := sk74LogOuterCertificate, logK := sk74LogKCertificate, logChi := chi57LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435185151/137433382912) } }, logDArg := sk74LogDArgCertificate }

private noncomputable def leaf3611InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf3611LocalValidity :
    LeafFacts leaf3611Box leaf3611Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3611Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716691456) }) = true
      norm_num [leaf3611Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3611CertificateValid :
    WideCertificateValid leaf3611Box leaf3611Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk74ValidityFacts chi57ValidityFacts
    leaf3611LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3611CoverageChecked :
    coverageCheck (innerAD leaf3611Box) leaf3611InnerLog = true := by
  rfl'

private theorem leaf3611InnerLogValid :
    leaf3611InnerLog.Valid 8 (innerAD leaf3611Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf3611CoverageChecked

private noncomputable def leaf3611InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629301/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3611InputLogOnePlusV_eq :
    leaf3611InputLogOnePlusV = outerEnclosure 24
      (leaf3611Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3611RoundedFacts : LeafRoundedFacts 8
    leaf3611Certificate.logOnePlusV leaf3611InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3611InputLogOnePlusV_eq }

private noncomputable def leaf3611Inputs : Inputs :=
  inputsOfCaches globalInput sk74RoundedInputs
    chi57InputQChi innerPair51Input
    leaf3611InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3611LowerChecked :
    lowerCheck 24 leaf3611Box leaf3611Inputs = true := by
  rfl'

private theorem leaf3611CoversExact : CoversExact 8
    leaf3611Box leaf3611Certificate leaf3611InnerLog leaf3611Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk74RoundedFacts chi57RoundedFacts
    innerPair51RoundedFacts leaf3611RoundedFacts (by rfl)

private theorem leaf3611FlatSound : Sound leaf3611Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3611CertificateValid
    leaf3611InnerLogValid leaf3611CoversExact leaf3611LowerChecked

private noncomputable def leaf3612Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (69/32), chiLo := (1/4), chiHi := (17/64) }

private noncomputable def leaf3612Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217899/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68717074432) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (205483607/134217728) }, upper := { exponent := 0, mantissa := (3221/2048) } }, logOuter := sk75LogOuterCertificate, logK := sk75LogKCertificate, logChi := chi54LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435568127/137434148864) } }, logDArg := sk75LogDArgCertificate }

private noncomputable def leaf3612InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf3612LocalValidity :
    LeafFacts leaf3612Box leaf3612Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3612Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68717074432) }) = true
      norm_num [leaf3612Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3612CertificateValid :
    WideCertificateValid leaf3612Box leaf3612Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk75ValidityFacts chi54ValidityFacts
    leaf3612LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3612CoverageChecked :
    coverageCheck (innerAD leaf3612Box) leaf3612InnerLog = true := by
  rfl'

private theorem leaf3612InnerLogValid :
    leaf3612InnerLog.Valid 8 (innerAD leaf3612Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf3612CoverageChecked

private noncomputable def leaf3612InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814627/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3612InputLogOnePlusV_eq :
    leaf3612InputLogOnePlusV = outerEnclosure 24
      (leaf3612Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3612RoundedFacts : LeafRoundedFacts 8
    leaf3612Certificate.logOnePlusV leaf3612InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3612InputLogOnePlusV_eq }

private noncomputable def leaf3612Inputs : Inputs :=
  inputsOfCaches globalInput sk75RoundedInputs
    chi54InputQChi innerPair41Input
    leaf3612InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3612LowerChecked :
    lowerCheck 24 leaf3612Box leaf3612Inputs = true := by
  rfl'

private theorem leaf3612CoversExact : CoversExact 8
    leaf3612Box leaf3612Certificate leaf3612InnerLog leaf3612Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk75RoundedFacts chi54RoundedFacts
    innerPair41RoundedFacts leaf3612RoundedFacts (by rfl)

private theorem leaf3612FlatSound : Sound leaf3612Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3612CertificateValid
    leaf3612InnerLogValid leaf3612CoversExact leaf3612LowerChecked

private noncomputable def leaf3613Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (69/32), kHi := (35/16), chiLo := (1/4), chiHi := (17/64) }

private noncomputable def leaf3613Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217901/134217728) }, vSqrt := { lower := (65531/65536), upper := (22906164565/22905679872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (206532117/134217728) }, upper := { exponent := 0, mantissa := (1619/1024) } }, logOuter := sk76LogOuterCertificate, logK := sk76LogKCertificate, logChi := chi54LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (45811844437/45811359744) } }, logDArg := sk76LogDArgCertificate }

private noncomputable def leaf3613InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf3613LocalValidity :
    LeafFacts leaf3613Box leaf3613Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3613Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (22906164565/22905679872) }) = true
      norm_num [leaf3613Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3613CertificateValid :
    WideCertificateValid leaf3613Box leaf3613Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk76ValidityFacts chi54ValidityFacts
    leaf3613LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3613CoverageChecked :
    coverageCheck (innerAD leaf3613Box) leaf3613InnerLog = true := by
  rfl'

private theorem leaf3613InnerLogValid :
    leaf3613InnerLog.Valid 8 (innerAD leaf3613Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf3613CoverageChecked

private noncomputable def leaf3613InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814629/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3613InputLogOnePlusV_eq :
    leaf3613InputLogOnePlusV = outerEnclosure 24
      (leaf3613Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3613RoundedFacts : LeafRoundedFacts 8
    leaf3613Certificate.logOnePlusV leaf3613InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3613InputLogOnePlusV_eq }

private noncomputable def leaf3613Inputs : Inputs :=
  inputsOfCaches globalInput sk76RoundedInputs
    chi54InputQChi innerPair41Input
    leaf3613InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3613LowerChecked :
    lowerCheck 24 leaf3613Box leaf3613Inputs = true := by
  rfl'

private theorem leaf3613CoversExact : CoversExact 8
    leaf3613Box leaf3613Certificate leaf3613InnerLog leaf3613Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk76RoundedFacts chi54RoundedFacts
    innerPair41RoundedFacts leaf3613RoundedFacts (by rfl)

private theorem leaf3613FlatSound : Sound leaf3613Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3613CertificateValid
    leaf3613InnerLogValid leaf3613CoversExact leaf3613LowerChecked

private noncomputable def leaf3614Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (69/32), chiLo := (17/64), chiHi := (9/32) }

private noncomputable def leaf3614Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217901/134217728) }, vSqrt := { lower := (65531/65536), upper := (13743698739/13743386624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (209939781/134217728) }, upper := { exponent := 0, mantissa := (1645/1024) } }, logOuter := sk75LogOuterCertificate, logK := sk75LogKCertificate, logChi := chi55LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (27487085363/27486773248) } }, logDArg := sk75LogDArgCertificate }

private noncomputable def leaf3614InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf3614LocalValidity :
    LeafFacts leaf3614Box leaf3614Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3614Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (13743698739/13743386624) }) = true
      norm_num [leaf3614Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3614CertificateValid :
    WideCertificateValid leaf3614Box leaf3614Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk75ValidityFacts chi55ValidityFacts
    leaf3614LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3614CoverageChecked :
    coverageCheck (innerAD leaf3614Box) leaf3614InnerLog = true := by
  rfl'

private theorem leaf3614InnerLogValid :
    leaf3614InnerLog.Valid 8 (innerAD leaf3614Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf3614CoverageChecked

private noncomputable def leaf3614InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629271/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3614InputLogOnePlusV_eq :
    leaf3614InputLogOnePlusV = outerEnclosure 24
      (leaf3614Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3614RoundedFacts : LeafRoundedFacts 8
    leaf3614Certificate.logOnePlusV leaf3614InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3614InputLogOnePlusV_eq }

private noncomputable def leaf3614Inputs : Inputs :=
  inputsOfCaches globalInput sk75RoundedInputs
    chi55InputQChi innerPair50Input
    leaf3614InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3614LowerChecked :
    lowerCheck 24 leaf3614Box leaf3614Inputs = true := by
  rfl'

private theorem leaf3614CoversExact : CoversExact 8
    leaf3614Box leaf3614Certificate leaf3614InnerLog leaf3614Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk75RoundedFacts chi55RoundedFacts
    innerPair50RoundedFacts leaf3614RoundedFacts (by rfl)

private theorem leaf3614FlatSound : Sound leaf3614Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3614CertificateValid
    leaf3614InnerLogValid leaf3614CoversExact leaf3614LowerChecked

private noncomputable def leaf3615Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (69/32), kHi := (35/16), chiLo := (17/64), chiHi := (9/32) }

private noncomputable def leaf3615Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217903/134217728) }, vSqrt := { lower := (65531/65536), upper := (4042264335/4042170368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (211053823/134217728) }, upper := { exponent := 0, mantissa := (827/512) } }, logOuter := sk76LogOuterCertificate, logK := sk76LogKCertificate, logChi := chi55LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (8084434703/8084340736) } }, logDArg := sk76LogDArgCertificate }

private noncomputable def leaf3615InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf3615LocalValidity :
    LeafFacts leaf3615Box leaf3615Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3615Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (4042264335/4042170368) }) = true
      norm_num [leaf3615Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3615CertificateValid :
    WideCertificateValid leaf3615Box leaf3615Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk76ValidityFacts chi55ValidityFacts
    leaf3615LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3615CoverageChecked :
    coverageCheck (innerAD leaf3615Box) leaf3615InnerLog = true := by
  rfl'

private theorem leaf3615InnerLogValid :
    leaf3615InnerLog.Valid 8 (innerAD leaf3615Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf3615CoverageChecked

private noncomputable def leaf3615InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907319/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3615InputLogOnePlusV_eq :
    leaf3615InputLogOnePlusV = outerEnclosure 24
      (leaf3615Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3615RoundedFacts : LeafRoundedFacts 8
    leaf3615Certificate.logOnePlusV leaf3615InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3615InputLogOnePlusV_eq }

private noncomputable def leaf3615Inputs : Inputs :=
  inputsOfCaches globalInput sk76RoundedInputs
    chi55InputQChi innerPair50Input
    leaf3615InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3615LowerChecked :
    lowerCheck 24 leaf3615Box leaf3615Inputs = true := by
  rfl'

private theorem leaf3615CoversExact : CoversExact 8
    leaf3615Box leaf3615Certificate leaf3615InnerLog leaf3615Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk76RoundedFacts chi55RoundedFacts
    innerPair50RoundedFacts leaf3615RoundedFacts (by rfl)

private theorem leaf3615FlatSound : Sound leaf3615Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3615CertificateValid
    leaf3615InnerLogValid leaf3615CoversExact leaf3615LowerChecked

private noncomputable def leaf3616Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (71/32), chiLo := (1/4), chiHi := (17/64) }

private noncomputable def leaf3616Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217903/134217728) }, vSqrt := { lower := (65531/65536), upper := (13743698739/13743400960) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (207580627/134217728) }, upper := { exponent := 0, mantissa := (3255/2048) } }, logOuter := sk77LogOuterCertificate, logK := sk77LogKCertificate, logChi := chi54LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (27487099699/27486801920) } }, logDArg := sk77LogDArgCertificate }

private noncomputable def leaf3616InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf3616LocalValidity :
    LeafFacts leaf3616Box leaf3616Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3616Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (13743698739/13743400960) }) = true
      norm_num [leaf3616Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3616CertificateValid :
    WideCertificateValid leaf3616Box leaf3616Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk77ValidityFacts chi54ValidityFacts
    leaf3616LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3616CoverageChecked :
    coverageCheck (innerAD leaf3616Box) leaf3616InnerLog = true := by
  rfl'

private theorem leaf3616InnerLogValid :
    leaf3616InnerLog.Valid 8 (innerAD leaf3616Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf3616CoverageChecked

private noncomputable def leaf3616InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814631/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3616InputLogOnePlusV_eq :
    leaf3616InputLogOnePlusV = outerEnclosure 24
      (leaf3616Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3616RoundedFacts : LeafRoundedFacts 8
    leaf3616Certificate.logOnePlusV leaf3616InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3616InputLogOnePlusV_eq }

private noncomputable def leaf3616Inputs : Inputs :=
  inputsOfCaches globalInput sk77RoundedInputs
    chi54InputQChi innerPair41Input
    leaf3616InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3616LowerChecked :
    lowerCheck 24 leaf3616Box leaf3616Inputs = true := by
  rfl'

private theorem leaf3616CoversExact : CoversExact 8
    leaf3616Box leaf3616Certificate leaf3616InnerLog leaf3616Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk77RoundedFacts chi54RoundedFacts
    innerPair41RoundedFacts leaf3616RoundedFacts (by rfl)

private theorem leaf3616FlatSound : Sound leaf3616Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3616CertificateValid
    leaf3616InnerLogValid leaf3616CoversExact leaf3616LowerChecked

private noncomputable def leaf3617Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (71/32), kHi := (9/4), chiLo := (1/4), chiHi := (17/64) }

private noncomputable def leaf3617Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217905/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716969984) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (208629137/134217728) }, upper := { exponent := 0, mantissa := (409/256) } }, logOuter := sk78LogOuterCertificate, logK := sk78LogKCertificate, logChi := chi54LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435463679/137433939968) } }, logDArg := sk78LogDArgCertificate }

private noncomputable def leaf3617InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf3617LocalValidity :
    LeafFacts leaf3617Box leaf3617Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3617Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716969984) }) = true
      norm_num [leaf3617Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3617CertificateValid :
    WideCertificateValid leaf3617Box leaf3617Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk78ValidityFacts chi54ValidityFacts
    leaf3617LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3617CoverageChecked :
    coverageCheck (innerAD leaf3617Box) leaf3617InnerLog = true := by
  rfl'

private theorem leaf3617InnerLogValid :
    leaf3617InnerLog.Valid 8 (innerAD leaf3617Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf3617CoverageChecked

private noncomputable def leaf3617InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629267/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3617InputLogOnePlusV_eq :
    leaf3617InputLogOnePlusV = outerEnclosure 24
      (leaf3617Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3617RoundedFacts : LeafRoundedFacts 8
    leaf3617Certificate.logOnePlusV leaf3617InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3617InputLogOnePlusV_eq }

private noncomputable def leaf3617Inputs : Inputs :=
  inputsOfCaches globalInput sk78RoundedInputs
    chi54InputQChi innerPair41Input
    leaf3617InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3617LowerChecked :
    lowerCheck 24 leaf3617Box leaf3617Inputs = true := by
  rfl'

private theorem leaf3617CoversExact : CoversExact 8
    leaf3617Box leaf3617Certificate leaf3617InnerLog leaf3617Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk78RoundedFacts chi54RoundedFacts
    innerPair41RoundedFacts leaf3617RoundedFacts (by rfl)

private theorem leaf3617FlatSound : Sound leaf3617Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3617CertificateValid
    leaf3617InnerLogValid leaf3617CoversExact leaf3617LowerChecked

private noncomputable def leaf3618Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (71/32), chiLo := (17/64), chiHi := (9/32) }

private noncomputable def leaf3618Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217905/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716859392) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (212167865/134217728) }, upper := { exponent := 0, mantissa := (1663/1024) } }, logOuter := sk77LogOuterCertificate, logK := sk77LogKCertificate, logChi := chi55LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435353087/137433718784) } }, logDArg := sk77LogDArgCertificate }

private noncomputable def leaf3618InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf3618LocalValidity :
    LeafFacts leaf3618Box leaf3618Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3618Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716859392) }) = true
      norm_num [leaf3618Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3618CertificateValid :
    WideCertificateValid leaf3618Box leaf3618Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk77ValidityFacts chi55ValidityFacts
    leaf3618LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3618CoverageChecked :
    coverageCheck (innerAD leaf3618Box) leaf3618InnerLog = true := by
  rfl'

private theorem leaf3618InnerLogValid :
    leaf3618InnerLog.Valid 8 (innerAD leaf3618Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf3618CoverageChecked

private noncomputable def leaf3618InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (363415/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf3618InputLogOnePlusV_eq :
    leaf3618InputLogOnePlusV = outerEnclosure 24
      (leaf3618Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3618RoundedFacts : LeafRoundedFacts 8
    leaf3618Certificate.logOnePlusV leaf3618InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3618InputLogOnePlusV_eq }

private noncomputable def leaf3618Inputs : Inputs :=
  inputsOfCaches globalInput sk77RoundedInputs
    chi55InputQChi innerPair50Input
    leaf3618InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3618LowerChecked :
    lowerCheck 24 leaf3618Box leaf3618Inputs = true := by
  rfl'

private theorem leaf3618CoversExact : CoversExact 8
    leaf3618Box leaf3618Certificate leaf3618InnerLog leaf3618Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk77RoundedFacts chi55RoundedFacts
    innerPair50RoundedFacts leaf3618RoundedFacts (by rfl)

private theorem leaf3618FlatSound : Sound leaf3618Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3618CertificateValid
    leaf3618InnerLogValid leaf3618CoversExact leaf3618LowerChecked

private noncomputable def leaf3619Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (71/32), kHi := (9/4), chiLo := (17/64), chiHi := (9/32) }

private noncomputable def leaf3619Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217907/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716822528) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (213281907/134217728) }, upper := { exponent := 0, mantissa := (209/128) } }, logOuter := sk78LogOuterCertificate, logK := sk78LogKCertificate, logChi := chi55LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435316223/137433645056) } }, logDArg := sk78LogDArgCertificate }

private noncomputable def leaf3619InnerLog : WideLogData :=
  innerPair170Data

set_option maxRecDepth 1000000 in
private theorem leaf3619LocalValidity :
    LeafFacts leaf3619Box leaf3619Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3619Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716822528) }) = true
      norm_num [leaf3619Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3619CertificateValid :
    WideCertificateValid leaf3619Box leaf3619Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk78ValidityFacts chi55ValidityFacts
    leaf3619LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3619CoverageChecked :
    coverageCheck (innerAD leaf3619Box) leaf3619InnerLog = true := by
  rfl'

private theorem leaf3619InnerLogValid :
    leaf3619InnerLog.Valid 8 (innerAD leaf3619Box) :=
  wideLogDataValid_of_cachedCheck endpoint47PositiveFacts
    endpoint45PositiveFacts.valid leaf3619CoverageChecked

private noncomputable def leaf3619InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629285/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3619InputLogOnePlusV_eq :
    leaf3619InputLogOnePlusV = outerEnclosure 24
      (leaf3619Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3619RoundedFacts : LeafRoundedFacts 8
    leaf3619Certificate.logOnePlusV leaf3619InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3619InputLogOnePlusV_eq }

private noncomputable def leaf3619Inputs : Inputs :=
  inputsOfCaches globalInput sk78RoundedInputs
    chi55InputQChi innerPair170Input
    leaf3619InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3619LowerChecked :
    lowerCheck 24 leaf3619Box leaf3619Inputs = true := by
  rfl'

private theorem leaf3619CoversExact : CoversExact 8
    leaf3619Box leaf3619Certificate leaf3619InnerLog leaf3619Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk78RoundedFacts chi55RoundedFacts
    innerPair170RoundedFacts leaf3619RoundedFacts (by rfl)

private theorem leaf3619FlatSound : Sound leaf3619Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3619CertificateValid
    leaf3619InnerLogValid leaf3619CoversExact leaf3619LowerChecked

private noncomputable def leaf3620Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (69/32), chiLo := (9/32), chiHi := (19/64) }

private noncomputable def leaf3620Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217903/134217728) }, vSqrt := { lower := (65531/65536), upper := (4042264335/4042164224) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (214395955/134217728) }, upper := { exponent := 0, mantissa := (3359/2048) } }, logOuter := sk75LogOuterCertificate, logK := sk75LogKCertificate, logChi := chi56LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (8084428559/8084328448) } }, logDArg := sk75LogDArgCertificate }

private noncomputable def leaf3620InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf3620LocalValidity :
    LeafFacts leaf3620Box leaf3620Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3620Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (4042264335/4042164224) }) = true
      norm_num [leaf3620Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3620CertificateValid :
    WideCertificateValid leaf3620Box leaf3620Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk75ValidityFacts chi56ValidityFacts
    leaf3620LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3620CoverageChecked :
    coverageCheck (innerAD leaf3620Box) leaf3620InnerLog = true := by
  rfl'

private theorem leaf3620InnerLogValid :
    leaf3620InnerLog.Valid 8 (innerAD leaf3620Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf3620CoverageChecked

private noncomputable def leaf3620InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629289/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3620InputLogOnePlusV_eq :
    leaf3620InputLogOnePlusV = outerEnclosure 24
      (leaf3620Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3620RoundedFacts : LeafRoundedFacts 8
    leaf3620Certificate.logOnePlusV leaf3620InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3620InputLogOnePlusV_eq }

private noncomputable def leaf3620Inputs : Inputs :=
  inputsOfCaches globalInput sk75RoundedInputs
    chi56InputQChi innerPair51Input
    leaf3620InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3620LowerChecked :
    lowerCheck 24 leaf3620Box leaf3620Inputs = true := by
  rfl'

private theorem leaf3620CoversExact : CoversExact 8
    leaf3620Box leaf3620Certificate leaf3620InnerLog leaf3620Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk75RoundedFacts chi56RoundedFacts
    innerPair51RoundedFacts leaf3620RoundedFacts (by rfl)

private theorem leaf3620FlatSound : Sound leaf3620Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3620CertificateValid
    leaf3620InnerLogValid leaf3620CoversExact leaf3620LowerChecked

private noncomputable def leaf3621Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (69/32), kHi := (35/16), chiLo := (9/32), chiHi := (19/64) }

private noncomputable def leaf3621Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217905/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716752896) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (215575529/134217728) }, upper := { exponent := 0, mantissa := (1689/1024) } }, logOuter := sk76LogOuterCertificate, logK := sk76LogKCertificate, logChi := chi56LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435246591/137433505792) } }, logDArg := sk76LogDArgCertificate }

private noncomputable def leaf3621InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf3621LocalValidity :
    LeafFacts leaf3621Box leaf3621Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3621Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716752896) }) = true
      norm_num [leaf3621Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3621CertificateValid :
    WideCertificateValid leaf3621Box leaf3621Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk76ValidityFacts chi56ValidityFacts
    leaf3621LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3621CoverageChecked :
    coverageCheck (innerAD leaf3621Box) leaf3621InnerLog = true := by
  rfl'

private theorem leaf3621InnerLogValid :
    leaf3621InnerLog.Valid 8 (innerAD leaf3621Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf3621CoverageChecked

private noncomputable def leaf3621InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629293/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3621InputLogOnePlusV_eq :
    leaf3621InputLogOnePlusV = outerEnclosure 24
      (leaf3621Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3621RoundedFacts : LeafRoundedFacts 8
    leaf3621Certificate.logOnePlusV leaf3621InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3621InputLogOnePlusV_eq }

private noncomputable def leaf3621Inputs : Inputs :=
  inputsOfCaches globalInput sk76RoundedInputs
    chi56InputQChi innerPair51Input
    leaf3621InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3621LowerChecked :
    lowerCheck 24 leaf3621Box leaf3621Inputs = true := by
  rfl'

private theorem leaf3621CoversExact : CoversExact 8
    leaf3621Box leaf3621Certificate leaf3621InnerLog leaf3621Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk76RoundedFacts chi56RoundedFacts
    innerPair51RoundedFacts leaf3621RoundedFacts (by rfl)

private theorem leaf3621FlatSound : Sound leaf3621Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3621CertificateValid
    leaf3621InnerLogValid leaf3621CoversExact leaf3621LowerChecked

private noncomputable def leaf3622Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (69/32), chiLo := (19/64), chiHi := (5/16) }

private noncomputable def leaf3622Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217905/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716650496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (218852129/134217728) }, upper := { exponent := 0, mantissa := (857/512) } }, logOuter := sk75LogOuterCertificate, logK := sk75LogKCertificate, logChi := chi57LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435144191/137433300992) } }, logDArg := sk75LogDArgCertificate }

private noncomputable def leaf3622InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf3622LocalValidity :
    LeafFacts leaf3622Box leaf3622Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3622Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716650496) }) = true
      norm_num [leaf3622Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3622CertificateValid :
    WideCertificateValid leaf3622Box leaf3622Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk75ValidityFacts chi57ValidityFacts
    leaf3622LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3622CoverageChecked :
    coverageCheck (innerAD leaf3622Box) leaf3622InnerLog = true := by
  rfl'

private theorem leaf3622InnerLogValid :
    leaf3622InnerLog.Valid 8 (innerAD leaf3622Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf3622CoverageChecked

private noncomputable def leaf3622InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814653/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3622InputLogOnePlusV_eq :
    leaf3622InputLogOnePlusV = outerEnclosure 24
      (leaf3622Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3622RoundedFacts : LeafRoundedFacts 8
    leaf3622Certificate.logOnePlusV leaf3622InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3622InputLogOnePlusV_eq }

private noncomputable def leaf3622Inputs : Inputs :=
  inputsOfCaches globalInput sk75RoundedInputs
    chi57InputQChi innerPair56Input
    leaf3622InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3622LowerChecked :
    lowerCheck 24 leaf3622Box leaf3622Inputs = true := by
  rfl'

private theorem leaf3622CoversExact : CoversExact 8
    leaf3622Box leaf3622Certificate leaf3622InnerLog leaf3622Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk75RoundedFacts chi57RoundedFacts
    innerPair56RoundedFacts leaf3622RoundedFacts (by rfl)

private theorem leaf3622FlatSound : Sound leaf3622Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3622CertificateValid
    leaf3622InnerLogValid leaf3622CoversExact leaf3622LowerChecked

private noncomputable def leaf3623Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (69/32), kHi := (35/16), chiLo := (19/64), chiHi := (5/16) }

private noncomputable def leaf3623Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217907/134217728) }, vSqrt := { lower := (65531/65536), upper := (22906164565/22905536512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (220097235/134217728) }, upper := { exponent := 0, mantissa := (431/256) } }, logOuter := sk76LogOuterCertificate, logK := sk76LogKCertificate, logChi := chi57LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (45811701077/45811073024) } }, logDArg := sk76LogDArgCertificate }

private noncomputable def leaf3623InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf3623LocalValidity :
    LeafFacts leaf3623Box leaf3623Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3623Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (22906164565/22905536512) }) = true
      norm_num [leaf3623Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3623CertificateValid :
    WideCertificateValid leaf3623Box leaf3623Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk76ValidityFacts chi57ValidityFacts
    leaf3623LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3623CoverageChecked :
    coverageCheck (innerAD leaf3623Box) leaf3623InnerLog = true := by
  rfl'

private theorem leaf3623InnerLogValid :
    leaf3623InnerLog.Valid 8 (innerAD leaf3623Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf3623CoverageChecked

private noncomputable def leaf3623InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629311/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3623InputLogOnePlusV_eq :
    leaf3623InputLogOnePlusV = outerEnclosure 24
      (leaf3623Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3623RoundedFacts : LeafRoundedFacts 8
    leaf3623Certificate.logOnePlusV leaf3623InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3623InputLogOnePlusV_eq }

private noncomputable def leaf3623Inputs : Inputs :=
  inputsOfCaches globalInput sk76RoundedInputs
    chi57InputQChi innerPair56Input
    leaf3623InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3623LowerChecked :
    lowerCheck 24 leaf3623Box leaf3623Inputs = true := by
  rfl'

private theorem leaf3623CoversExact : CoversExact 8
    leaf3623Box leaf3623Certificate leaf3623InnerLog leaf3623Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk76RoundedFacts chi57RoundedFacts
    innerPair56RoundedFacts leaf3623RoundedFacts (by rfl)

private theorem leaf3623FlatSound : Sound leaf3623Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3623CertificateValid
    leaf3623InnerLogValid leaf3623CoversExact leaf3623LowerChecked

private noncomputable def leaf3624Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (71/32), chiLo := (9/32), chiHi := (19/64) }

private noncomputable def leaf3624Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217907/134217728) }, vSqrt := { lower := (65531/65536), upper := (22906164565/22905571328) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (216755103/134217728) }, upper := { exponent := 0, mantissa := (3397/2048) } }, logOuter := sk77LogOuterCertificate, logK := sk77LogKCertificate, logChi := chi56LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (45811735893/45811142656) } }, logDArg := sk77LogDArgCertificate }

private noncomputable def leaf3624InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf3624LocalValidity :
    LeafFacts leaf3624Box leaf3624Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3624Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (22906164565/22905571328) }) = true
      norm_num [leaf3624Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3624CertificateValid :
    WideCertificateValid leaf3624Box leaf3624Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk77ValidityFacts chi56ValidityFacts
    leaf3624LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3624CoverageChecked :
    coverageCheck (innerAD leaf3624Box) leaf3624InnerLog = true := by
  rfl'

private theorem leaf3624InnerLogValid :
    leaf3624InnerLog.Valid 8 (innerAD leaf3624Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf3624CoverageChecked

private noncomputable def leaf3624InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814649/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3624InputLogOnePlusV_eq :
    leaf3624InputLogOnePlusV = outerEnclosure 24
      (leaf3624Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3624RoundedFacts : LeafRoundedFacts 8
    leaf3624Certificate.logOnePlusV leaf3624InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3624InputLogOnePlusV_eq }

private noncomputable def leaf3624Inputs : Inputs :=
  inputsOfCaches globalInput sk77RoundedInputs
    chi56InputQChi innerPair51Input
    leaf3624InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3624LowerChecked :
    lowerCheck 24 leaf3624Box leaf3624Inputs = true := by
  rfl'

private theorem leaf3624CoversExact : CoversExact 8
    leaf3624Box leaf3624Certificate leaf3624InnerLog leaf3624Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk77RoundedFacts chi56RoundedFacts
    innerPair51RoundedFacts leaf3624RoundedFacts (by rfl)

private theorem leaf3624FlatSound : Sound leaf3624Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3624CertificateValid
    leaf3624InnerLogValid leaf3624CoversExact leaf3624LowerChecked

private noncomputable def leaf3625Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (71/32), kHi := (9/4), chiLo := (9/32), chiHi := (19/64) }

private noncomputable def leaf3625Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217909/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716675072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (217934677/134217728) }, upper := { exponent := 0, mantissa := (427/256) } }, logOuter := sk78LogOuterCertificate, logK := sk78LogKCertificate, logChi := chi56LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435168767/137433350144) } }, logDArg := sk78LogDArgCertificate }

private noncomputable def leaf3625InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf3625LocalValidity :
    LeafFacts leaf3625Box leaf3625Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3625Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716675072) }) = true
      norm_num [leaf3625Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3625CertificateValid :
    WideCertificateValid leaf3625Box leaf3625Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk78ValidityFacts chi56ValidityFacts
    leaf3625LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3625CoverageChecked :
    coverageCheck (innerAD leaf3625Box) leaf3625InnerLog = true := by
  rfl'

private theorem leaf3625InnerLogValid :
    leaf3625InnerLog.Valid 8 (innerAD leaf3625Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf3625CoverageChecked

private noncomputable def leaf3625InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629303/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3625InputLogOnePlusV_eq :
    leaf3625InputLogOnePlusV = outerEnclosure 24
      (leaf3625Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3625RoundedFacts : LeafRoundedFacts 8
    leaf3625Certificate.logOnePlusV leaf3625InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3625InputLogOnePlusV_eq }

private noncomputable def leaf3625Inputs : Inputs :=
  inputsOfCaches globalInput sk78RoundedInputs
    chi56InputQChi innerPair51Input
    leaf3625InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3625LowerChecked :
    lowerCheck 24 leaf3625Box leaf3625Inputs = true := by
  rfl'

private theorem leaf3625CoversExact : CoversExact 8
    leaf3625Box leaf3625Certificate leaf3625InnerLog leaf3625Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk78RoundedFacts chi56RoundedFacts
    innerPair51RoundedFacts leaf3625RoundedFacts (by rfl)

private theorem leaf3625FlatSound : Sound leaf3625Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3625CertificateValid
    leaf3625InnerLogValid leaf3625CoversExact leaf3625LowerChecked

private noncomputable def leaf3626Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (71/32), chiLo := (19/64), chiHi := (5/16) }

private noncomputable def leaf3626Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217909/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716568576) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (221342341/134217728) }, upper := { exponent := 0, mantissa := (867/512) } }, logOuter := sk77LogOuterCertificate, logK := sk77LogKCertificate, logChi := chi57LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435062271/137433137152) } }, logDArg := sk77LogDArgCertificate }

private noncomputable def leaf3626InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf3626LocalValidity :
    LeafFacts leaf3626Box leaf3626Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3626Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716568576) }) = true
      norm_num [leaf3626Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3626CertificateValid :
    WideCertificateValid leaf3626Box leaf3626Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk77ValidityFacts chi57ValidityFacts
    leaf3626LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3626CoverageChecked :
    coverageCheck (innerAD leaf3626Box) leaf3626InnerLog = true := by
  rfl'

private theorem leaf3626InnerLogValid :
    leaf3626InnerLog.Valid 8 (innerAD leaf3626Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf3626CoverageChecked

private noncomputable def leaf3626InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907329/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3626InputLogOnePlusV_eq :
    leaf3626InputLogOnePlusV = outerEnclosure 24
      (leaf3626Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3626RoundedFacts : LeafRoundedFacts 8
    leaf3626Certificate.logOnePlusV leaf3626InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3626InputLogOnePlusV_eq }

private noncomputable def leaf3626Inputs : Inputs :=
  inputsOfCaches globalInput sk77RoundedInputs
    chi57InputQChi innerPair57Input
    leaf3626InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3626LowerChecked :
    lowerCheck 24 leaf3626Box leaf3626Inputs = true := by
  rfl'

private theorem leaf3626CoversExact : CoversExact 8
    leaf3626Box leaf3626Certificate leaf3626InnerLog leaf3626Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk77RoundedFacts chi57RoundedFacts
    innerPair57RoundedFacts leaf3626RoundedFacts (by rfl)

private theorem leaf3626FlatSound : Sound leaf3626Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3626CertificateValid
    leaf3626InnerLogValid leaf3626CoversExact leaf3626LowerChecked

private noncomputable def leaf3627Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (71/32), kHi := (9/4), chiLo := (19/64), chiHi := (5/16) }

private noncomputable def leaf3627Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217911/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716527616) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (222587447/134217728) }, upper := { exponent := 0, mantissa := (109/64) } }, logOuter := sk78LogOuterCertificate, logK := sk78LogKCertificate, logChi := chi57LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435021311/137433055232) } }, logDArg := sk78LogDArgCertificate }

private noncomputable def leaf3627InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf3627LocalValidity :
    LeafFacts leaf3627Box leaf3627Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3627Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716527616) }) = true
      norm_num [leaf3627Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3627CertificateValid :
    WideCertificateValid leaf3627Box leaf3627Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk78ValidityFacts chi57ValidityFacts
    leaf3627LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3627CoverageChecked :
    coverageCheck (innerAD leaf3627Box) leaf3627InnerLog = true := by
  rfl'

private theorem leaf3627InnerLogValid :
    leaf3627InnerLog.Valid 8 (innerAD leaf3627Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf3627CoverageChecked

private noncomputable def leaf3627InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629321/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3627InputLogOnePlusV_eq :
    leaf3627InputLogOnePlusV = outerEnclosure 24
      (leaf3627Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3627RoundedFacts : LeafRoundedFacts 8
    leaf3627Certificate.logOnePlusV leaf3627InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3627InputLogOnePlusV_eq }

private noncomputable def leaf3627Inputs : Inputs :=
  inputsOfCaches globalInput sk78RoundedInputs
    chi57InputQChi innerPair57Input
    leaf3627InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3627LowerChecked :
    lowerCheck 24 leaf3627Box leaf3627Inputs = true := by
  rfl'

private theorem leaf3627CoversExact : CoversExact 8
    leaf3627Box leaf3627Certificate leaf3627InnerLog leaf3627Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk78RoundedFacts chi57RoundedFacts
    innerPair57RoundedFacts leaf3627RoundedFacts (by rfl)

private theorem leaf3627FlatSound : Sound leaf3627Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3627CertificateValid
    leaf3627InnerLogValid leaf3627CoversExact leaf3627LowerChecked

private noncomputable def leaf3628Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (65/32), chiLo := (5/16), chiHi := (21/64) }

private noncomputable def leaf3628Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217899/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716681216) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (218065751/134217728) }, upper := { exponent := 0, mantissa := (3413/2048) } }, logOuter := sk71LogOuterCertificate, logK := sk71LogKCertificate, logChi := chi58LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435174911/137433362432) } }, logDArg := sk71LogDArgCertificate }

private noncomputable def leaf3628InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf3628LocalValidity :
    LeafFacts leaf3628Box leaf3628Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3628Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716681216) }) = true
      norm_num [leaf3628Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3628CertificateValid :
    WideCertificateValid leaf3628Box leaf3628Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk71ValidityFacts chi58ValidityFacts
    leaf3628LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3628CoverageChecked :
    coverageCheck (innerAD leaf3628Box) leaf3628InnerLog = true := by
  rfl'

private theorem leaf3628InnerLogValid :
    leaf3628InnerLog.Valid 8 (innerAD leaf3628Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf3628CoverageChecked

private noncomputable def leaf3628InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814651/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3628InputLogOnePlusV_eq :
    leaf3628InputLogOnePlusV = outerEnclosure 24
      (leaf3628Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3628RoundedFacts : LeafRoundedFacts 8
    leaf3628Certificate.logOnePlusV leaf3628InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3628InputLogOnePlusV_eq }

private noncomputable def leaf3628Inputs : Inputs :=
  inputsOfCaches globalInput sk71RoundedInputs
    chi58InputQChi innerPair51Input
    leaf3628InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3628LowerChecked :
    lowerCheck 24 leaf3628Box leaf3628Inputs = true := by
  rfl'

private theorem leaf3628CoversExact : CoversExact 8
    leaf3628Box leaf3628Certificate leaf3628InnerLog leaf3628Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk71RoundedFacts chi58RoundedFacts
    innerPair51RoundedFacts leaf3628RoundedFacts (by rfl)

private theorem leaf3628FlatSound : Sound leaf3628Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3628CertificateValid
    leaf3628InnerLogValid leaf3628CoversExact leaf3628LowerChecked

private noncomputable def leaf3629Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (65/32), kHi := (33/16), chiLo := (5/16), chiHi := (21/64) }

private noncomputable def leaf3629Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217901/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716638208) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (219376389/134217728) }, upper := { exponent := 0, mantissa := (1717/1024) } }, logOuter := sk72LogOuterCertificate, logK := sk72LogKCertificate, logChi := chi58LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435131903/137433276416) } }, logDArg := sk72LogDArgCertificate }

private noncomputable def leaf3629InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf3629LocalValidity :
    LeafFacts leaf3629Box leaf3629Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3629Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716638208) }) = true
      norm_num [leaf3629Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3629CertificateValid :
    WideCertificateValid leaf3629Box leaf3629Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk72ValidityFacts chi58ValidityFacts
    leaf3629LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3629CoverageChecked :
    coverageCheck (innerAD leaf3629Box) leaf3629InnerLog = true := by
  rfl'

private theorem leaf3629InnerLogValid :
    leaf3629InnerLog.Valid 8 (innerAD leaf3629Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf3629CoverageChecked

private noncomputable def leaf3629InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629307/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3629InputLogOnePlusV_eq :
    leaf3629InputLogOnePlusV = outerEnclosure 24
      (leaf3629Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3629RoundedFacts : LeafRoundedFacts 8
    leaf3629Certificate.logOnePlusV leaf3629InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3629InputLogOnePlusV_eq }

private noncomputable def leaf3629Inputs : Inputs :=
  inputsOfCaches globalInput sk72RoundedInputs
    chi58InputQChi innerPair56Input
    leaf3629InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3629LowerChecked :
    lowerCheck 24 leaf3629Box leaf3629Inputs = true := by
  rfl'

private theorem leaf3629CoversExact : CoversExact 8
    leaf3629Box leaf3629Certificate leaf3629InnerLog leaf3629Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk72RoundedFacts chi58RoundedFacts
    innerPair56RoundedFacts leaf3629RoundedFacts (by rfl)

private theorem leaf3629FlatSound : Sound leaf3629Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3629CertificateValid
    leaf3629InnerLogValid leaf3629CoversExact leaf3629LowerChecked

private noncomputable def leaf3630Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (65/32), chiLo := (21/64), chiHi := (11/32) }

private noncomputable def leaf3630Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217901/134217728) }, vSqrt := { lower := (65531/65536), upper := (1347421445/1347383296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (222259797/134217728) }, upper := { exponent := 0, mantissa := (1739/1024) } }, logOuter := sk71LogOuterCertificate, logK := sk71LogKCertificate, logChi := chi59LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (2694804741/2694766592) } }, logDArg := sk71LogDArgCertificate }

private noncomputable def leaf3630InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf3630LocalValidity :
    LeafFacts leaf3630Box leaf3630Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3630Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (1347421445/1347383296) }) = true
      norm_num [leaf3630Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3630CertificateValid :
    WideCertificateValid leaf3630Box leaf3630Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk71ValidityFacts chi59ValidityFacts
    leaf3630LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3630CoverageChecked :
    coverageCheck (innerAD leaf3630Box) leaf3630InnerLog = true := by
  rfl'

private theorem leaf3630InnerLogValid :
    leaf3630InnerLog.Valid 8 (innerAD leaf3630Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf3630CoverageChecked

private noncomputable def leaf3630InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814659/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3630InputLogOnePlusV_eq :
    leaf3630InputLogOnePlusV = outerEnclosure 24
      (leaf3630Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3630RoundedFacts : LeafRoundedFacts 8
    leaf3630Certificate.logOnePlusV leaf3630InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3630InputLogOnePlusV_eq }

private noncomputable def leaf3630Inputs : Inputs :=
  inputsOfCaches globalInput sk71RoundedInputs
    chi59InputQChi innerPair57Input
    leaf3630InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3630LowerChecked :
    lowerCheck 24 leaf3630Box leaf3630Inputs = true := by
  rfl'

private theorem leaf3630CoversExact : CoversExact 8
    leaf3630Box leaf3630Certificate leaf3630InnerLog leaf3630Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk71RoundedFacts chi59RoundedFacts
    innerPair57RoundedFacts leaf3630RoundedFacts (by rfl)

private theorem leaf3630FlatSound : Sound leaf3630Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3630CertificateValid
    leaf3630InnerLogValid leaf3630CoversExact leaf3630LowerChecked

private noncomputable def leaf3631Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (65/32), kHi := (33/16), chiLo := (21/64), chiHi := (11/32) }

private noncomputable def leaf3631Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217903/134217728) }, vSqrt := { lower := (65531/65536), upper := (13743698739/13743300608) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (223635967/134217728) }, upper := { exponent := 0, mantissa := (875/512) } }, logOuter := sk72LogOuterCertificate, logK := sk72LogKCertificate, logChi := chi59LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (27486999347/27486601216) } }, logDArg := sk72LogDArgCertificate }

private noncomputable def leaf3631InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf3631LocalValidity :
    LeafFacts leaf3631Box leaf3631Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3631Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (13743698739/13743300608) }) = true
      norm_num [leaf3631Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3631CertificateValid :
    WideCertificateValid leaf3631Box leaf3631Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk72ValidityFacts chi59ValidityFacts
    leaf3631LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3631CoverageChecked :
    coverageCheck (innerAD leaf3631Box) leaf3631InnerLog = true := by
  rfl'

private theorem leaf3631InnerLogValid :
    leaf3631InnerLog.Valid 8 (innerAD leaf3631Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf3631CoverageChecked

private noncomputable def leaf3631InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907331/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3631InputLogOnePlusV_eq :
    leaf3631InputLogOnePlusV = outerEnclosure 24
      (leaf3631Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3631RoundedFacts : LeafRoundedFacts 8
    leaf3631Certificate.logOnePlusV leaf3631InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3631InputLogOnePlusV_eq }

private noncomputable def leaf3631Inputs : Inputs :=
  inputsOfCaches globalInput sk72RoundedInputs
    chi59InputQChi innerPair57Input
    leaf3631InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3631LowerChecked :
    lowerCheck 24 leaf3631Box leaf3631Inputs = true := by
  rfl'

private theorem leaf3631CoversExact : CoversExact 8
    leaf3631Box leaf3631Certificate leaf3631InnerLog leaf3631Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk72RoundedFacts chi59RoundedFacts
    innerPair57RoundedFacts leaf3631RoundedFacts (by rfl)

private theorem leaf3631FlatSound : Sound leaf3631Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3631CertificateValid
    leaf3631InnerLogValid leaf3631CoversExact leaf3631LowerChecked

private noncomputable def leaf3632Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (67/32), chiLo := (5/16), chiHi := (21/64) }

private noncomputable def leaf3632Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217903/134217728) }, vSqrt := { lower := (65531/65536), upper := (13743698739/13743319040) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (220687027/134217728) }, upper := { exponent := 0, mantissa := (3455/2048) } }, logOuter := sk73LogOuterCertificate, logK := sk73LogKCertificate, logChi := chi58LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (27487017779/27486638080) } }, logDArg := sk73LogDArgCertificate }

private noncomputable def leaf3632InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf3632LocalValidity :
    LeafFacts leaf3632Box leaf3632Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3632Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (13743698739/13743319040) }) = true
      norm_num [leaf3632Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3632CertificateValid :
    WideCertificateValid leaf3632Box leaf3632Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk73ValidityFacts chi58ValidityFacts
    leaf3632LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3632CoverageChecked :
    coverageCheck (innerAD leaf3632Box) leaf3632InnerLog = true := by
  rfl'

private theorem leaf3632InnerLogValid :
    leaf3632InnerLog.Valid 8 (innerAD leaf3632Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf3632CoverageChecked

private noncomputable def leaf3632InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629313/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3632InputLogOnePlusV_eq :
    leaf3632InputLogOnePlusV = outerEnclosure 24
      (leaf3632Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3632RoundedFacts : LeafRoundedFacts 8
    leaf3632Certificate.logOnePlusV leaf3632InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3632InputLogOnePlusV_eq }

private noncomputable def leaf3632Inputs : Inputs :=
  inputsOfCaches globalInput sk73RoundedInputs
    chi58InputQChi innerPair56Input
    leaf3632InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3632LowerChecked :
    lowerCheck 24 leaf3632Box leaf3632Inputs = true := by
  rfl'

private theorem leaf3632CoversExact : CoversExact 8
    leaf3632Box leaf3632Certificate leaf3632InnerLog leaf3632Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk73RoundedFacts chi58RoundedFacts
    innerPair56RoundedFacts leaf3632RoundedFacts (by rfl)

private theorem leaf3632FlatSound : Sound leaf3632Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3632CertificateValid
    leaf3632InnerLogValid leaf3632CoversExact leaf3632LowerChecked

private noncomputable def leaf3633Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (67/32), kHi := (17/8), chiLo := (5/16), chiHi := (21/64) }

private noncomputable def leaf3633Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217905/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716552192) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (221997665/134217728) }, upper := { exponent := 0, mantissa := (869/512) } }, logOuter := sk74LogOuterCertificate, logK := sk74LogKCertificate, logChi := chi58LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435045887/137433104384) } }, logDArg := sk74LogDArgCertificate }

private noncomputable def leaf3633InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf3633LocalValidity :
    LeafFacts leaf3633Box leaf3633Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3633Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716552192) }) = true
      norm_num [leaf3633Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3633CertificateValid :
    WideCertificateValid leaf3633Box leaf3633Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk74ValidityFacts chi58ValidityFacts
    leaf3633LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3633CoverageChecked :
    coverageCheck (innerAD leaf3633Box) leaf3633InnerLog = true := by
  rfl'

private theorem leaf3633InnerLogValid :
    leaf3633InnerLog.Valid 8 (innerAD leaf3633Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf3633CoverageChecked

private noncomputable def leaf3633InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814659/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3633InputLogOnePlusV_eq :
    leaf3633InputLogOnePlusV = outerEnclosure 24
      (leaf3633Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3633RoundedFacts : LeafRoundedFacts 8
    leaf3633Certificate.logOnePlusV leaf3633InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3633InputLogOnePlusV_eq }

private noncomputable def leaf3633Inputs : Inputs :=
  inputsOfCaches globalInput sk74RoundedInputs
    chi58InputQChi innerPair57Input
    leaf3633InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3633LowerChecked :
    lowerCheck 24 leaf3633Box leaf3633Inputs = true := by
  rfl'

private theorem leaf3633CoversExact : CoversExact 8
    leaf3633Box leaf3633Certificate leaf3633InnerLog leaf3633Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk74RoundedFacts chi58RoundedFacts
    innerPair57RoundedFacts leaf3633RoundedFacts (by rfl)

private theorem leaf3633FlatSound : Sound leaf3633Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3633CertificateValid
    leaf3633InnerLogValid leaf3633CoversExact leaf3633LowerChecked

private noncomputable def leaf3634Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (67/32), chiLo := (21/64), chiHi := (11/32) }

private noncomputable def leaf3634Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217905/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716457984) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (225012137/134217728) }, upper := { exponent := 0, mantissa := (1761/1024) } }, logOuter := sk73LogOuterCertificate, logK := sk73LogKCertificate, logChi := chi59LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434951679/137432915968) } }, logDArg := sk73LogDArgCertificate }

private noncomputable def leaf3634InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf3634LocalValidity :
    LeafFacts leaf3634Box leaf3634Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3634Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716457984) }) = true
      norm_num [leaf3634Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3634CertificateValid :
    WideCertificateValid leaf3634Box leaf3634Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk73ValidityFacts chi59ValidityFacts
    leaf3634LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3634CoverageChecked :
    coverageCheck (innerAD leaf3634Box) leaf3634InnerLog = true := by
  rfl'

private theorem leaf3634InnerLogValid :
    leaf3634InnerLog.Valid 8 (innerAD leaf3634Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf3634CoverageChecked

private noncomputable def leaf3634InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629329/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3634InputLogOnePlusV_eq :
    leaf3634InputLogOnePlusV = outerEnclosure 24
      (leaf3634Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3634RoundedFacts : LeafRoundedFacts 8
    leaf3634Certificate.logOnePlusV leaf3634InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3634InputLogOnePlusV_eq }

private noncomputable def leaf3634Inputs : Inputs :=
  inputsOfCaches globalInput sk73RoundedInputs
    chi59InputQChi innerPair57Input
    leaf3634InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3634LowerChecked :
    lowerCheck 24 leaf3634Box leaf3634Inputs = true := by
  rfl'

private theorem leaf3634CoversExact : CoversExact 8
    leaf3634Box leaf3634Certificate leaf3634InnerLog leaf3634Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk73RoundedFacts chi59RoundedFacts
    innerPair57RoundedFacts leaf3634RoundedFacts (by rfl)

private theorem leaf3634FlatSound : Sound leaf3634Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3634CertificateValid
    leaf3634InnerLogValid leaf3634CoversExact leaf3634LowerChecked

private noncomputable def leaf3635Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (67/32), kHi := (17/8), chiLo := (21/64), chiHi := (11/32) }

private noncomputable def leaf3635Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217907/134217728) }, vSqrt := { lower := (65531/65536), upper := (22906164565/22905470976) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (226388307/134217728) }, upper := { exponent := 0, mantissa := (443/256) } }, logOuter := sk74LogOuterCertificate, logK := sk74LogKCertificate, logChi := chi59LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (45811635541/45810941952) } }, logDArg := sk74LogDArgCertificate }

private noncomputable def leaf3635InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf3635LocalValidity :
    LeafFacts leaf3635Box leaf3635Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3635Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (22906164565/22905470976) }) = true
      norm_num [leaf3635Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3635CertificateValid :
    WideCertificateValid leaf3635Box leaf3635Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk74ValidityFacts chi59ValidityFacts
    leaf3635LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3635CoverageChecked :
    coverageCheck (innerAD leaf3635Box) leaf3635InnerLog = true := by
  rfl'

private theorem leaf3635InnerLogValid :
    leaf3635InnerLog.Valid 8 (innerAD leaf3635Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf3635CoverageChecked

private noncomputable def leaf3635InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629335/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3635InputLogOnePlusV_eq :
    leaf3635InputLogOnePlusV = outerEnclosure 24
      (leaf3635Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3635RoundedFacts : LeafRoundedFacts 8
    leaf3635Certificate.logOnePlusV leaf3635InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3635InputLogOnePlusV_eq }

private noncomputable def leaf3635Inputs : Inputs :=
  inputsOfCaches globalInput sk74RoundedInputs
    chi59InputQChi innerPair57Input
    leaf3635InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3635LowerChecked :
    lowerCheck 24 leaf3635Box leaf3635Inputs = true := by
  rfl'

private theorem leaf3635CoversExact : CoversExact 8
    leaf3635Box leaf3635Certificate leaf3635InnerLog leaf3635Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk74RoundedFacts chi59RoundedFacts
    innerPair57RoundedFacts leaf3635RoundedFacts (by rfl)

private theorem leaf3635FlatSound : Sound leaf3635Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3635CertificateValid
    leaf3635InnerLogValid leaf3635CoversExact leaf3635LowerChecked

private noncomputable def leaf3636Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (65/32), chiLo := (11/32), chiHi := (23/64) }

private noncomputable def leaf3636Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217903/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716414976) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (226453843/134217728) }, upper := { exponent := 0, mantissa := (3543/2048) } }, logOuter := sk71LogOuterCertificate, logK := sk71LogKCertificate, logChi := chi60LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434908671/137432829952) } }, logDArg := sk71LogDArgCertificate }

private noncomputable def leaf3636InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf3636LocalValidity :
    LeafFacts leaf3636Box leaf3636Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3636Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716414976) }) = true
      norm_num [leaf3636Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3636CertificateValid :
    WideCertificateValid leaf3636Box leaf3636Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk71ValidityFacts chi60ValidityFacts
    leaf3636LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3636CoverageChecked :
    coverageCheck (innerAD leaf3636Box) leaf3636InnerLog = true := by
  rfl'

private theorem leaf3636InnerLogValid :
    leaf3636InnerLog.Valid 8 (innerAD leaf3636Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf3636CoverageChecked

private noncomputable def leaf3636InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629335/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3636InputLogOnePlusV_eq :
    leaf3636InputLogOnePlusV = outerEnclosure 24
      (leaf3636Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3636RoundedFacts : LeafRoundedFacts 8
    leaf3636Certificate.logOnePlusV leaf3636InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3636InputLogOnePlusV_eq }

private noncomputable def leaf3636Inputs : Inputs :=
  inputsOfCaches globalInput sk71RoundedInputs
    chi60InputQChi innerPair57Input
    leaf3636InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3636LowerChecked :
    lowerCheck 24 leaf3636Box leaf3636Inputs = true := by
  rfl'

private theorem leaf3636CoversExact : CoversExact 8
    leaf3636Box leaf3636Certificate leaf3636InnerLog leaf3636Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk71RoundedFacts chi60RoundedFacts
    innerPair57RoundedFacts leaf3636RoundedFacts (by rfl)

private theorem leaf3636FlatSound : Sound leaf3636Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3636CertificateValid
    leaf3636InnerLogValid leaf3636CoversExact leaf3636LowerChecked

private noncomputable def leaf3637Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (65/32), kHi := (33/16), chiLo := (11/32), chiHi := (23/64) }

private noncomputable def leaf3637Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217905/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716367872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (227895545/134217728) }, upper := { exponent := 0, mantissa := (1783/1024) } }, logOuter := sk72LogOuterCertificate, logK := sk72LogKCertificate, logChi := chi60LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434861567/137432735744) } }, logDArg := sk72LogDArgCertificate }

private noncomputable def leaf3637InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3637LocalValidity :
    LeafFacts leaf3637Box leaf3637Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3637Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716367872) }) = true
      norm_num [leaf3637Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3637CertificateValid :
    WideCertificateValid leaf3637Box leaf3637Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk72ValidityFacts chi60ValidityFacts
    leaf3637LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3637CoverageChecked :
    coverageCheck (innerAD leaf3637Box) leaf3637InnerLog = true := by
  rfl'

private theorem leaf3637InnerLogValid :
    leaf3637InnerLog.Valid 8 (innerAD leaf3637Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3637CoverageChecked

private noncomputable def leaf3637InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907335/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3637InputLogOnePlusV_eq :
    leaf3637InputLogOnePlusV = outerEnclosure 24
      (leaf3637Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3637RoundedFacts : LeafRoundedFacts 8
    leaf3637Certificate.logOnePlusV leaf3637InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3637InputLogOnePlusV_eq }

private noncomputable def leaf3637Inputs : Inputs :=
  inputsOfCaches globalInput sk72RoundedInputs
    chi60InputQChi innerPair64Input
    leaf3637InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3637LowerChecked :
    lowerCheck 24 leaf3637Box leaf3637Inputs = true := by
  rfl'

private theorem leaf3637CoversExact : CoversExact 8
    leaf3637Box leaf3637Certificate leaf3637InnerLog leaf3637Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk72RoundedFacts chi60RoundedFacts
    innerPair64RoundedFacts leaf3637RoundedFacts (by rfl)

private theorem leaf3637FlatSound : Sound leaf3637Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3637CertificateValid
    leaf3637InnerLogValid leaf3637CoversExact leaf3637LowerChecked

private noncomputable def leaf3638Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (65/32), chiLo := (23/64), chiHi := (3/8) }

private noncomputable def leaf3638Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217905/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716281856) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (230647889/134217728) }, upper := { exponent := 0, mantissa := (451/256) } }, logOuter := sk71LogOuterCertificate, logK := sk71LogKCertificate, logChi := chi61LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434775551/137432563712) } }, logDArg := sk71LogDArgCertificate }

private noncomputable def leaf3638InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf3638LocalValidity :
    LeafFacts leaf3638Box leaf3638Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3638Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716281856) }) = true
      norm_num [leaf3638Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3638CertificateValid :
    WideCertificateValid leaf3638Box leaf3638Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk71ValidityFacts chi61ValidityFacts
    leaf3638LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3638CoverageChecked :
    coverageCheck (innerAD leaf3638Box) leaf3638InnerLog = true := by
  rfl'

private theorem leaf3638InnerLogValid :
    leaf3638InnerLog.Valid 8 (innerAD leaf3638Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf3638CoverageChecked

private noncomputable def leaf3638InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629351/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3638InputLogOnePlusV_eq :
    leaf3638InputLogOnePlusV = outerEnclosure 24
      (leaf3638Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3638RoundedFacts : LeafRoundedFacts 8
    leaf3638Certificate.logOnePlusV leaf3638InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3638InputLogOnePlusV_eq }

private noncomputable def leaf3638Inputs : Inputs :=
  inputsOfCaches globalInput sk71RoundedInputs
    chi61InputQChi innerPair66Input
    leaf3638InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3638LowerChecked :
    lowerCheck 24 leaf3638Box leaf3638Inputs = true := by
  rfl'

private theorem leaf3638CoversExact : CoversExact 8
    leaf3638Box leaf3638Certificate leaf3638InnerLog leaf3638Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk71RoundedFacts chi61RoundedFacts
    innerPair66RoundedFacts leaf3638RoundedFacts (by rfl)

private theorem leaf3638FlatSound : Sound leaf3638Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3638CertificateValid
    leaf3638InnerLogValid leaf3638CoversExact leaf3638LowerChecked

private noncomputable def leaf3639Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (65/32), kHi := (33/16), chiLo := (23/64), chiHi := (3/8) }

private noncomputable def leaf3639Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217907/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716232704) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (232155123/134217728) }, upper := { exponent := 0, mantissa := (227/128) } }, logOuter := sk72LogOuterCertificate, logK := sk72LogKCertificate, logChi := chi61LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434726399/137432465408) } }, logDArg := sk72LogDArgCertificate }

private noncomputable def leaf3639InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf3639LocalValidity :
    LeafFacts leaf3639Box leaf3639Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3639Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716232704) }) = true
      norm_num [leaf3639Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3639CertificateValid :
    WideCertificateValid leaf3639Box leaf3639Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk72ValidityFacts chi61ValidityFacts
    leaf3639LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3639CoverageChecked :
    coverageCheck (innerAD leaf3639Box) leaf3639InnerLog = true := by
  rfl'

private theorem leaf3639InnerLogValid :
    leaf3639InnerLog.Valid 8 (innerAD leaf3639Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf3639CoverageChecked

private noncomputable def leaf3639InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629357/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3639InputLogOnePlusV_eq :
    leaf3639InputLogOnePlusV = outerEnclosure 24
      (leaf3639Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3639RoundedFacts : LeafRoundedFacts 8
    leaf3639Certificate.logOnePlusV leaf3639InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3639InputLogOnePlusV_eq }

private noncomputable def leaf3639Inputs : Inputs :=
  inputsOfCaches globalInput sk72RoundedInputs
    chi61InputQChi innerPair66Input
    leaf3639InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3639LowerChecked :
    lowerCheck 24 leaf3639Box leaf3639Inputs = true := by
  rfl'

private theorem leaf3639CoversExact : CoversExact 8
    leaf3639Box leaf3639Certificate leaf3639InnerLog leaf3639Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk72RoundedFacts chi61RoundedFacts
    innerPair66RoundedFacts leaf3639RoundedFacts (by rfl)

private theorem leaf3639FlatSound : Sound leaf3639Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3639CertificateValid
    leaf3639InnerLogValid leaf3639CoversExact leaf3639LowerChecked

private noncomputable def leaf3640Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (67/32), chiLo := (11/32), chiHi := (23/64) }

private noncomputable def leaf3640Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217907/134217728) }, vSqrt := { lower := (65531/65536), upper := (22906164565/22905440256) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (229337247/134217728) }, upper := { exponent := 0, mantissa := (3589/2048) } }, logOuter := sk73LogOuterCertificate, logK := sk73LogKCertificate, logChi := chi60LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (45811604821/45810880512) } }, logDArg := sk73LogDArgCertificate }

private noncomputable def leaf3640InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf3640LocalValidity :
    LeafFacts leaf3640Box leaf3640Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3640Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (22906164565/22905440256) }) = true
      norm_num [leaf3640Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3640CertificateValid :
    WideCertificateValid leaf3640Box leaf3640Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk73ValidityFacts chi60ValidityFacts
    leaf3640LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3640CoverageChecked :
    coverageCheck (innerAD leaf3640Box) leaf3640InnerLog = true := by
  rfl'

private theorem leaf3640InnerLogValid :
    leaf3640InnerLog.Valid 8 (innerAD leaf3640Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf3640CoverageChecked

private noncomputable def leaf3640InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814673/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3640InputLogOnePlusV_eq :
    leaf3640InputLogOnePlusV = outerEnclosure 24
      (leaf3640Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3640RoundedFacts : LeafRoundedFacts 8
    leaf3640Certificate.logOnePlusV leaf3640InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3640InputLogOnePlusV_eq }

private noncomputable def leaf3640Inputs : Inputs :=
  inputsOfCaches globalInput sk73RoundedInputs
    chi60InputQChi innerPair66Input
    leaf3640InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3640LowerChecked :
    lowerCheck 24 leaf3640Box leaf3640Inputs = true := by
  rfl'

private theorem leaf3640CoversExact : CoversExact 8
    leaf3640Box leaf3640Certificate leaf3640InnerLog leaf3640Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk73RoundedFacts chi60RoundedFacts
    innerPair66RoundedFacts leaf3640RoundedFacts (by rfl)

private theorem leaf3640FlatSound : Sound leaf3640Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3640CertificateValid
    leaf3640InnerLogValid leaf3640CoversExact leaf3640LowerChecked

private noncomputable def leaf3641Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (67/32), kHi := (17/8), chiLo := (11/32), chiHi := (23/64) }

private noncomputable def leaf3641Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217909/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716273664) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (230778949/134217728) }, upper := { exponent := 0, mantissa := (903/512) } }, logOuter := sk74LogOuterCertificate, logK := sk74LogKCertificate, logChi := chi60LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434767359/137432547328) } }, logDArg := sk74LogDArgCertificate }

private noncomputable def leaf3641InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf3641LocalValidity :
    LeafFacts leaf3641Box leaf3641Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3641Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716273664) }) = true
      norm_num [leaf3641Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3641CertificateValid :
    WideCertificateValid leaf3641Box leaf3641Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk74ValidityFacts chi60ValidityFacts
    leaf3641LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3641CoverageChecked :
    coverageCheck (innerAD leaf3641Box) leaf3641InnerLog = true := by
  rfl'

private theorem leaf3641InnerLogValid :
    leaf3641InnerLog.Valid 8 (innerAD leaf3641Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf3641CoverageChecked

private noncomputable def leaf3641InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (1453669/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3641InputLogOnePlusV_eq :
    leaf3641InputLogOnePlusV = outerEnclosure 24
      (leaf3641Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3641RoundedFacts : LeafRoundedFacts 8
    leaf3641Certificate.logOnePlusV leaf3641InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3641InputLogOnePlusV_eq }

private noncomputable def leaf3641Inputs : Inputs :=
  inputsOfCaches globalInput sk74RoundedInputs
    chi60InputQChi innerPair66Input
    leaf3641InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3641LowerChecked :
    lowerCheck 24 leaf3641Box leaf3641Inputs = true := by
  rfl'

private theorem leaf3641CoversExact : CoversExact 8
    leaf3641Box leaf3641Certificate leaf3641InnerLog leaf3641Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk74RoundedFacts chi60RoundedFacts
    innerPair66RoundedFacts leaf3641RoundedFacts (by rfl)

private theorem leaf3641FlatSound : Sound leaf3641Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3641CertificateValid
    leaf3641InnerLogValid leaf3641CoversExact leaf3641LowerChecked

private noncomputable def leaf3642Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (67/32), chiLo := (23/64), chiHi := (3/8) }

private noncomputable def leaf3642Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217909/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716183552) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (233662357/134217728) }, upper := { exponent := 0, mantissa := (457/256) } }, logOuter := sk73LogOuterCertificate, logK := sk73LogKCertificate, logChi := chi61LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434677247/137432367104) } }, logDArg := sk73LogDArgCertificate }

private noncomputable def leaf3642InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf3642LocalValidity :
    LeafFacts leaf3642Box leaf3642Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3642Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716183552) }) = true
      norm_num [leaf3642Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3642CertificateValid :
    WideCertificateValid leaf3642Box leaf3642Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk73ValidityFacts chi61ValidityFacts
    leaf3642LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3642CoverageChecked :
    coverageCheck (innerAD leaf3642Box) leaf3642InnerLog = true := by
  rfl'

private theorem leaf3642InnerLogValid :
    leaf3642InnerLog.Valid 8 (innerAD leaf3642Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf3642CoverageChecked

private noncomputable def leaf3642InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629363/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3642InputLogOnePlusV_eq :
    leaf3642InputLogOnePlusV = outerEnclosure 24
      (leaf3642Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3642RoundedFacts : LeafRoundedFacts 8
    leaf3642Certificate.logOnePlusV leaf3642InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3642InputLogOnePlusV_eq }

private noncomputable def leaf3642Inputs : Inputs :=
  inputsOfCaches globalInput sk73RoundedInputs
    chi61InputQChi innerPair66Input
    leaf3642InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3642LowerChecked :
    lowerCheck 24 leaf3642Box leaf3642Inputs = true := by
  rfl'

private theorem leaf3642CoversExact : CoversExact 8
    leaf3642Box leaf3642Certificate leaf3642InnerLog leaf3642Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk73RoundedFacts chi61RoundedFacts
    innerPair66RoundedFacts leaf3642RoundedFacts (by rfl)

private theorem leaf3642FlatSound : Sound leaf3642Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3642CertificateValid
    leaf3642InnerLogValid leaf3642CoversExact leaf3642LowerChecked

private noncomputable def leaf3643Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (67/32), kHi := (17/8), chiLo := (23/64), chiHi := (3/8) }

private noncomputable def leaf3643Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217911/134217728) }, vSqrt := { lower := (65531/65536), upper := (13743698739/13743226880) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (235169591/134217728) }, upper := { exponent := 0, mantissa := (115/64) } }, logOuter := sk74LogOuterCertificate, logK := sk74LogKCertificate, logChi := chi61LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (27486925619/27486453760) } }, logDArg := sk74LogDArgCertificate }

private noncomputable def leaf3643InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3643LocalValidity :
    LeafFacts leaf3643Box leaf3643Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3643Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (13743698739/13743226880) }) = true
      norm_num [leaf3643Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3643CertificateValid :
    WideCertificateValid leaf3643Box leaf3643Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk74ValidityFacts chi61ValidityFacts
    leaf3643LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3643CoverageChecked :
    coverageCheck (innerAD leaf3643Box) leaf3643InnerLog = true := by
  rfl'

private theorem leaf3643InnerLogValid :
    leaf3643InnerLog.Valid 8 (innerAD leaf3643Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3643CoverageChecked

private noncomputable def leaf3643InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629369/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3643InputLogOnePlusV_eq :
    leaf3643InputLogOnePlusV = outerEnclosure 24
      (leaf3643Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3643RoundedFacts : LeafRoundedFacts 8
    leaf3643Certificate.logOnePlusV leaf3643InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3643InputLogOnePlusV_eq }

private noncomputable def leaf3643Inputs : Inputs :=
  inputsOfCaches globalInput sk74RoundedInputs
    chi61InputQChi innerPair71Input
    leaf3643InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3643LowerChecked :
    lowerCheck 24 leaf3643Box leaf3643Inputs = true := by
  rfl'

private theorem leaf3643CoversExact : CoversExact 8
    leaf3643Box leaf3643Certificate leaf3643InnerLog leaf3643Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk74RoundedFacts chi61RoundedFacts
    innerPair71RoundedFacts leaf3643RoundedFacts (by rfl)

private theorem leaf3643FlatSound : Sound leaf3643Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3643CertificateValid
    leaf3643InnerLogValid leaf3643CoversExact leaf3643LowerChecked

private noncomputable def leaf3644Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (69/32), chiLo := (5/16), chiHi := (21/64) }

private noncomputable def leaf3644Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217907/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716509184) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (223308303/134217728) }, upper := { exponent := 0, mantissa := (3497/2048) } }, logOuter := sk75LogOuterCertificate, logK := sk75LogKCertificate, logChi := chi58LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435002879/137433018368) } }, logDArg := sk75LogDArgCertificate }

private noncomputable def leaf3644InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf3644LocalValidity :
    LeafFacts leaf3644Box leaf3644Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3644Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716509184) }) = true
      norm_num [leaf3644Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3644CertificateValid :
    WideCertificateValid leaf3644Box leaf3644Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk75ValidityFacts chi58ValidityFacts
    leaf3644LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3644CoverageChecked :
    coverageCheck (innerAD leaf3644Box) leaf3644InnerLog = true := by
  rfl'

private theorem leaf3644InnerLogValid :
    leaf3644InnerLog.Valid 8 (innerAD leaf3644Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf3644CoverageChecked

private noncomputable def leaf3644InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629323/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3644InputLogOnePlusV_eq :
    leaf3644InputLogOnePlusV = outerEnclosure 24
      (leaf3644Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3644RoundedFacts : LeafRoundedFacts 8
    leaf3644Certificate.logOnePlusV leaf3644InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3644InputLogOnePlusV_eq }

private noncomputable def leaf3644Inputs : Inputs :=
  inputsOfCaches globalInput sk75RoundedInputs
    chi58InputQChi innerPair57Input
    leaf3644InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3644LowerChecked :
    lowerCheck 24 leaf3644Box leaf3644Inputs = true := by
  rfl'

private theorem leaf3644CoversExact : CoversExact 8
    leaf3644Box leaf3644Certificate leaf3644InnerLog leaf3644Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk75RoundedFacts chi58RoundedFacts
    innerPair57RoundedFacts leaf3644RoundedFacts (by rfl)

private theorem leaf3644FlatSound : Sound leaf3644Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3644CertificateValid
    leaf3644InnerLogValid leaf3644CoversExact leaf3644LowerChecked

private noncomputable def leaf3645Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (69/32), kHi := (35/16), chiLo := (5/16), chiHi := (21/64) }

private noncomputable def leaf3645Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217909/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716466176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (224618941/134217728) }, upper := { exponent := 0, mantissa := (1759/1024) } }, logOuter := sk76LogOuterCertificate, logK := sk76LogKCertificate, logChi := chi58LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434959871/137432932352) } }, logDArg := sk76LogDArgCertificate }

private noncomputable def leaf3645InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf3645LocalValidity :
    LeafFacts leaf3645Box leaf3645Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3645Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716466176) }) = true
      norm_num [leaf3645Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3645CertificateValid :
    WideCertificateValid leaf3645Box leaf3645Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk76ValidityFacts chi58ValidityFacts
    leaf3645LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3645CoverageChecked :
    coverageCheck (innerAD leaf3645Box) leaf3645InnerLog = true := by
  rfl'

private theorem leaf3645InnerLogValid :
    leaf3645InnerLog.Valid 8 (innerAD leaf3645Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf3645CoverageChecked

private noncomputable def leaf3645InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (726833/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf3645InputLogOnePlusV_eq :
    leaf3645InputLogOnePlusV = outerEnclosure 24
      (leaf3645Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3645RoundedFacts : LeafRoundedFacts 8
    leaf3645Certificate.logOnePlusV leaf3645InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3645InputLogOnePlusV_eq }

private noncomputable def leaf3645Inputs : Inputs :=
  inputsOfCaches globalInput sk76RoundedInputs
    chi58InputQChi innerPair57Input
    leaf3645InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3645LowerChecked :
    lowerCheck 24 leaf3645Box leaf3645Inputs = true := by
  rfl'

private theorem leaf3645CoversExact : CoversExact 8
    leaf3645Box leaf3645Certificate leaf3645InnerLog leaf3645Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk76RoundedFacts chi58RoundedFacts
    innerPair57RoundedFacts leaf3645RoundedFacts (by rfl)

private theorem leaf3645FlatSound : Sound leaf3645Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3645CertificateValid
    leaf3645InnerLogValid leaf3645CoversExact leaf3645LowerChecked

private noncomputable def leaf3646Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (69/32), chiLo := (21/64), chiHi := (11/32) }

private noncomputable def leaf3646Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217909/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716367872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (227764477/134217728) }, upper := { exponent := 0, mantissa := (1783/1024) } }, logOuter := sk75LogOuterCertificate, logK := sk75LogKCertificate, logChi := chi59LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434861567/137432735744) } }, logDArg := sk75LogDArgCertificate }

private noncomputable def leaf3646InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3646LocalValidity :
    LeafFacts leaf3646Box leaf3646Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3646Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716367872) }) = true
      norm_num [leaf3646Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3646CertificateValid :
    WideCertificateValid leaf3646Box leaf3646Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk75ValidityFacts chi59ValidityFacts
    leaf3646LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3646CoverageChecked :
    coverageCheck (innerAD leaf3646Box) leaf3646InnerLog = true := by
  rfl'

private theorem leaf3646InnerLogValid :
    leaf3646InnerLog.Valid 8 (innerAD leaf3646Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3646CoverageChecked

private noncomputable def leaf3646InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907335/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3646InputLogOnePlusV_eq :
    leaf3646InputLogOnePlusV = outerEnclosure 24
      (leaf3646Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3646RoundedFacts : LeafRoundedFacts 8
    leaf3646Certificate.logOnePlusV leaf3646InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3646InputLogOnePlusV_eq }

private noncomputable def leaf3646Inputs : Inputs :=
  inputsOfCaches globalInput sk75RoundedInputs
    chi59InputQChi innerPair64Input
    leaf3646InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3646LowerChecked :
    lowerCheck 24 leaf3646Box leaf3646Inputs = true := by
  rfl'

private theorem leaf3646CoversExact : CoversExact 8
    leaf3646Box leaf3646Certificate leaf3646InnerLog leaf3646Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk75RoundedFacts chi59RoundedFacts
    innerPair64RoundedFacts leaf3646RoundedFacts (by rfl)

private theorem leaf3646FlatSound : Sound leaf3646Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3646CertificateValid
    leaf3646InnerLogValid leaf3646CoversExact leaf3646LowerChecked

private noncomputable def leaf3647Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (69/32), kHi := (35/16), chiLo := (21/64), chiHi := (11/32) }

private noncomputable def leaf3647Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217911/134217728) }, vSqrt := { lower := (65531/65536), upper := (267387135/267378688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (229140647/134217728) }, upper := { exponent := 0, mantissa := (897/512) } }, logOuter := sk76LogOuterCertificate, logK := sk76LogKCertificate, logChi := chi59LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (534765823/534757376) } }, logDArg := sk76LogDArgCertificate }

private noncomputable def leaf3647InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf3647LocalValidity :
    LeafFacts leaf3647Box leaf3647Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3647Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (267387135/267378688) }) = true
      norm_num [leaf3647Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3647CertificateValid :
    WideCertificateValid leaf3647Box leaf3647Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk76ValidityFacts chi59ValidityFacts
    leaf3647LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3647CoverageChecked :
    coverageCheck (innerAD leaf3647Box) leaf3647InnerLog = true := by
  rfl'

private theorem leaf3647InnerLogValid :
    leaf3647InnerLog.Valid 8 (innerAD leaf3647Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf3647CoverageChecked

private noncomputable def leaf3647InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814673/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3647InputLogOnePlusV_eq :
    leaf3647InputLogOnePlusV = outerEnclosure 24
      (leaf3647Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3647RoundedFacts : LeafRoundedFacts 8
    leaf3647Certificate.logOnePlusV leaf3647InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3647InputLogOnePlusV_eq }

private noncomputable def leaf3647Inputs : Inputs :=
  inputsOfCaches globalInput sk76RoundedInputs
    chi59InputQChi innerPair66Input
    leaf3647InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3647LowerChecked :
    lowerCheck 24 leaf3647Box leaf3647Inputs = true := by
  rfl'

private theorem leaf3647CoversExact : CoversExact 8
    leaf3647Box leaf3647Certificate leaf3647InnerLog leaf3647Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk76RoundedFacts chi59RoundedFacts
    innerPair66RoundedFacts leaf3647RoundedFacts (by rfl)

private theorem leaf3647FlatSound : Sound leaf3647Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3647CertificateValid
    leaf3647InnerLogValid leaf3647CoversExact leaf3647LowerChecked

private noncomputable def leaf3648Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (71/32), chiLo := (5/16), chiHi := (21/64) }

private noncomputable def leaf3648Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217911/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716423168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (225929579/134217728) }, upper := { exponent := 0, mantissa := (3539/2048) } }, logOuter := sk77LogOuterCertificate, logK := sk77LogKCertificate, logChi := chi58LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434916863/137432846336) } }, logDArg := sk77LogDArgCertificate }

private noncomputable def leaf3648InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf3648LocalValidity :
    LeafFacts leaf3648Box leaf3648Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3648Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716423168) }) = true
      norm_num [leaf3648Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3648CertificateValid :
    WideCertificateValid leaf3648Box leaf3648Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk77ValidityFacts chi58ValidityFacts
    leaf3648LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3648CoverageChecked :
    coverageCheck (innerAD leaf3648Box) leaf3648InnerLog = true := by
  rfl'

private theorem leaf3648InnerLogValid :
    leaf3648InnerLog.Valid 8 (innerAD leaf3648Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf3648CoverageChecked

private noncomputable def leaf3648InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814667/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3648InputLogOnePlusV_eq :
    leaf3648InputLogOnePlusV = outerEnclosure 24
      (leaf3648Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3648RoundedFacts : LeafRoundedFacts 8
    leaf3648Certificate.logOnePlusV leaf3648InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3648InputLogOnePlusV_eq }

private noncomputable def leaf3648Inputs : Inputs :=
  inputsOfCaches globalInput sk77RoundedInputs
    chi58InputQChi innerPair57Input
    leaf3648InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3648LowerChecked :
    lowerCheck 24 leaf3648Box leaf3648Inputs = true := by
  rfl'

private theorem leaf3648CoversExact : CoversExact 8
    leaf3648Box leaf3648Certificate leaf3648InnerLog leaf3648Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk77RoundedFacts chi58RoundedFacts
    innerPair57RoundedFacts leaf3648RoundedFacts (by rfl)

private theorem leaf3648FlatSound : Sound leaf3648Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3648CertificateValid
    leaf3648InnerLogValid leaf3648CoversExact leaf3648LowerChecked

private noncomputable def leaf3649Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (71/32), kHi := (9/4), chiLo := (5/16), chiHi := (21/64) }

private noncomputable def leaf3649Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217913/134217728) }, vSqrt := { lower := (65531/65536), upper := (13743698739/13743276032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (227240217/134217728) }, upper := { exponent := 0, mantissa := (445/256) } }, logOuter := sk78LogOuterCertificate, logK := sk78LogKCertificate, logChi := chi58LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (27486974771/27486552064) } }, logDArg := sk78LogDArgCertificate }

private noncomputable def leaf3649InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3649LocalValidity :
    LeafFacts leaf3649Box leaf3649Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3649Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (13743698739/13743276032) }) = true
      norm_num [leaf3649Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3649CertificateValid :
    WideCertificateValid leaf3649Box leaf3649Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk78ValidityFacts chi58ValidityFacts
    leaf3649LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3649CoverageChecked :
    coverageCheck (innerAD leaf3649Box) leaf3649InnerLog = true := by
  rfl'

private theorem leaf3649InnerLogValid :
    leaf3649InnerLog.Valid 8 (innerAD leaf3649Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3649CoverageChecked

private noncomputable def leaf3649InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629339/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3649InputLogOnePlusV_eq :
    leaf3649InputLogOnePlusV = outerEnclosure 24
      (leaf3649Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3649RoundedFacts : LeafRoundedFacts 8
    leaf3649Certificate.logOnePlusV leaf3649InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3649InputLogOnePlusV_eq }

private noncomputable def leaf3649Inputs : Inputs :=
  inputsOfCaches globalInput sk78RoundedInputs
    chi58InputQChi innerPair64Input
    leaf3649InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3649LowerChecked :
    lowerCheck 24 leaf3649Box leaf3649Inputs = true := by
  rfl'

private theorem leaf3649CoversExact : CoversExact 8
    leaf3649Box leaf3649Certificate leaf3649InnerLog leaf3649Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk78RoundedFacts chi58RoundedFacts
    innerPair64RoundedFacts leaf3649RoundedFacts (by rfl)

private theorem leaf3649FlatSound : Sound leaf3649Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3649CertificateValid
    leaf3649InnerLogValid leaf3649CoversExact leaf3649LowerChecked

private noncomputable def leaf3650Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (71/32), chiLo := (21/64), chiHi := (11/32) }

private noncomputable def leaf3650Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217913/134217728) }, vSqrt := { lower := (65531/65536), upper := (4581232913/4581085184) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (230516817/134217728) }, upper := { exponent := 0, mantissa := (1805/1024) } }, logOuter := sk77LogOuterCertificate, logK := sk77LogKCertificate, logChi := chi59LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (9162318097/9162170368) } }, logDArg := sk77LogDArgCertificate }

private noncomputable def leaf3650InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf3650LocalValidity :
    LeafFacts leaf3650Box leaf3650Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3650Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (4581232913/4581085184) }) = true
      norm_num [leaf3650Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3650CertificateValid :
    WideCertificateValid leaf3650Box leaf3650Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk77ValidityFacts chi59ValidityFacts
    leaf3650LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3650CoverageChecked :
    coverageCheck (innerAD leaf3650Box) leaf3650InnerLog = true := by
  rfl'

private theorem leaf3650InnerLogValid :
    leaf3650InnerLog.Valid 8 (innerAD leaf3650Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf3650CoverageChecked

private noncomputable def leaf3650InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629351/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3650InputLogOnePlusV_eq :
    leaf3650InputLogOnePlusV = outerEnclosure 24
      (leaf3650Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3650RoundedFacts : LeafRoundedFacts 8
    leaf3650Certificate.logOnePlusV leaf3650InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3650InputLogOnePlusV_eq }

private noncomputable def leaf3650Inputs : Inputs :=
  inputsOfCaches globalInput sk77RoundedInputs
    chi59InputQChi innerPair66Input
    leaf3650InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3650LowerChecked :
    lowerCheck 24 leaf3650Box leaf3650Inputs = true := by
  rfl'

private theorem leaf3650CoversExact : CoversExact 8
    leaf3650Box leaf3650Certificate leaf3650InnerLog leaf3650Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk77RoundedFacts chi59RoundedFacts
    innerPair66RoundedFacts leaf3650RoundedFacts (by rfl)

private theorem leaf3650FlatSound : Sound leaf3650Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3650CertificateValid
    leaf3650InnerLogValid leaf3650CoversExact leaf3650LowerChecked

private noncomputable def leaf3651Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (71/32), kHi := (9/4), chiLo := (21/64), chiHi := (11/32) }

private noncomputable def leaf3651Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217915/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716232704) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (231892987/134217728) }, upper := { exponent := 0, mantissa := (227/128) } }, logOuter := sk78LogOuterCertificate, logK := sk78LogKCertificate, logChi := chi59LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434726399/137432465408) } }, logDArg := sk78LogDArgCertificate }

private noncomputable def leaf3651InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf3651LocalValidity :
    LeafFacts leaf3651Box leaf3651Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3651Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716232704) }) = true
      norm_num [leaf3651Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3651CertificateValid :
    WideCertificateValid leaf3651Box leaf3651Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk78ValidityFacts chi59ValidityFacts
    leaf3651LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3651CoverageChecked :
    coverageCheck (innerAD leaf3651Box) leaf3651InnerLog = true := by
  rfl'

private theorem leaf3651InnerLogValid :
    leaf3651InnerLog.Valid 8 (innerAD leaf3651Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf3651CoverageChecked

private noncomputable def leaf3651InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629357/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3651InputLogOnePlusV_eq :
    leaf3651InputLogOnePlusV = outerEnclosure 24
      (leaf3651Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3651RoundedFacts : LeafRoundedFacts 8
    leaf3651Certificate.logOnePlusV leaf3651InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3651InputLogOnePlusV_eq }

private noncomputable def leaf3651Inputs : Inputs :=
  inputsOfCaches globalInput sk78RoundedInputs
    chi59InputQChi innerPair66Input
    leaf3651InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3651LowerChecked :
    lowerCheck 24 leaf3651Box leaf3651Inputs = true := by
  rfl'

private theorem leaf3651CoversExact : CoversExact 8
    leaf3651Box leaf3651Certificate leaf3651InnerLog leaf3651Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk78RoundedFacts chi59RoundedFacts
    innerPair66RoundedFacts leaf3651RoundedFacts (by rfl)

private theorem leaf3651FlatSound : Sound leaf3651Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3651CertificateValid
    leaf3651InnerLogValid leaf3651CoversExact leaf3651LowerChecked

private noncomputable def leaf3652Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (69/32), chiLo := (11/32), chiHi := (23/64) }

private noncomputable def leaf3652Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217911/134217728) }, vSqrt := { lower := (65531/65536), upper := (13743698739/13743245312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (232220651/134217728) }, upper := { exponent := 0, mantissa := (3635/2048) } }, logOuter := sk75LogOuterCertificate, logK := sk75LogKCertificate, logChi := chi60LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (27486944051/27486490624) } }, logDArg := sk75LogDArgCertificate }

private noncomputable def leaf3652InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf3652LocalValidity :
    LeafFacts leaf3652Box leaf3652Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3652Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (13743698739/13743245312) }) = true
      norm_num [leaf3652Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3652CertificateValid :
    WideCertificateValid leaf3652Box leaf3652Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk75ValidityFacts chi60ValidityFacts
    leaf3652LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3652CoverageChecked :
    coverageCheck (innerAD leaf3652Box) leaf3652InnerLog = true := by
  rfl'

private theorem leaf3652InnerLogValid :
    leaf3652InnerLog.Valid 8 (innerAD leaf3652Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf3652CoverageChecked

private noncomputable def leaf3652InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814679/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3652InputLogOnePlusV_eq :
    leaf3652InputLogOnePlusV = outerEnclosure 24
      (leaf3652Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3652RoundedFacts : LeafRoundedFacts 8
    leaf3652Certificate.logOnePlusV leaf3652InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3652InputLogOnePlusV_eq }

private noncomputable def leaf3652Inputs : Inputs :=
  inputsOfCaches globalInput sk75RoundedInputs
    chi60InputQChi innerPair66Input
    leaf3652InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3652LowerChecked :
    lowerCheck 24 leaf3652Box leaf3652Inputs = true := by
  rfl'

private theorem leaf3652CoversExact : CoversExact 8
    leaf3652Box leaf3652Certificate leaf3652InnerLog leaf3652Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk75RoundedFacts chi60RoundedFacts
    innerPair66RoundedFacts leaf3652RoundedFacts (by rfl)

private theorem leaf3652FlatSound : Sound leaf3652Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3652CertificateValid
    leaf3652InnerLogValid leaf3652CoversExact leaf3652LowerChecked

private noncomputable def leaf3653Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (69/32), kHi := (35/16), chiLo := (11/32), chiHi := (23/64) }

private noncomputable def leaf3653Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217913/134217728) }, vSqrt := { lower := (65531/65536), upper := (22906164565/22905393152) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (233662353/134217728) }, upper := { exponent := 0, mantissa := (1829/1024) } }, logOuter := sk76LogOuterCertificate, logK := sk76LogKCertificate, logChi := chi60LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (45811557717/45810786304) } }, logDArg := sk76LogDArgCertificate }

private noncomputable def leaf3653InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf3653LocalValidity :
    LeafFacts leaf3653Box leaf3653Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3653Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (22906164565/22905393152) }) = true
      norm_num [leaf3653Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3653CertificateValid :
    WideCertificateValid leaf3653Box leaf3653Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk76ValidityFacts chi60ValidityFacts
    leaf3653LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3653CoverageChecked :
    coverageCheck (innerAD leaf3653Box) leaf3653InnerLog = true := by
  rfl'

private theorem leaf3653InnerLogValid :
    leaf3653InnerLog.Valid 8 (innerAD leaf3653Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf3653CoverageChecked

private noncomputable def leaf3653InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629363/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3653InputLogOnePlusV_eq :
    leaf3653InputLogOnePlusV = outerEnclosure 24
      (leaf3653Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3653RoundedFacts : LeafRoundedFacts 8
    leaf3653Certificate.logOnePlusV leaf3653InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3653InputLogOnePlusV_eq }

private noncomputable def leaf3653Inputs : Inputs :=
  inputsOfCaches globalInput sk76RoundedInputs
    chi60InputQChi innerPair66Input
    leaf3653InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3653LowerChecked :
    lowerCheck 24 leaf3653Box leaf3653Inputs = true := by
  rfl'

private theorem leaf3653CoversExact : CoversExact 8
    leaf3653Box leaf3653Certificate leaf3653InnerLog leaf3653Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk76RoundedFacts chi60RoundedFacts
    innerPair66RoundedFacts leaf3653RoundedFacts (by rfl)

private theorem leaf3653FlatSound : Sound leaf3653Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3653CertificateValid
    leaf3653InnerLogValid leaf3653CoversExact leaf3653LowerChecked

private noncomputable def leaf3654Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (69/32), chiLo := (23/64), chiHi := (3/8) }

private noncomputable def leaf3654Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217913/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716085248) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (236676825/134217728) }, upper := { exponent := 0, mantissa := (463/256) } }, logOuter := sk75LogOuterCertificate, logK := sk75LogKCertificate, logChi := chi61LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434578943/137432170496) } }, logDArg := sk75LogDArgCertificate }

private noncomputable def leaf3654InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3654LocalValidity :
    LeafFacts leaf3654Box leaf3654Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3654Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716085248) }) = true
      norm_num [leaf3654Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3654CertificateValid :
    WideCertificateValid leaf3654Box leaf3654Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk75ValidityFacts chi61ValidityFacts
    leaf3654LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3654CoverageChecked :
    coverageCheck (innerAD leaf3654Box) leaf3654InnerLog = true := by
  rfl'

private theorem leaf3654InnerLogValid :
    leaf3654InnerLog.Valid 8 (innerAD leaf3654Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3654CoverageChecked

private noncomputable def leaf3654InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629375/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3654InputLogOnePlusV_eq :
    leaf3654InputLogOnePlusV = outerEnclosure 24
      (leaf3654Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3654RoundedFacts : LeafRoundedFacts 8
    leaf3654Certificate.logOnePlusV leaf3654InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3654InputLogOnePlusV_eq }

private noncomputable def leaf3654Inputs : Inputs :=
  inputsOfCaches globalInput sk75RoundedInputs
    chi61InputQChi innerPair71Input
    leaf3654InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3654LowerChecked :
    lowerCheck 24 leaf3654Box leaf3654Inputs = true := by
  rfl'

private theorem leaf3654CoversExact : CoversExact 8
    leaf3654Box leaf3654Certificate leaf3654InnerLog leaf3654Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk75RoundedFacts chi61RoundedFacts
    innerPair71RoundedFacts leaf3654RoundedFacts (by rfl)

private theorem leaf3654FlatSound : Sound leaf3654Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3654CertificateValid
    leaf3654InnerLogValid leaf3654CoversExact leaf3654LowerChecked

private noncomputable def leaf3655Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (69/32), kHi := (35/16), chiLo := (23/64), chiHi := (3/8) }

private noncomputable def leaf3655Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217915/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716036096) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (238184059/134217728) }, upper := { exponent := 0, mantissa := (233/128) } }, logOuter := sk76LogOuterCertificate, logK := sk76LogKCertificate, logChi := chi61LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434529791/137432072192) } }, logDArg := sk76LogDArgCertificate }

private noncomputable def leaf3655InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf3655LocalValidity :
    LeafFacts leaf3655Box leaf3655Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3655Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716036096) }) = true
      norm_num [leaf3655Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3655CertificateValid :
    WideCertificateValid leaf3655Box leaf3655Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk76ValidityFacts chi61ValidityFacts
    leaf3655LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3655CoverageChecked :
    coverageCheck (innerAD leaf3655Box) leaf3655InnerLog = true := by
  rfl'

private theorem leaf3655InnerLogValid :
    leaf3655InnerLog.Valid 8 (innerAD leaf3655Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf3655CoverageChecked

private noncomputable def leaf3655InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629381/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3655InputLogOnePlusV_eq :
    leaf3655InputLogOnePlusV = outerEnclosure 24
      (leaf3655Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3655RoundedFacts : LeafRoundedFacts 8
    leaf3655Certificate.logOnePlusV leaf3655InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3655InputLogOnePlusV_eq }

private noncomputable def leaf3655Inputs : Inputs :=
  inputsOfCaches globalInput sk76RoundedInputs
    chi61InputQChi innerPair72Input
    leaf3655InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3655LowerChecked :
    lowerCheck 24 leaf3655Box leaf3655Inputs = true := by
  rfl'

private theorem leaf3655CoversExact : CoversExact 8
    leaf3655Box leaf3655Certificate leaf3655InnerLog leaf3655Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk76RoundedFacts chi61RoundedFacts
    innerPair72RoundedFacts leaf3655RoundedFacts (by rfl)

private theorem leaf3655FlatSound : Sound leaf3655Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3655CertificateValid
    leaf3655InnerLogValid leaf3655CoversExact leaf3655LowerChecked

private noncomputable def leaf3656Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (71/32), chiLo := (11/32), chiHi := (23/64) }

private noncomputable def leaf3656Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217915/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716132352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (235104055/134217728) }, upper := { exponent := 0, mantissa := (3681/2048) } }, logOuter := sk77LogOuterCertificate, logK := sk77LogKCertificate, logChi := chi60LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434626047/137432264704) } }, logDArg := sk77LogDArgCertificate }

private noncomputable def leaf3656InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3656LocalValidity :
    LeafFacts leaf3656Box leaf3656Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3656Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716132352) }) = true
      norm_num [leaf3656Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3656CertificateValid :
    WideCertificateValid leaf3656Box leaf3656Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk77ValidityFacts chi60ValidityFacts
    leaf3656LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3656CoverageChecked :
    coverageCheck (innerAD leaf3656Box) leaf3656InnerLog = true := by
  rfl'

private theorem leaf3656InnerLogValid :
    leaf3656InnerLog.Valid 8 (innerAD leaf3656Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3656CoverageChecked

private noncomputable def leaf3656InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629369/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3656InputLogOnePlusV_eq :
    leaf3656InputLogOnePlusV = outerEnclosure 24
      (leaf3656Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3656RoundedFacts : LeafRoundedFacts 8
    leaf3656Certificate.logOnePlusV leaf3656InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3656InputLogOnePlusV_eq }

private noncomputable def leaf3656Inputs : Inputs :=
  inputsOfCaches globalInput sk77RoundedInputs
    chi60InputQChi innerPair71Input
    leaf3656InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3656LowerChecked :
    lowerCheck 24 leaf3656Box leaf3656Inputs = true := by
  rfl'

private theorem leaf3656CoversExact : CoversExact 8
    leaf3656Box leaf3656Certificate leaf3656InnerLog leaf3656Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk77RoundedFacts chi60RoundedFacts
    innerPair71RoundedFacts leaf3656RoundedFacts (by rfl)

private theorem leaf3656FlatSound : Sound leaf3656Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3656CertificateValid
    leaf3656InnerLogValid leaf3656CoversExact leaf3656LowerChecked

private noncomputable def leaf3657Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (71/32), kHi := (9/4), chiLo := (11/32), chiHi := (23/64) }

private noncomputable def leaf3657Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217917/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716085248) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (236545757/134217728) }, upper := { exponent := 0, mantissa := (463/256) } }, logOuter := sk78LogOuterCertificate, logK := sk78LogKCertificate, logChi := chi60LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434578943/137432170496) } }, logDArg := sk78LogDArgCertificate }

private noncomputable def leaf3657InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3657LocalValidity :
    LeafFacts leaf3657Box leaf3657Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3657Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716085248) }) = true
      norm_num [leaf3657Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3657CertificateValid :
    WideCertificateValid leaf3657Box leaf3657Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk78ValidityFacts chi60ValidityFacts
    leaf3657LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3657CoverageChecked :
    coverageCheck (innerAD leaf3657Box) leaf3657InnerLog = true := by
  rfl'

private theorem leaf3657InnerLogValid :
    leaf3657InnerLog.Valid 8 (innerAD leaf3657Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3657CoverageChecked

private noncomputable def leaf3657InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629375/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3657InputLogOnePlusV_eq :
    leaf3657InputLogOnePlusV = outerEnclosure 24
      (leaf3657Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3657RoundedFacts : LeafRoundedFacts 8
    leaf3657Certificate.logOnePlusV leaf3657InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3657InputLogOnePlusV_eq }

private noncomputable def leaf3657Inputs : Inputs :=
  inputsOfCaches globalInput sk78RoundedInputs
    chi60InputQChi innerPair71Input
    leaf3657InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3657LowerChecked :
    lowerCheck 24 leaf3657Box leaf3657Inputs = true := by
  rfl'

private theorem leaf3657CoversExact : CoversExact 8
    leaf3657Box leaf3657Certificate leaf3657InnerLog leaf3657Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk78RoundedFacts chi60RoundedFacts
    innerPair71RoundedFacts leaf3657RoundedFacts (by rfl)

private theorem leaf3657FlatSound : Sound leaf3657Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3657CertificateValid
    leaf3657InnerLogValid leaf3657CoversExact leaf3657LowerChecked

private noncomputable def leaf3658Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (71/32), chiLo := (23/64), chiHi := (3/8) }

private noncomputable def leaf3658Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217917/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68715986944) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (239691293/134217728) }, upper := { exponent := 0, mantissa := (469/256) } }, logOuter := sk77LogOuterCertificate, logK := sk77LogKCertificate, logChi := chi61LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434480639/137431973888) } }, logDArg := sk77LogDArgCertificate }

private noncomputable def leaf3658InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf3658LocalValidity :
    LeafFacts leaf3658Box leaf3658Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3658Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68715986944) }) = true
      norm_num [leaf3658Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3658CertificateValid :
    WideCertificateValid leaf3658Box leaf3658Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk77ValidityFacts chi61ValidityFacts
    leaf3658LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3658CoverageChecked :
    coverageCheck (innerAD leaf3658Box) leaf3658InnerLog = true := by
  rfl'

private theorem leaf3658InnerLogValid :
    leaf3658InnerLog.Valid 8 (innerAD leaf3658Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf3658CoverageChecked

private noncomputable def leaf3658InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629387/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3658InputLogOnePlusV_eq :
    leaf3658InputLogOnePlusV = outerEnclosure 24
      (leaf3658Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3658RoundedFacts : LeafRoundedFacts 8
    leaf3658Certificate.logOnePlusV leaf3658InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3658InputLogOnePlusV_eq }

private noncomputable def leaf3658Inputs : Inputs :=
  inputsOfCaches globalInput sk77RoundedInputs
    chi61InputQChi innerPair72Input
    leaf3658InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3658LowerChecked :
    lowerCheck 24 leaf3658Box leaf3658Inputs = true := by
  rfl'

private theorem leaf3658CoversExact : CoversExact 8
    leaf3658Box leaf3658Certificate leaf3658InnerLog leaf3658Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk77RoundedFacts chi61RoundedFacts
    innerPair72RoundedFacts leaf3658RoundedFacts (by rfl)

private theorem leaf3658FlatSound : Sound leaf3658Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3658CertificateValid
    leaf3658InnerLogValid leaf3658CoversExact leaf3658LowerChecked

private noncomputable def leaf3659Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (71/32), kHi := (9/4), chiLo := (23/64), chiHi := (3/8) }

private noncomputable def leaf3659Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217919/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68715937792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (241198527/134217728) }, upper := { exponent := 0, mantissa := (59/32) } }, logOuter := sk78LogOuterCertificate, logK := sk78LogKCertificate, logChi := chi61LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434431487/137431875584) } }, logDArg := sk78LogDArgCertificate }

private noncomputable def leaf3659InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf3659LocalValidity :
    LeafFacts leaf3659Box leaf3659Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3659Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68715937792) }) = true
      norm_num [leaf3659Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3659CertificateValid :
    WideCertificateValid leaf3659Box leaf3659Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk78ValidityFacts chi61ValidityFacts
    leaf3659LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3659CoverageChecked :
    coverageCheck (innerAD leaf3659Box) leaf3659InnerLog = true := by
  rfl'

private theorem leaf3659InnerLogValid :
    leaf3659InnerLog.Valid 8 (innerAD leaf3659Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf3659CoverageChecked

private noncomputable def leaf3659InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629393/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3659InputLogOnePlusV_eq :
    leaf3659InputLogOnePlusV = outerEnclosure 24
      (leaf3659Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3659RoundedFacts : LeafRoundedFacts 8
    leaf3659Certificate.logOnePlusV leaf3659InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3659InputLogOnePlusV_eq }

private noncomputable def leaf3659Inputs : Inputs :=
  inputsOfCaches globalInput sk78RoundedInputs
    chi61InputQChi innerPair72Input
    leaf3659InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3659LowerChecked :
    lowerCheck 24 leaf3659Box leaf3659Inputs = true := by
  rfl'

private theorem leaf3659CoversExact : CoversExact 8
    leaf3659Box leaf3659Certificate leaf3659InnerLog leaf3659Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk78RoundedFacts chi61RoundedFacts
    innerPair72RoundedFacts leaf3659RoundedFacts (by rfl)

private theorem leaf3659FlatSound : Sound leaf3659Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3659CertificateValid
    leaf3659InnerLogValid leaf3659CoversExact leaf3659LowerChecked

private noncomputable def component74Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component74Node0_sound : Sound component74Node0Box :=
  sound_of_literal_split component74Node0Box leaf3596Box leaf3597Box
    .k (65/32) (by rfl) (by rfl)
    leaf3596FlatSound leaf3597FlatSound

private noncomputable def component74Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component74Node1_sound : Sound component74Node1Box :=
  sound_of_literal_split component74Node1Box leaf3598Box leaf3599Box
    .k (65/32) (by rfl) (by rfl)
    leaf3598FlatSound leaf3599FlatSound

private noncomputable def component74Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (1/4), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component74Node2_sound : Sound component74Node2Box :=
  sound_of_literal_split component74Node2Box component74Node0Box component74Node1Box
    .chi (17/64) (by rfl) (by rfl)
    component74Node0_sound component74Node1_sound

private noncomputable def component74Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component74Node3_sound : Sound component74Node3Box :=
  sound_of_literal_split component74Node3Box leaf3600Box leaf3601Box
    .k (67/32) (by rfl) (by rfl)
    leaf3600FlatSound leaf3601FlatSound

private noncomputable def component74Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component74Node4_sound : Sound component74Node4Box :=
  sound_of_literal_split component74Node4Box leaf3602Box leaf3603Box
    .k (67/32) (by rfl) (by rfl)
    leaf3602FlatSound leaf3603FlatSound

private noncomputable def component74Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (1/4), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component74Node5_sound : Sound component74Node5Box :=
  sound_of_literal_split component74Node5Box component74Node3Box component74Node4Box
    .chi (17/64) (by rfl) (by rfl)
    component74Node3_sound component74Node4_sound

private noncomputable def component74Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (17/8), chiLo := (1/4), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component74Node6_sound : Sound component74Node6Box :=
  sound_of_literal_split component74Node6Box component74Node2Box component74Node5Box
    .k (33/16) (by rfl) (by rfl)
    component74Node2_sound component74Node5_sound

private noncomputable def component74Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component74Node7_sound : Sound component74Node7Box :=
  sound_of_literal_split component74Node7Box leaf3604Box leaf3605Box
    .k (65/32) (by rfl) (by rfl)
    leaf3604FlatSound leaf3605FlatSound

private noncomputable def component74Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (19/64), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component74Node8_sound : Sound component74Node8Box :=
  sound_of_literal_split component74Node8Box leaf3606Box leaf3607Box
    .k (65/32) (by rfl) (by rfl)
    leaf3606FlatSound leaf3607FlatSound

private noncomputable def component74Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (9/32), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component74Node9_sound : Sound component74Node9Box :=
  sound_of_literal_split component74Node9Box component74Node7Box component74Node8Box
    .chi (19/64) (by rfl) (by rfl)
    component74Node7_sound component74Node8_sound

private noncomputable def component74Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component74Node10_sound : Sound component74Node10Box :=
  sound_of_literal_split component74Node10Box leaf3608Box leaf3609Box
    .k (67/32) (by rfl) (by rfl)
    leaf3608FlatSound leaf3609FlatSound

private noncomputable def component74Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (19/64), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component74Node11_sound : Sound component74Node11Box :=
  sound_of_literal_split component74Node11Box leaf3610Box leaf3611Box
    .k (67/32) (by rfl) (by rfl)
    leaf3610FlatSound leaf3611FlatSound

private noncomputable def component74Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (9/32), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component74Node12_sound : Sound component74Node12Box :=
  sound_of_literal_split component74Node12Box component74Node10Box component74Node11Box
    .chi (19/64) (by rfl) (by rfl)
    component74Node10_sound component74Node11_sound

private noncomputable def component74Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (17/8), chiLo := (9/32), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component74Node13_sound : Sound component74Node13Box :=
  sound_of_literal_split component74Node13Box component74Node9Box component74Node12Box
    .k (33/16) (by rfl) (by rfl)
    component74Node9_sound component74Node12_sound

private noncomputable def component74Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (17/8), chiLo := (1/4), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component74Node14_sound : Sound component74Node14Box :=
  sound_of_literal_split component74Node14Box component74Node6Box component74Node13Box
    .chi (9/32) (by rfl) (by rfl)
    component74Node6_sound component74Node13_sound

private noncomputable def component74Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component74Node15_sound : Sound component74Node15Box :=
  sound_of_literal_split component74Node15Box leaf3612Box leaf3613Box
    .k (69/32) (by rfl) (by rfl)
    leaf3612FlatSound leaf3613FlatSound

private noncomputable def component74Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component74Node16_sound : Sound component74Node16Box :=
  sound_of_literal_split component74Node16Box leaf3614Box leaf3615Box
    .k (69/32) (by rfl) (by rfl)
    leaf3614FlatSound leaf3615FlatSound

private noncomputable def component74Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (1/4), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component74Node17_sound : Sound component74Node17Box :=
  sound_of_literal_split component74Node17Box component74Node15Box component74Node16Box
    .chi (17/64) (by rfl) (by rfl)
    component74Node15_sound component74Node16_sound

private noncomputable def component74Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component74Node18_sound : Sound component74Node18Box :=
  sound_of_literal_split component74Node18Box leaf3616Box leaf3617Box
    .k (71/32) (by rfl) (by rfl)
    leaf3616FlatSound leaf3617FlatSound

private noncomputable def component74Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component74Node19_sound : Sound component74Node19Box :=
  sound_of_literal_split component74Node19Box leaf3618Box leaf3619Box
    .k (71/32) (by rfl) (by rfl)
    leaf3618FlatSound leaf3619FlatSound

private noncomputable def component74Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (1/4), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component74Node20_sound : Sound component74Node20Box :=
  sound_of_literal_split component74Node20Box component74Node18Box component74Node19Box
    .chi (17/64) (by rfl) (by rfl)
    component74Node18_sound component74Node19_sound

private noncomputable def component74Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (1/4), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component74Node21_sound : Sound component74Node21Box :=
  sound_of_literal_split component74Node21Box component74Node17Box component74Node20Box
    .k (35/16) (by rfl) (by rfl)
    component74Node17_sound component74Node20_sound

private noncomputable def component74Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component74Node22_sound : Sound component74Node22Box :=
  sound_of_literal_split component74Node22Box leaf3620Box leaf3621Box
    .k (69/32) (by rfl) (by rfl)
    leaf3620FlatSound leaf3621FlatSound

private noncomputable def component74Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (19/64), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component74Node23_sound : Sound component74Node23Box :=
  sound_of_literal_split component74Node23Box leaf3622Box leaf3623Box
    .k (69/32) (by rfl) (by rfl)
    leaf3622FlatSound leaf3623FlatSound

private noncomputable def component74Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (9/32), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component74Node24_sound : Sound component74Node24Box :=
  sound_of_literal_split component74Node24Box component74Node22Box component74Node23Box
    .chi (19/64) (by rfl) (by rfl)
    component74Node22_sound component74Node23_sound

private noncomputable def component74Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component74Node25_sound : Sound component74Node25Box :=
  sound_of_literal_split component74Node25Box leaf3624Box leaf3625Box
    .k (71/32) (by rfl) (by rfl)
    leaf3624FlatSound leaf3625FlatSound

private noncomputable def component74Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (19/64), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component74Node26_sound : Sound component74Node26Box :=
  sound_of_literal_split component74Node26Box leaf3626Box leaf3627Box
    .k (71/32) (by rfl) (by rfl)
    leaf3626FlatSound leaf3627FlatSound

private noncomputable def component74Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (9/32), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component74Node27_sound : Sound component74Node27Box :=
  sound_of_literal_split component74Node27Box component74Node25Box component74Node26Box
    .chi (19/64) (by rfl) (by rfl)
    component74Node25_sound component74Node26_sound

private noncomputable def component74Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (9/32), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component74Node28_sound : Sound component74Node28Box :=
  sound_of_literal_split component74Node28Box component74Node24Box component74Node27Box
    .k (35/16) (by rfl) (by rfl)
    component74Node24_sound component74Node27_sound

private noncomputable def component74Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (1/4), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component74Node29_sound : Sound component74Node29Box :=
  sound_of_literal_split component74Node29Box component74Node21Box component74Node28Box
    .chi (9/32) (by rfl) (by rfl)
    component74Node21_sound component74Node28_sound

private noncomputable def component74Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (9/4), chiLo := (1/4), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component74Node30_sound : Sound component74Node30Box :=
  sound_of_literal_split component74Node30Box component74Node14Box component74Node29Box
    .k (17/8) (by rfl) (by rfl)
    component74Node14_sound component74Node29_sound

private noncomputable def component74Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (5/16), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component74Node31_sound : Sound component74Node31Box :=
  sound_of_literal_split component74Node31Box leaf3628Box leaf3629Box
    .k (65/32) (by rfl) (by rfl)
    leaf3628FlatSound leaf3629FlatSound

private noncomputable def component74Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (21/64), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component74Node32_sound : Sound component74Node32Box :=
  sound_of_literal_split component74Node32Box leaf3630Box leaf3631Box
    .k (65/32) (by rfl) (by rfl)
    leaf3630FlatSound leaf3631FlatSound

private noncomputable def component74Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (5/16), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component74Node33_sound : Sound component74Node33Box :=
  sound_of_literal_split component74Node33Box component74Node31Box component74Node32Box
    .chi (21/64) (by rfl) (by rfl)
    component74Node31_sound component74Node32_sound

private noncomputable def component74Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (5/16), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component74Node34_sound : Sound component74Node34Box :=
  sound_of_literal_split component74Node34Box leaf3632Box leaf3633Box
    .k (67/32) (by rfl) (by rfl)
    leaf3632FlatSound leaf3633FlatSound

private noncomputable def component74Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (21/64), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component74Node35_sound : Sound component74Node35Box :=
  sound_of_literal_split component74Node35Box leaf3634Box leaf3635Box
    .k (67/32) (by rfl) (by rfl)
    leaf3634FlatSound leaf3635FlatSound

private noncomputable def component74Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (5/16), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component74Node36_sound : Sound component74Node36Box :=
  sound_of_literal_split component74Node36Box component74Node34Box component74Node35Box
    .chi (21/64) (by rfl) (by rfl)
    component74Node34_sound component74Node35_sound

private noncomputable def component74Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (17/8), chiLo := (5/16), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component74Node37_sound : Sound component74Node37Box :=
  sound_of_literal_split component74Node37Box component74Node33Box component74Node36Box
    .k (33/16) (by rfl) (by rfl)
    component74Node33_sound component74Node36_sound

private noncomputable def component74Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (11/32), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component74Node38_sound : Sound component74Node38Box :=
  sound_of_literal_split component74Node38Box leaf3636Box leaf3637Box
    .k (65/32) (by rfl) (by rfl)
    leaf3636FlatSound leaf3637FlatSound

private noncomputable def component74Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (23/64), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component74Node39_sound : Sound component74Node39Box :=
  sound_of_literal_split component74Node39Box leaf3638Box leaf3639Box
    .k (65/32) (by rfl) (by rfl)
    leaf3638FlatSound leaf3639FlatSound

private noncomputable def component74Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (11/32), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component74Node40_sound : Sound component74Node40Box :=
  sound_of_literal_split component74Node40Box component74Node38Box component74Node39Box
    .chi (23/64) (by rfl) (by rfl)
    component74Node38_sound component74Node39_sound

private noncomputable def component74Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (11/32), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component74Node41_sound : Sound component74Node41Box :=
  sound_of_literal_split component74Node41Box leaf3640Box leaf3641Box
    .k (67/32) (by rfl) (by rfl)
    leaf3640FlatSound leaf3641FlatSound

private noncomputable def component74Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (23/64), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component74Node42_sound : Sound component74Node42Box :=
  sound_of_literal_split component74Node42Box leaf3642Box leaf3643Box
    .k (67/32) (by rfl) (by rfl)
    leaf3642FlatSound leaf3643FlatSound

private noncomputable def component74Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (11/32), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component74Node43_sound : Sound component74Node43Box :=
  sound_of_literal_split component74Node43Box component74Node41Box component74Node42Box
    .chi (23/64) (by rfl) (by rfl)
    component74Node41_sound component74Node42_sound

private noncomputable def component74Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (17/8), chiLo := (11/32), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component74Node44_sound : Sound component74Node44Box :=
  sound_of_literal_split component74Node44Box component74Node40Box component74Node43Box
    .k (33/16) (by rfl) (by rfl)
    component74Node40_sound component74Node43_sound

private noncomputable def component74Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (17/8), chiLo := (5/16), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component74Node45_sound : Sound component74Node45Box :=
  sound_of_literal_split component74Node45Box component74Node37Box component74Node44Box
    .chi (11/32) (by rfl) (by rfl)
    component74Node37_sound component74Node44_sound

private noncomputable def component74Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (5/16), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component74Node46_sound : Sound component74Node46Box :=
  sound_of_literal_split component74Node46Box leaf3644Box leaf3645Box
    .k (69/32) (by rfl) (by rfl)
    leaf3644FlatSound leaf3645FlatSound

private noncomputable def component74Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (21/64), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component74Node47_sound : Sound component74Node47Box :=
  sound_of_literal_split component74Node47Box leaf3646Box leaf3647Box
    .k (69/32) (by rfl) (by rfl)
    leaf3646FlatSound leaf3647FlatSound

private noncomputable def component74Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (5/16), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component74Node48_sound : Sound component74Node48Box :=
  sound_of_literal_split component74Node48Box component74Node46Box component74Node47Box
    .chi (21/64) (by rfl) (by rfl)
    component74Node46_sound component74Node47_sound

private noncomputable def component74Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (5/16), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component74Node49_sound : Sound component74Node49Box :=
  sound_of_literal_split component74Node49Box leaf3648Box leaf3649Box
    .k (71/32) (by rfl) (by rfl)
    leaf3648FlatSound leaf3649FlatSound

private noncomputable def component74Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (21/64), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component74Node50_sound : Sound component74Node50Box :=
  sound_of_literal_split component74Node50Box leaf3650Box leaf3651Box
    .k (71/32) (by rfl) (by rfl)
    leaf3650FlatSound leaf3651FlatSound

private noncomputable def component74Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (5/16), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component74Node51_sound : Sound component74Node51Box :=
  sound_of_literal_split component74Node51Box component74Node49Box component74Node50Box
    .chi (21/64) (by rfl) (by rfl)
    component74Node49_sound component74Node50_sound

private noncomputable def component74Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (5/16), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component74Node52_sound : Sound component74Node52Box :=
  sound_of_literal_split component74Node52Box component74Node48Box component74Node51Box
    .k (35/16) (by rfl) (by rfl)
    component74Node48_sound component74Node51_sound

private noncomputable def component74Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (11/32), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component74Node53_sound : Sound component74Node53Box :=
  sound_of_literal_split component74Node53Box leaf3652Box leaf3653Box
    .k (69/32) (by rfl) (by rfl)
    leaf3652FlatSound leaf3653FlatSound

private noncomputable def component74Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (23/64), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component74Node54_sound : Sound component74Node54Box :=
  sound_of_literal_split component74Node54Box leaf3654Box leaf3655Box
    .k (69/32) (by rfl) (by rfl)
    leaf3654FlatSound leaf3655FlatSound

private noncomputable def component74Node55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (11/32), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component74Node55_sound : Sound component74Node55Box :=
  sound_of_literal_split component74Node55Box component74Node53Box component74Node54Box
    .chi (23/64) (by rfl) (by rfl)
    component74Node53_sound component74Node54_sound

private noncomputable def component74Node56Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (11/32), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component74Node56_sound : Sound component74Node56Box :=
  sound_of_literal_split component74Node56Box leaf3656Box leaf3657Box
    .k (71/32) (by rfl) (by rfl)
    leaf3656FlatSound leaf3657FlatSound

private noncomputable def component74Node57Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (23/64), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component74Node57_sound : Sound component74Node57Box :=
  sound_of_literal_split component74Node57Box leaf3658Box leaf3659Box
    .k (71/32) (by rfl) (by rfl)
    leaf3658FlatSound leaf3659FlatSound

private noncomputable def component74Node58Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (11/32), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component74Node58_sound : Sound component74Node58Box :=
  sound_of_literal_split component74Node58Box component74Node56Box component74Node57Box
    .chi (23/64) (by rfl) (by rfl)
    component74Node56_sound component74Node57_sound

private noncomputable def component74Node59Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (11/32), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component74Node59_sound : Sound component74Node59Box :=
  sound_of_literal_split component74Node59Box component74Node55Box component74Node58Box
    .k (35/16) (by rfl) (by rfl)
    component74Node55_sound component74Node58_sound

private noncomputable def component74Node60Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (5/16), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component74Node60_sound : Sound component74Node60Box :=
  sound_of_literal_split component74Node60Box component74Node52Box component74Node59Box
    .chi (11/32) (by rfl) (by rfl)
    component74Node52_sound component74Node59_sound

private noncomputable def component74Node61Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (9/4), chiLo := (5/16), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component74Node61_sound : Sound component74Node61Box :=
  sound_of_literal_split component74Node61Box component74Node45Box component74Node60Box
    .k (17/8) (by rfl) (by rfl)
    component74Node45_sound component74Node60_sound

noncomputable def component74Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (9/4), chiLo := (1/4), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
theorem component74_sound : Sound component74Box :=
  sound_of_literal_split component74Box component74Node30Box component74Node61Box
    .chi (5/16) (by rfl) (by rfl)
    component74Node30_sound component74Node61_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
