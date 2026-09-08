import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch1
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

private noncomputable def leaf4497Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (9/32), chiHi := (73/256) }

private noncomputable def leaf4497Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871267/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715552256) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1027541407/536870912) }, upper := { exponent := 0, mantissa := (15857/8192) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi281LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434045951/137431104512) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf4497InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4497LocalValidity :
    LeafFacts leaf4497Box leaf4497Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4497Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715552256) }) = true
      norm_num [leaf4497Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4497CertificateValid :
    WideCertificateValid leaf4497Box leaf4497Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi281ValidityFacts
    leaf4497LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4497CoverageChecked :
    coverageCheck (innerAD leaf4497Box) leaf4497InnerLog = true := by
  rfl'

private theorem leaf4497InnerLogValid :
    leaf4497InnerLog.Valid 8 (innerAD leaf4497Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4497CoverageChecked

private noncomputable def leaf4497InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (90855/131072) }

set_option maxRecDepth 1000000 in
private theorem leaf4497InputLogOnePlusV_eq :
    leaf4497InputLogOnePlusV = outerEnclosure 24
      (leaf4497Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4497RoundedFacts : LeafRoundedFacts 8
    leaf4497Certificate.logOnePlusV leaf4497InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4497InputLogOnePlusV_eq }

private noncomputable def leaf4497Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi281InputQChi innerPair100Input
    leaf4497InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4497LowerChecked :
    lowerCheck 24 leaf4497Box leaf4497Inputs = true := by
  rfl'

private theorem leaf4497CoversExact : CoversExact 8
    leaf4497Box leaf4497Certificate leaf4497InnerLog leaf4497Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi281RoundedFacts
    innerPair100RoundedFacts leaf4497RoundedFacts (by rfl)

private theorem leaf4497FlatSound : Sound leaf4497Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4497CertificateValid
    leaf4497InnerLogValid leaf4497CoversExact leaf4497LowerChecked

private noncomputable def leaf4498Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (73/256), chiHi := (37/128) }

private noncomputable def leaf4498Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871269/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715498496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1034356733/536870912) }, upper := { exponent := 0, mantissa := (7981/4096) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi282LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137433992191/137430996992) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf4498InnerLog : WideLogData :=
  innerPair304Data

set_option maxRecDepth 1000000 in
private theorem leaf4498LocalValidity :
    LeafFacts leaf4498Box leaf4498Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4498Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715498496) }) = true
      norm_num [leaf4498Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4498CertificateValid :
    WideCertificateValid leaf4498Box leaf4498Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi282ValidityFacts
    leaf4498LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4498CoverageChecked :
    coverageCheck (innerAD leaf4498Box) leaf4498InnerLog = true := by
  rfl'

private theorem leaf4498InnerLogValid :
    leaf4498InnerLog.Valid 8 (innerAD leaf4498Box) :=
  wideLogDataValid_of_cachedCheck endpoint81PositiveFacts
    endpoint71PositiveFacts.valid leaf4498CoverageChecked

private noncomputable def leaf4498InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814723/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4498InputLogOnePlusV_eq :
    leaf4498InputLogOnePlusV = outerEnclosure 24
      (leaf4498Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4498RoundedFacts : LeafRoundedFacts 8
    leaf4498Certificate.logOnePlusV leaf4498InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4498InputLogOnePlusV_eq }

private noncomputable def leaf4498Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi282InputQChi innerPair304Input
    leaf4498InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4498LowerChecked :
    lowerCheck 24 leaf4498Box leaf4498Inputs = true := by
  rfl'

private theorem leaf4498CoversExact : CoversExact 8
    leaf4498Box leaf4498Certificate leaf4498InnerLog leaf4498Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi282RoundedFacts
    innerPair304RoundedFacts leaf4498RoundedFacts (by rfl)

private theorem leaf4498FlatSound : Sound leaf4498Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4498CertificateValid
    leaf4498InnerLogValid leaf4498CoversExact leaf4498LowerChecked

private noncomputable def leaf4499Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (9/32), chiHi := (73/256) }

private noncomputable def leaf4499Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871269/536870912) }, vSqrt := { lower := (65529/65536), upper := (13743698739/13743102976) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1032259709/536870912) }, upper := { exponent := 0, mantissa := (7965/4096) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi281LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (27486801715/27486205952) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf4499InnerLog : WideLogData :=
  innerPair304Data

set_option maxRecDepth 1000000 in
private theorem leaf4499LocalValidity :
    LeafFacts leaf4499Box leaf4499Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4499Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (13743698739/13743102976) }) = true
      norm_num [leaf4499Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4499CertificateValid :
    WideCertificateValid leaf4499Box leaf4499Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi281ValidityFacts
    leaf4499LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4499CoverageChecked :
    coverageCheck (innerAD leaf4499Box) leaf4499InnerLog = true := by
  rfl'

private theorem leaf4499InnerLogValid :
    leaf4499InnerLog.Valid 8 (innerAD leaf4499Box) :=
  wideLogDataValid_of_cachedCheck endpoint81PositiveFacts
    endpoint71PositiveFacts.valid leaf4499CoverageChecked

private noncomputable def leaf4499InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907361/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4499InputLogOnePlusV_eq :
    leaf4499InputLogOnePlusV = outerEnclosure 24
      (leaf4499Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4499RoundedFacts : LeafRoundedFacts 8
    leaf4499Certificate.logOnePlusV leaf4499InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4499InputLogOnePlusV_eq }

private noncomputable def leaf4499Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi281InputQChi innerPair304Input
    leaf4499InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4499LowerChecked :
    lowerCheck 24 leaf4499Box leaf4499Inputs = true := by
  rfl'

private theorem leaf4499CoversExact : CoversExact 8
    leaf4499Box leaf4499Certificate leaf4499InnerLog leaf4499Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi281RoundedFacts
    innerPair304RoundedFacts leaf4499RoundedFacts (by rfl)

private theorem leaf4499FlatSound : Sound leaf4499Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4499CertificateValid
    leaf4499InnerLogValid leaf4499CoversExact leaf4499LowerChecked

private noncomputable def leaf4500Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (73/256), chiHi := (37/128) }

private noncomputable def leaf4500Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871271/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905153536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1039140567/536870912) }, upper := { exponent := 0, mantissa := (4009/2048) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi282LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811318101/45810307072) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf4500InnerLog : WideLogData :=
  innerPair306Data

set_option maxRecDepth 1000000 in
private theorem leaf4500LocalValidity :
    LeafFacts leaf4500Box leaf4500Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4500Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905153536) }) = true
      norm_num [leaf4500Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4500CertificateValid :
    WideCertificateValid leaf4500Box leaf4500Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi282ValidityFacts
    leaf4500LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4500CoverageChecked :
    coverageCheck (innerAD leaf4500Box) leaf4500InnerLog = true := by
  rfl'

private theorem leaf4500InnerLogValid :
    leaf4500InnerLog.Valid 8 (innerAD leaf4500Box) :=
  wideLogDataValid_of_cachedCheck endpoint81PositiveFacts
    endpoint85PositiveFacts.valid leaf4500CoverageChecked

private noncomputable def leaf4500InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629451/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4500InputLogOnePlusV_eq :
    leaf4500InputLogOnePlusV = outerEnclosure 24
      (leaf4500Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4500RoundedFacts : LeafRoundedFacts 8
    leaf4500Certificate.logOnePlusV leaf4500InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4500InputLogOnePlusV_eq }

private noncomputable def leaf4500Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi282InputQChi innerPair306Input
    leaf4500InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4500LowerChecked :
    lowerCheck 24 leaf4500Box leaf4500Inputs = true := by
  rfl'

private theorem leaf4500CoversExact : CoversExact 8
    leaf4500Box leaf4500Certificate leaf4500InnerLog leaf4500Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi282RoundedFacts
    innerPair306RoundedFacts leaf4500RoundedFacts (by rfl)

private theorem leaf4500FlatSound : Sound leaf4500Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4500CertificateValid
    leaf4500InnerLogValid leaf4500CoversExact leaf4500LowerChecked

private noncomputable def leaf4501Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (37/128), chiHi := (75/256) }

private noncomputable def leaf4501Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871271/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715444736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1041172059/536870912) }, upper := { exponent := 0, mantissa := (16067/8192) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi283LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137433938431/137430889472) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf4501InnerLog : WideLogData :=
  innerPair113Data

set_option maxRecDepth 1000000 in
private theorem leaf4501LocalValidity :
    LeafFacts leaf4501Box leaf4501Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4501Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715444736) }) = true
      norm_num [leaf4501Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4501CertificateValid :
    WideCertificateValid leaf4501Box leaf4501Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi283ValidityFacts
    leaf4501LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4501CoverageChecked :
    coverageCheck (innerAD leaf4501Box) leaf4501InnerLog = true := by
  rfl'

private theorem leaf4501InnerLogValid :
    leaf4501InnerLog.Valid 8 (innerAD leaf4501Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint85PositiveFacts.valid leaf4501CoverageChecked

private noncomputable def leaf4501InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629453/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4501InputLogOnePlusV_eq :
    leaf4501InputLogOnePlusV = outerEnclosure 24
      (leaf4501Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4501RoundedFacts : LeafRoundedFacts 8
    leaf4501Certificate.logOnePlusV leaf4501InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4501InputLogOnePlusV_eq }

private noncomputable def leaf4501Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi283InputQChi innerPair113Input
    leaf4501InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4501LowerChecked :
    lowerCheck 24 leaf4501Box leaf4501Inputs = true := by
  rfl'

private theorem leaf4501CoversExact : CoversExact 8
    leaf4501Box leaf4501Certificate leaf4501InnerLog leaf4501Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi283RoundedFacts
    innerPair113RoundedFacts leaf4501RoundedFacts (by rfl)

private theorem leaf4501FlatSound : Sound leaf4501Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4501CertificateValid
    leaf4501InnerLogValid leaf4501CoversExact leaf4501LowerChecked

private noncomputable def leaf4502Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (75/256), chiHi := (19/64) }

private noncomputable def leaf4502Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871273/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715390976) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1047987385/536870912) }, upper := { exponent := 0, mantissa := (4043/2048) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi284LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137433884671/137430781952) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf4502InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4502LocalValidity :
    LeafFacts leaf4502Box leaf4502Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4502Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715390976) }) = true
      norm_num [leaf4502Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4502CertificateValid :
    WideCertificateValid leaf4502Box leaf4502Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi284ValidityFacts
    leaf4502LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4502CoverageChecked :
    coverageCheck (innerAD leaf4502Box) leaf4502InnerLog = true := by
  rfl'

private theorem leaf4502InnerLogValid :
    leaf4502InnerLog.Valid 8 (innerAD leaf4502Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4502CoverageChecked

private noncomputable def leaf4502InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907365/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4502InputLogOnePlusV_eq :
    leaf4502InputLogOnePlusV = outerEnclosure 24
      (leaf4502Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4502RoundedFacts : LeafRoundedFacts 8
    leaf4502Certificate.logOnePlusV leaf4502InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4502InputLogOnePlusV_eq }

private noncomputable def leaf4502Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi284InputQChi innerPair108Input
    leaf4502InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4502LowerChecked :
    lowerCheck 24 leaf4502Box leaf4502Inputs = true := by
  rfl'

private theorem leaf4502CoversExact : CoversExact 8
    leaf4502Box leaf4502Certificate leaf4502InnerLog leaf4502Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi284RoundedFacts
    innerPair108RoundedFacts leaf4502RoundedFacts (by rfl)

private theorem leaf4502FlatSound : Sound leaf4502Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4502CertificateValid
    leaf4502InnerLogValid leaf4502CoversExact leaf4502LowerChecked

private noncomputable def leaf4503Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (37/128), chiHi := (75/256) }

private noncomputable def leaf4503Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871273/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715406336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1046021425/536870912) }, upper := { exponent := 0, mantissa := (8071/4096) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi283LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137433900031/137430812672) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf4503InnerLog : WideLogData :=
  innerPair114Data

set_option maxRecDepth 1000000 in
private theorem leaf4503LocalValidity :
    LeafFacts leaf4503Box leaf4503Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4503Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715406336) }) = true
      norm_num [leaf4503Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4503CertificateValid :
    WideCertificateValid leaf4503Box leaf4503Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi283ValidityFacts
    leaf4503LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4503CoverageChecked :
    coverageCheck (innerAD leaf4503Box) leaf4503InnerLog = true := by
  rfl'

private theorem leaf4503InnerLogValid :
    leaf4503InnerLog.Valid 8 (innerAD leaf4503Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint267PositiveFacts.valid leaf4503CoverageChecked

private noncomputable def leaf4503InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814729/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4503InputLogOnePlusV_eq :
    leaf4503InputLogOnePlusV = outerEnclosure 24
      (leaf4503Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4503RoundedFacts : LeafRoundedFacts 8
    leaf4503Certificate.logOnePlusV leaf4503InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4503InputLogOnePlusV_eq }

private noncomputable def leaf4503Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi283InputQChi innerPair114Input
    leaf4503InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4503LowerChecked :
    lowerCheck 24 leaf4503Box leaf4503Inputs = true := by
  rfl'

private theorem leaf4503CoversExact : CoversExact 8
    leaf4503Box leaf4503Certificate leaf4503InnerLog leaf4503Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi283RoundedFacts
    innerPair114RoundedFacts leaf4503RoundedFacts (by rfl)

private theorem leaf4503FlatSound : Sound leaf4503Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4503CertificateValid
    leaf4503InnerLogValid leaf4503CoversExact leaf4503LowerChecked

private noncomputable def leaf4504Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (75/256), chiHi := (19/64) }

private noncomputable def leaf4504Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871275/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715352064) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1052902283/536870912) }, upper := { exponent := 0, mantissa := (2031/1024) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi284LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137433845759/137430704128) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf4504InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4504LocalValidity :
    LeafFacts leaf4504Box leaf4504Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4504Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715352064) }) = true
      norm_num [leaf4504Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4504CertificateValid :
    WideCertificateValid leaf4504Box leaf4504Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi284ValidityFacts
    leaf4504LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4504CoverageChecked :
    coverageCheck (innerAD leaf4504Box) leaf4504InnerLog = true := by
  rfl'

private theorem leaf4504InnerLogValid :
    leaf4504InnerLog.Valid 8 (innerAD leaf4504Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4504CoverageChecked

private noncomputable def leaf4504InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453683/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf4504InputLogOnePlusV_eq :
    leaf4504InputLogOnePlusV = outerEnclosure 24
      (leaf4504Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4504RoundedFacts : LeafRoundedFacts 8
    leaf4504Certificate.logOnePlusV leaf4504InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4504InputLogOnePlusV_eq }

private noncomputable def leaf4504Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi284InputQChi innerPair108Input
    leaf4504InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4504LowerChecked :
    lowerCheck 24 leaf4504Box leaf4504Inputs = true := by
  rfl'

private theorem leaf4504CoversExact : CoversExact 8
    leaf4504Box leaf4504Certificate leaf4504InnerLog leaf4504Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi284RoundedFacts
    innerPair108RoundedFacts leaf4504RoundedFacts (by rfl)

private theorem leaf4504FlatSound : Sound leaf4504Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4504CertificateValid
    leaf4504InnerLogValid leaf4504CoversExact leaf4504LowerChecked

private noncomputable def leaf4505Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (9/32), chiHi := (73/256) }

private noncomputable def leaf4505Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871271/536870912) }, vSqrt := { lower := (65529/65536), upper := (1347421445/1347362304) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1036978011/536870912) }, upper := { exponent := 0, mantissa := (16003/8192) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi281LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (2694783749/2694724608) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf4505InnerLog : WideLogData :=
  innerPair306Data

set_option maxRecDepth 1000000 in
private theorem leaf4505LocalValidity :
    LeafFacts leaf4505Box leaf4505Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4505Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (1347421445/1347362304) }) = true
      norm_num [leaf4505Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4505CertificateValid :
    WideCertificateValid leaf4505Box leaf4505Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi281ValidityFacts
    leaf4505LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4505CoverageChecked :
    coverageCheck (innerAD leaf4505Box) leaf4505InnerLog = true := by
  rfl'

private theorem leaf4505InnerLogValid :
    leaf4505InnerLog.Valid 8 (innerAD leaf4505Box) :=
  wideLogDataValid_of_cachedCheck endpoint81PositiveFacts
    endpoint85PositiveFacts.valid leaf4505CoverageChecked

private noncomputable def leaf4505InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629449/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4505InputLogOnePlusV_eq :
    leaf4505InputLogOnePlusV = outerEnclosure 24
      (leaf4505Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4505RoundedFacts : LeafRoundedFacts 8
    leaf4505Certificate.logOnePlusV leaf4505InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4505InputLogOnePlusV_eq }

private noncomputable def leaf4505Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi281InputQChi innerPair306Input
    leaf4505InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4505LowerChecked :
    lowerCheck 24 leaf4505Box leaf4505Inputs = true := by
  rfl'

private theorem leaf4505CoversExact : CoversExact 8
    leaf4505Box leaf4505Certificate leaf4505InnerLog leaf4505Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi281RoundedFacts
    innerPair306RoundedFacts leaf4505RoundedFacts (by rfl)

private theorem leaf4505FlatSound : Sound leaf4505Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4505CertificateValid
    leaf4505InnerLogValid leaf4505CoversExact leaf4505LowerChecked

private noncomputable def leaf4506Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (73/256), chiHi := (37/128) }

private noncomputable def leaf4506Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871273/536870912) }, vSqrt := { lower := (65529/65536), upper := (13743698739/13743084544) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1043924401/536870912) }, upper := { exponent := 0, mantissa := (8055/4096) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi282LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (27486783283/27486169088) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf4506InnerLog : WideLogData :=
  innerPair113Data

set_option maxRecDepth 1000000 in
private theorem leaf4506LocalValidity :
    LeafFacts leaf4506Box leaf4506Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4506Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (13743698739/13743084544) }) = true
      norm_num [leaf4506Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4506CertificateValid :
    WideCertificateValid leaf4506Box leaf4506Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi282ValidityFacts
    leaf4506LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4506CoverageChecked :
    coverageCheck (innerAD leaf4506Box) leaf4506InnerLog = true := by
  rfl'

private theorem leaf4506InnerLogValid :
    leaf4506InnerLog.Valid 8 (innerAD leaf4506Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint85PositiveFacts.valid leaf4506CoverageChecked

private noncomputable def leaf4506InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (726841/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf4506InputLogOnePlusV_eq :
    leaf4506InputLogOnePlusV = outerEnclosure 24
      (leaf4506Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4506RoundedFacts : LeafRoundedFacts 8
    leaf4506Certificate.logOnePlusV leaf4506InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4506InputLogOnePlusV_eq }

private noncomputable def leaf4506Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi282InputQChi innerPair113Input
    leaf4506InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4506LowerChecked :
    lowerCheck 24 leaf4506Box leaf4506Inputs = true := by
  rfl'

private theorem leaf4506CoversExact : CoversExact 8
    leaf4506Box leaf4506Certificate leaf4506InnerLog leaf4506Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi282RoundedFacts
    innerPair113RoundedFacts leaf4506RoundedFacts (by rfl)

private theorem leaf4506FlatSound : Sound leaf4506Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4506CertificateValid
    leaf4506InnerLogValid leaf4506CoversExact leaf4506LowerChecked

private noncomputable def leaf4507Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (9/32), chiHi := (73/256) }

private noncomputable def leaf4507Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871273/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715440128) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1041696313/536870912) }, upper := { exponent := 0, mantissa := (4019/2048) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi281LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137433933823/137430880256) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf4507InnerLog : WideLogData :=
  innerPair113Data

set_option maxRecDepth 1000000 in
private theorem leaf4507LocalValidity :
    LeafFacts leaf4507Box leaf4507Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4507Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715440128) }) = true
      norm_num [leaf4507Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4507CertificateValid :
    WideCertificateValid leaf4507Box leaf4507Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi281ValidityFacts
    leaf4507LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4507CoverageChecked :
    coverageCheck (innerAD leaf4507Box) leaf4507InnerLog = true := by
  rfl'

private theorem leaf4507InnerLogValid :
    leaf4507InnerLog.Valid 8 (innerAD leaf4507Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint85PositiveFacts.valid leaf4507CoverageChecked

private noncomputable def leaf4507InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814727/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4507InputLogOnePlusV_eq :
    leaf4507InputLogOnePlusV = outerEnclosure 24
      (leaf4507Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4507RoundedFacts : LeafRoundedFacts 8
    leaf4507Certificate.logOnePlusV leaf4507InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4507InputLogOnePlusV_eq }

private noncomputable def leaf4507Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi281InputQChi innerPair113Input
    leaf4507InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4507LowerChecked :
    lowerCheck 24 leaf4507Box leaf4507Inputs = true := by
  rfl'

private theorem leaf4507CoversExact : CoversExact 8
    leaf4507Box leaf4507Certificate leaf4507InnerLog leaf4507Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi281RoundedFacts
    innerPair113RoundedFacts leaf4507RoundedFacts (by rfl)

private theorem leaf4507FlatSound : Sound leaf4507Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4507CertificateValid
    leaf4507InnerLogValid leaf4507CoversExact leaf4507LowerChecked

private noncomputable def leaf4508Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (73/256), chiHi := (37/128) }

private noncomputable def leaf4508Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871275/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715384832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1048708235/536870912) }, upper := { exponent := 0, mantissa := (2023/1024) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi282LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137433878527/137430769664) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf4508InnerLog : WideLogData :=
  innerPair238Data

set_option maxRecDepth 1000000 in
private theorem leaf4508LocalValidity :
    LeafFacts leaf4508Box leaf4508Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4508Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715384832) }) = true
      norm_num [leaf4508Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4508CertificateValid :
    WideCertificateValid leaf4508Box leaf4508Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi282ValidityFacts
    leaf4508LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4508CoverageChecked :
    coverageCheck (innerAD leaf4508Box) leaf4508InnerLog = true := by
  rfl'

private theorem leaf4508InnerLogValid :
    leaf4508InnerLog.Valid 8 (innerAD leaf4508Box) :=
  wideLogDataValid_of_cachedCheck endpoint71PositiveFacts
    endpoint267PositiveFacts.valid leaf4508CoverageChecked

private noncomputable def leaf4508InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907365/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4508InputLogOnePlusV_eq :
    leaf4508InputLogOnePlusV = outerEnclosure 24
      (leaf4508Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4508RoundedFacts : LeafRoundedFacts 8
    leaf4508Certificate.logOnePlusV leaf4508InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4508InputLogOnePlusV_eq }

private noncomputable def leaf4508Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi282InputQChi innerPair238Input
    leaf4508InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4508LowerChecked :
    lowerCheck 24 leaf4508Box leaf4508Inputs = true := by
  rfl'

private theorem leaf4508CoversExact : CoversExact 8
    leaf4508Box leaf4508Certificate leaf4508InnerLog leaf4508Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi282RoundedFacts
    innerPair238RoundedFacts leaf4508RoundedFacts (by rfl)

private theorem leaf4508FlatSound : Sound leaf4508Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4508CertificateValid
    leaf4508InnerLogValid leaf4508CoversExact leaf4508LowerChecked

private noncomputable def leaf4509Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (37/128), chiHi := (75/256) }

private noncomputable def leaf4509Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871275/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715367936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1050870791/536870912) }, upper := { exponent := 0, mantissa := (16217/8192) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi283LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137433861631/137430735872) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf4509InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4509LocalValidity :
    LeafFacts leaf4509Box leaf4509Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4509Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715367936) }) = true
      norm_num [leaf4509Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4509CertificateValid :
    WideCertificateValid leaf4509Box leaf4509Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi283ValidityFacts
    leaf4509LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4509CoverageChecked :
    coverageCheck (innerAD leaf4509Box) leaf4509InnerLog = true := by
  rfl'

private theorem leaf4509InnerLogValid :
    leaf4509InnerLog.Valid 8 (innerAD leaf4509Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4509CoverageChecked

private noncomputable def leaf4509InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814731/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4509InputLogOnePlusV_eq :
    leaf4509InputLogOnePlusV = outerEnclosure 24
      (leaf4509Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4509RoundedFacts : LeafRoundedFacts 8
    leaf4509Certificate.logOnePlusV leaf4509InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4509InputLogOnePlusV_eq }

private noncomputable def leaf4509Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi283InputQChi innerPair108Input
    leaf4509InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4509LowerChecked :
    lowerCheck 24 leaf4509Box leaf4509Inputs = true := by
  rfl'

private theorem leaf4509CoversExact : CoversExact 8
    leaf4509Box leaf4509Certificate leaf4509InnerLog leaf4509Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi283RoundedFacts
    innerPair108RoundedFacts leaf4509RoundedFacts (by rfl)

private theorem leaf4509FlatSound : Sound leaf4509Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4509CertificateValid
    leaf4509InnerLogValid leaf4509CoversExact leaf4509LowerChecked

private noncomputable def leaf4510Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (75/256), chiHi := (19/64) }

private noncomputable def leaf4510Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871277/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357656576) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1057817181/536870912) }, upper := { exponent := 0, mantissa := (4081/2048) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi284LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716379135/68715313152) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf4510InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4510LocalValidity :
    LeafFacts leaf4510Box leaf4510Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4510Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357656576) }) = true
      norm_num [leaf4510Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4510CertificateValid :
    WideCertificateValid leaf4510Box leaf4510Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi284ValidityFacts
    leaf4510LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4510CoverageChecked :
    coverageCheck (innerAD leaf4510Box) leaf4510InnerLog = true := by
  rfl'

private theorem leaf4510InnerLogValid :
    leaf4510InnerLog.Valid 8 (innerAD leaf4510Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4510CoverageChecked

private noncomputable def leaf4510InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629341/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4510InputLogOnePlusV_eq :
    leaf4510InputLogOnePlusV = outerEnclosure 24
      (leaf4510Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4510RoundedFacts : LeafRoundedFacts 8
    leaf4510Certificate.logOnePlusV leaf4510InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4510InputLogOnePlusV_eq }

private noncomputable def leaf4510Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi284InputQChi innerPair108Input
    leaf4510InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4510LowerChecked :
    lowerCheck 24 leaf4510Box leaf4510Inputs = true := by
  rfl'

private theorem leaf4510CoversExact : CoversExact 8
    leaf4510Box leaf4510Certificate leaf4510InnerLog leaf4510Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi284RoundedFacts
    innerPair108RoundedFacts leaf4510RoundedFacts (by rfl)

private theorem leaf4510FlatSound : Sound leaf4510Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4510CertificateValid
    leaf4510InnerLogValid leaf4510CoversExact leaf4510LowerChecked

private noncomputable def leaf4511Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (37/128), chiHi := (75/256) }

private noncomputable def leaf4511Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871277/536870912) }, vSqrt := { lower := (65529/65536), upper := (288728761/288719872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1055720157/536870912) }, upper := { exponent := 0, mantissa := (4073/2048) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi283LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (577448633/577439744) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf4511InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4511LocalValidity :
    LeafFacts leaf4511Box leaf4511Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4511Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (288728761/288719872) }) = true
      norm_num [leaf4511Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4511CertificateValid :
    WideCertificateValid leaf4511Box leaf4511Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi283ValidityFacts
    leaf4511LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4511CoverageChecked :
    coverageCheck (innerAD leaf4511Box) leaf4511InnerLog = true := by
  rfl'

private theorem leaf4511InnerLogValid :
    leaf4511InnerLog.Valid 8 (innerAD leaf4511Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4511CoverageChecked

private noncomputable def leaf4511InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629339/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4511InputLogOnePlusV_eq :
    leaf4511InputLogOnePlusV = outerEnclosure 24
      (leaf4511Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4511RoundedFacts : LeafRoundedFacts 8
    leaf4511Certificate.logOnePlusV leaf4511InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4511InputLogOnePlusV_eq }

private noncomputable def leaf4511Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi283InputQChi innerPair108Input
    leaf4511InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4511LowerChecked :
    lowerCheck 24 leaf4511Box leaf4511Inputs = true := by
  rfl'

private theorem leaf4511CoversExact : CoversExact 8
    leaf4511Box leaf4511Certificate leaf4511InnerLog leaf4511Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi283RoundedFacts
    innerPair108RoundedFacts leaf4511RoundedFacts (by rfl)

private theorem leaf4511FlatSound : Sound leaf4511Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4511CertificateValid
    leaf4511InnerLogValid leaf4511CoversExact leaf4511LowerChecked

private noncomputable def leaf4512Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (75/256), chiHi := (19/64) }

private noncomputable def leaf4512Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871279/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357637120) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1062732079/536870912) }, upper := { exponent := 1, mantissa := (1025/1024) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi284LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716359679/68715274240) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf4512InnerLog : WideLogData :=
  innerPair321Data

set_option maxRecDepth 1000000 in
private theorem leaf4512LocalValidity :
    LeafFacts leaf4512Box leaf4512Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4512Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357637120) }) = true
      norm_num [leaf4512Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4512CertificateValid :
    WideCertificateValid leaf4512Box leaf4512Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi284ValidityFacts
    leaf4512LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4512CoverageChecked :
    coverageCheck (innerAD leaf4512Box) leaf4512InnerLog = true := by
  rfl'

private theorem leaf4512InnerLogValid :
    leaf4512InnerLog.Valid 8 (innerAD leaf4512Box) :=
  wideLogDataValid_of_cachedCheck endpoint85PositiveFacts
    endpoint283PositiveFacts.valid leaf4512CoverageChecked

private noncomputable def leaf4512InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814673/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4512InputLogOnePlusV_eq :
    leaf4512InputLogOnePlusV = outerEnclosure 24
      (leaf4512Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4512RoundedFacts : LeafRoundedFacts 8
    leaf4512Certificate.logOnePlusV leaf4512InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4512InputLogOnePlusV_eq }

private noncomputable def leaf4512Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi284InputQChi innerPair321Input
    leaf4512InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4512LowerChecked :
    lowerCheck 24 leaf4512Box leaf4512Inputs = true := by
  rfl'

private theorem leaf4512CoversExact : CoversExact 8
    leaf4512Box leaf4512Certificate leaf4512InnerLog leaf4512Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi284RoundedFacts
    innerPair321RoundedFacts leaf4512RoundedFacts (by rfl)

private theorem leaf4512FlatSound : Sound leaf4512Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4512CertificateValid
    leaf4512InnerLogValid leaf4512CoversExact leaf4512LowerChecked

private noncomputable def leaf4513Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (19/64), chiHi := (77/256) }

private noncomputable def leaf4513Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871275/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357668608) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1054802711/536870912) }, upper := { exponent := 0, mantissa := (16277/8192) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi285LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716391167/68715337216) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf4513InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4513LocalValidity :
    LeafFacts leaf4513Box leaf4513Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4513Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357668608) }) = true
      norm_num [leaf4513Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4513CertificateValid :
    WideCertificateValid leaf4513Box leaf4513Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi285ValidityFacts
    leaf4513LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4513CoverageChecked :
    coverageCheck (innerAD leaf4513Box) leaf4513InnerLog = true := by
  rfl'

private theorem leaf4513InnerLogValid :
    leaf4513InnerLog.Valid 8 (innerAD leaf4513Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4513CoverageChecked

private noncomputable def leaf4513InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814669/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4513InputLogOnePlusV_eq :
    leaf4513InputLogOnePlusV = outerEnclosure 24
      (leaf4513Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4513RoundedFacts : LeafRoundedFacts 8
    leaf4513Certificate.logOnePlusV leaf4513InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4513InputLogOnePlusV_eq }

private noncomputable def leaf4513Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi285InputQChi innerPair108Input
    leaf4513InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4513LowerChecked :
    lowerCheck 24 leaf4513Box leaf4513Inputs = true := by
  rfl'

private theorem leaf4513CoversExact : CoversExact 8
    leaf4513Box leaf4513Certificate leaf4513InnerLog leaf4513Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi285RoundedFacts
    innerPair108RoundedFacts leaf4513RoundedFacts (by rfl)

private theorem leaf4513FlatSound : Sound leaf4513Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4513CertificateValid
    leaf4513InnerLogValid leaf4513CoversExact leaf4513LowerChecked

private noncomputable def leaf4514Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (77/256), chiHi := (39/128) }

private noncomputable def leaf4514Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871277/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357641728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1061618037/536870912) }, upper := { exponent := 0, mantissa := (8191/4096) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi286LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716364287/68715283456) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf4514InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4514LocalValidity :
    LeafFacts leaf4514Box leaf4514Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4514Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357641728) }) = true
      norm_num [leaf4514Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4514CertificateValid :
    WideCertificateValid leaf4514Box leaf4514Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi286ValidityFacts
    leaf4514LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4514CoverageChecked :
    coverageCheck (innerAD leaf4514Box) leaf4514InnerLog = true := by
  rfl'

private theorem leaf4514InnerLogValid :
    leaf4514InnerLog.Valid 8 (innerAD leaf4514Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4514CoverageChecked

private noncomputable def leaf4514InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629345/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4514InputLogOnePlusV_eq :
    leaf4514InputLogOnePlusV = outerEnclosure 24
      (leaf4514Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4514RoundedFacts : LeafRoundedFacts 8
    leaf4514Certificate.logOnePlusV leaf4514InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4514InputLogOnePlusV_eq }

private noncomputable def leaf4514Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi286InputQChi innerPair108Input
    leaf4514InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4514LowerChecked :
    lowerCheck 24 leaf4514Box leaf4514Inputs = true := by
  rfl'

private theorem leaf4514CoversExact : CoversExact 8
    leaf4514Box leaf4514Certificate leaf4514InnerLog leaf4514Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi286RoundedFacts
    innerPair108RoundedFacts leaf4514RoundedFacts (by rfl)

private theorem leaf4514FlatSound : Sound leaf4514Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4514CertificateValid
    leaf4514InnerLogValid leaf4514CoversExact leaf4514LowerChecked

private noncomputable def leaf4515Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (19/64), chiHi := (77/256) }

private noncomputable def leaf4515Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871277/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357648896) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1059783141/536870912) }, upper := { exponent := 0, mantissa := (8177/4096) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi285LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716371455/68715297792) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf4515InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4515LocalValidity :
    LeafFacts leaf4515Box leaf4515Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4515Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357648896) }) = true
      norm_num [leaf4515Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4515CertificateValid :
    WideCertificateValid leaf4515Box leaf4515Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi285ValidityFacts
    leaf4515LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4515CoverageChecked :
    coverageCheck (innerAD leaf4515Box) leaf4515InnerLog = true := by
  rfl'

private theorem leaf4515InnerLogValid :
    leaf4515InnerLog.Valid 8 (innerAD leaf4515Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4515CoverageChecked

private noncomputable def leaf4515InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629343/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4515InputLogOnePlusV_eq :
    leaf4515InputLogOnePlusV = outerEnclosure 24
      (leaf4515Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4515RoundedFacts : LeafRoundedFacts 8
    leaf4515Certificate.logOnePlusV leaf4515InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4515InputLogOnePlusV_eq }

private noncomputable def leaf4515Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi285InputQChi innerPair108Input
    leaf4515InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4515LowerChecked :
    lowerCheck 24 leaf4515Box leaf4515Inputs = true := by
  rfl'

private theorem leaf4515CoversExact : CoversExact 8
    leaf4515Box leaf4515Certificate leaf4515InnerLog leaf4515Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi285RoundedFacts
    innerPair108RoundedFacts leaf4515RoundedFacts (by rfl)

private theorem leaf4515FlatSound : Sound leaf4515Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4515CertificateValid
    leaf4515InnerLogValid leaf4515CoversExact leaf4515LowerChecked

private noncomputable def leaf4516Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (77/256), chiHi := (39/128) }

private noncomputable def leaf4516Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871279/536870912) }, vSqrt := { lower := (65529/65536), upper := (4908388937/4908231680) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1066663999/536870912) }, upper := { exponent := 1, mantissa := (4115/4096) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi286LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9816620617/9816463360) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf4516InnerLog : WideLogData :=
  innerPair533Data

set_option maxRecDepth 1000000 in
private theorem leaf4516LocalValidity :
    LeafFacts leaf4516Box leaf4516Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4516Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4908388937/4908231680) }) = true
      norm_num [leaf4516Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4516CertificateValid :
    WideCertificateValid leaf4516Box leaf4516Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi286ValidityFacts
    leaf4516LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4516CoverageChecked :
    coverageCheck (innerAD leaf4516Box) leaf4516InnerLog = true := by
  rfl'

private theorem leaf4516InnerLogValid :
    leaf4516InnerLog.Valid 8 (innerAD leaf4516Box) :=
  wideLogDataValid_of_cachedCheck endpoint267PositiveFacts
    endpoint283PositiveFacts.valid leaf4516CoverageChecked

private noncomputable def leaf4516InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814675/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4516InputLogOnePlusV_eq :
    leaf4516InputLogOnePlusV = outerEnclosure 24
      (leaf4516Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4516RoundedFacts : LeafRoundedFacts 8
    leaf4516Certificate.logOnePlusV leaf4516InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4516InputLogOnePlusV_eq }

private noncomputable def leaf4516Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi286InputQChi innerPair533Input
    leaf4516InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4516LowerChecked :
    lowerCheck 24 leaf4516Box leaf4516Inputs = true := by
  rfl'

private theorem leaf4516CoversExact : CoversExact 8
    leaf4516Box leaf4516Certificate leaf4516InnerLog leaf4516Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi286RoundedFacts
    innerPair533RoundedFacts leaf4516RoundedFacts (by rfl)

private theorem leaf4516FlatSound : Sound leaf4516Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4516CertificateValid
    leaf4516InnerLogValid leaf4516CoversExact leaf4516LowerChecked

private noncomputable def leaf4517Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (39/128), chiHi := (79/256) }

private noncomputable def leaf4517Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871279/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357614848) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1068433363/536870912) }, upper := { exponent := 1, mantissa := (16487/16384) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi287LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716337407/68715229696) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf4517InnerLog : WideLogData :=
  innerPair533Data

set_option maxRecDepth 1000000 in
private theorem leaf4517LocalValidity :
    LeafFacts leaf4517Box leaf4517Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4517Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357614848) }) = true
      norm_num [leaf4517Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4517CertificateValid :
    WideCertificateValid leaf4517Box leaf4517Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi287ValidityFacts
    leaf4517LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4517CoverageChecked :
    coverageCheck (innerAD leaf4517Box) leaf4517InnerLog = true := by
  rfl'

private theorem leaf4517InnerLogValid :
    leaf4517InnerLog.Valid 8 (innerAD leaf4517Box) :=
  wideLogDataValid_of_cachedCheck endpoint267PositiveFacts
    endpoint283PositiveFacts.valid leaf4517CoverageChecked

private noncomputable def leaf4517InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629351/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4517InputLogOnePlusV_eq :
    leaf4517InputLogOnePlusV = outerEnclosure 24
      (leaf4517Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4517RoundedFacts : LeafRoundedFacts 8
    leaf4517Certificate.logOnePlusV leaf4517InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4517InputLogOnePlusV_eq }

private noncomputable def leaf4517Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi287InputQChi innerPair533Input
    leaf4517InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4517LowerChecked :
    lowerCheck 24 leaf4517Box leaf4517Inputs = true := by
  rfl'

private theorem leaf4517CoversExact : CoversExact 8
    leaf4517Box leaf4517Certificate leaf4517InnerLog leaf4517Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi287RoundedFacts
    innerPair533RoundedFacts leaf4517RoundedFacts (by rfl)

private theorem leaf4517FlatSound : Sound leaf4517Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4517CertificateValid
    leaf4517InnerLogValid leaf4517CoversExact leaf4517LowerChecked

private noncomputable def leaf4518Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (79/256), chiHi := (5/16) }

private noncomputable def leaf4518Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871281/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357587968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1075248689/1073741824) }, upper := { exponent := 1, mantissa := (1037/1024) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi288LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716310527/68715175936) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf4518InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4518LocalValidity :
    LeafFacts leaf4518Box leaf4518Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4518Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357587968) }) = true
      norm_num [leaf4518Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4518CertificateValid :
    WideCertificateValid leaf4518Box leaf4518Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi288ValidityFacts
    leaf4518LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4518CoverageChecked :
    coverageCheck (innerAD leaf4518Box) leaf4518InnerLog = true := by
  rfl'

private theorem leaf4518InnerLogValid :
    leaf4518InnerLog.Valid 8 (innerAD leaf4518Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4518CoverageChecked

private noncomputable def leaf4518InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814679/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4518InputLogOnePlusV_eq :
    leaf4518InputLogOnePlusV = outerEnclosure 24
      (leaf4518Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4518RoundedFacts : LeafRoundedFacts 8
    leaf4518Certificate.logOnePlusV leaf4518InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4518InputLogOnePlusV_eq }

private noncomputable def leaf4518Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi288InputQChi innerPair116Input
    leaf4518InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4518LowerChecked :
    lowerCheck 24 leaf4518Box leaf4518Inputs = true := by
  rfl'

private theorem leaf4518CoversExact : CoversExact 8
    leaf4518Box leaf4518Certificate leaf4518InnerLog leaf4518Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi288RoundedFacts
    innerPair116RoundedFacts leaf4518RoundedFacts (by rfl)

private theorem leaf4518FlatSound : Sound leaf4518Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4518CertificateValid
    leaf4518InnerLogValid leaf4518CoversExact leaf4518LowerChecked

private noncomputable def leaf4519Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (39/128), chiHi := (79/256) }

private noncomputable def leaf4519Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871281/536870912) }, vSqrt := { lower := (65529/65536), upper := (1108345889/1108309504) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1073544857/536870912) }, upper := { exponent := 1, mantissa := (8283/8192) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi287LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (2216655393/2216619008) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf4519InnerLog : WideLogData :=
  innerPair531Data

set_option maxRecDepth 1000000 in
private theorem leaf4519LocalValidity :
    LeafFacts leaf4519Box leaf4519Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4519Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (1108345889/1108309504) }) = true
      norm_num [leaf4519Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4519CertificateValid :
    WideCertificateValid leaf4519Box leaf4519Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi287ValidityFacts
    leaf4519LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4519CoverageChecked :
    coverageCheck (innerAD leaf4519Box) leaf4519InnerLog = true := by
  rfl'

private theorem leaf4519InnerLogValid :
    leaf4519InnerLog.Valid 8 (innerAD leaf4519Box) :=
  wideLogDataValid_of_cachedCheck endpoint267PositiveFacts
    endpoint82PositiveFacts.valid leaf4519CoverageChecked

private noncomputable def leaf4519InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907339/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4519InputLogOnePlusV_eq :
    leaf4519InputLogOnePlusV = outerEnclosure 24
      (leaf4519Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4519RoundedFacts : LeafRoundedFacts 8
    leaf4519Certificate.logOnePlusV leaf4519InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4519InputLogOnePlusV_eq }

private noncomputable def leaf4519Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi287InputQChi innerPair531Input
    leaf4519InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4519LowerChecked :
    lowerCheck 24 leaf4519Box leaf4519Inputs = true := by
  rfl'

private theorem leaf4519CoversExact : CoversExact 8
    leaf4519Box leaf4519Certificate leaf4519InnerLog leaf4519Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi287RoundedFacts
    innerPair531RoundedFacts leaf4519RoundedFacts (by rfl)

private theorem leaf4519FlatSound : Sound leaf4519Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4519CertificateValid
    leaf4519InnerLogValid leaf4519CoversExact leaf4519LowerChecked

private noncomputable def leaf4520Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (79/256), chiHi := (5/16) }

private noncomputable def leaf4520Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871283/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357567488) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1080425715/1073741824) }, upper := { exponent := 1, mantissa := (521/512) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi288LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716290047/68715134976) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf4520InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4520LocalValidity :
    LeafFacts leaf4520Box leaf4520Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4520Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357567488) }) = true
      norm_num [leaf4520Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4520CertificateValid :
    WideCertificateValid leaf4520Box leaf4520Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi288ValidityFacts
    leaf4520LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4520CoverageChecked :
    coverageCheck (innerAD leaf4520Box) leaf4520InnerLog = true := by
  rfl'

private theorem leaf4520InnerLogValid :
    leaf4520InnerLog.Valid 8 (innerAD leaf4520Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4520CoverageChecked

private noncomputable def leaf4520InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629363/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4520InputLogOnePlusV_eq :
    leaf4520InputLogOnePlusV = outerEnclosure 24
      (leaf4520Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4520RoundedFacts : LeafRoundedFacts 8
    leaf4520Certificate.logOnePlusV leaf4520InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4520InputLogOnePlusV_eq }

private noncomputable def leaf4520Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi288InputQChi innerPair116Input
    leaf4520InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4520LowerChecked :
    lowerCheck 24 leaf4520Box leaf4520Inputs = true := by
  rfl'

private theorem leaf4520CoversExact : CoversExact 8
    leaf4520Box leaf4520Certificate leaf4520InnerLog leaf4520Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi288RoundedFacts
    innerPair116RoundedFacts leaf4520RoundedFacts (by rfl)

private theorem leaf4520FlatSound : Sound leaf4520Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4520CertificateValid
    leaf4520InnerLogValid leaf4520CoversExact leaf4520LowerChecked

private noncomputable def leaf4521Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (19/64), chiHi := (77/256) }

private noncomputable def leaf4521Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871279/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357629184) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1064763571/536870912) }, upper := { exponent := 1, mantissa := (16431/16384) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi285LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716351743/68715258368) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf4521InnerLog : WideLogData :=
  innerPair321Data

set_option maxRecDepth 1000000 in
private theorem leaf4521LocalValidity :
    LeafFacts leaf4521Box leaf4521Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4521Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357629184) }) = true
      norm_num [leaf4521Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4521CertificateValid :
    WideCertificateValid leaf4521Box leaf4521Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi285ValidityFacts
    leaf4521LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4521CoverageChecked :
    coverageCheck (innerAD leaf4521Box) leaf4521InnerLog = true := by
  rfl'

private theorem leaf4521InnerLogValid :
    leaf4521InnerLog.Valid 8 (innerAD leaf4521Box) :=
  wideLogDataValid_of_cachedCheck endpoint85PositiveFacts
    endpoint283PositiveFacts.valid leaf4521CoverageChecked

private noncomputable def leaf4521InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907337/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4521InputLogOnePlusV_eq :
    leaf4521InputLogOnePlusV = outerEnclosure 24
      (leaf4521Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4521RoundedFacts : LeafRoundedFacts 8
    leaf4521Certificate.logOnePlusV leaf4521InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4521InputLogOnePlusV_eq }

private noncomputable def leaf4521Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi285InputQChi innerPair321Input
    leaf4521InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4521LowerChecked :
    lowerCheck 24 leaf4521Box leaf4521Inputs = true := by
  rfl'

private theorem leaf4521CoversExact : CoversExact 8
    leaf4521Box leaf4521Certificate leaf4521InnerLog leaf4521Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi285RoundedFacts
    innerPair321RoundedFacts leaf4521RoundedFacts (by rfl)

private theorem leaf4521FlatSound : Sound leaf4521Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4521CertificateValid
    leaf4521InnerLogValid leaf4521CoversExact leaf4521LowerChecked

private noncomputable def leaf4522Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (77/256), chiHi := (39/128) }

private noncomputable def leaf4522Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871281/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357601792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1071709961/536870912) }, upper := { exponent := 1, mantissa := (8269/8192) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi286LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716324351/68715203584) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf4522InnerLog : WideLogData :=
  innerPair531Data

set_option maxRecDepth 1000000 in
private theorem leaf4522LocalValidity :
    LeafFacts leaf4522Box leaf4522Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4522Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357601792) }) = true
      norm_num [leaf4522Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4522CertificateValid :
    WideCertificateValid leaf4522Box leaf4522Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi286ValidityFacts
    leaf4522LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4522CoverageChecked :
    coverageCheck (innerAD leaf4522Box) leaf4522InnerLog = true := by
  rfl'

private theorem leaf4522InnerLogValid :
    leaf4522InnerLog.Valid 8 (innerAD leaf4522Box) :=
  wideLogDataValid_of_cachedCheck endpoint267PositiveFacts
    endpoint82PositiveFacts.valid leaf4522CoverageChecked

private noncomputable def leaf4522InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814677/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4522InputLogOnePlusV_eq :
    leaf4522InputLogOnePlusV = outerEnclosure 24
      (leaf4522Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4522RoundedFacts : LeafRoundedFacts 8
    leaf4522Certificate.logOnePlusV leaf4522InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4522InputLogOnePlusV_eq }

private noncomputable def leaf4522Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi286InputQChi innerPair531Input
    leaf4522InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4522LowerChecked :
    lowerCheck 24 leaf4522Box leaf4522Inputs = true := by
  rfl'

private theorem leaf4522CoversExact : CoversExact 8
    leaf4522Box leaf4522Certificate leaf4522InnerLog leaf4522Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi286RoundedFacts
    innerPair531RoundedFacts leaf4522RoundedFacts (by rfl)

private theorem leaf4522FlatSound : Sound leaf4522Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4522CertificateValid
    leaf4522InnerLogValid leaf4522CoversExact leaf4522LowerChecked

private noncomputable def leaf4523Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (19/64), chiHi := (77/256) }

private noncomputable def leaf4523Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871281/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357609472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1069744001/536870912) }, upper := { exponent := 1, mantissa := (4127/4096) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi285LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716332031/68715218944) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf4523InnerLog : WideLogData :=
  innerPair533Data

set_option maxRecDepth 1000000 in
private theorem leaf4523LocalValidity :
    LeafFacts leaf4523Box leaf4523Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4523Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357609472) }) = true
      norm_num [leaf4523Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4523CertificateValid :
    WideCertificateValid leaf4523Box leaf4523Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi285ValidityFacts
    leaf4523LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4523CoverageChecked :
    coverageCheck (innerAD leaf4523Box) leaf4523InnerLog = true := by
  rfl'

private theorem leaf4523InnerLogValid :
    leaf4523InnerLog.Valid 8 (innerAD leaf4523Box) :=
  wideLogDataValid_of_cachedCheck endpoint267PositiveFacts
    endpoint283PositiveFacts.valid leaf4523CoverageChecked

private noncomputable def leaf4523InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629353/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4523InputLogOnePlusV_eq :
    leaf4523InputLogOnePlusV = outerEnclosure 24
      (leaf4523Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4523RoundedFacts : LeafRoundedFacts 8
    leaf4523Certificate.logOnePlusV leaf4523InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4523InputLogOnePlusV_eq }

private noncomputable def leaf4523Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi285InputQChi innerPair533Input
    leaf4523InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4523LowerChecked :
    lowerCheck 24 leaf4523Box leaf4523Inputs = true := by
  rfl'

private theorem leaf4523CoversExact : CoversExact 8
    leaf4523Box leaf4523Certificate leaf4523InnerLog leaf4523Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi285RoundedFacts
    innerPair533RoundedFacts leaf4523RoundedFacts (by rfl)

private theorem leaf4523FlatSound : Sound leaf4523Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4523CertificateValid
    leaf4523InnerLogValid leaf4523CoversExact leaf4523LowerChecked

private noncomputable def leaf4524Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (77/256), chiHi := (39/128) }

private noncomputable def leaf4524Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871283/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357581824) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1076755923/1073741824) }, upper := { exponent := 1, mantissa := (2077/2048) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi286LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716304383/68715163648) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf4524InnerLog : WideLogData :=
  innerPair119Data

set_option maxRecDepth 1000000 in
private theorem leaf4524LocalValidity :
    LeafFacts leaf4524Box leaf4524Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4524Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357581824) }) = true
      norm_num [leaf4524Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4524CertificateValid :
    WideCertificateValid leaf4524Box leaf4524Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi286ValidityFacts
    leaf4524LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4524CoverageChecked :
    coverageCheck (innerAD leaf4524Box) leaf4524InnerLog = true := by
  rfl'

private theorem leaf4524InnerLogValid :
    leaf4524InnerLog.Valid 8 (innerAD leaf4524Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint82PositiveFacts.valid leaf4524CoverageChecked

private noncomputable def leaf4524InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629359/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4524InputLogOnePlusV_eq :
    leaf4524InputLogOnePlusV = outerEnclosure 24
      (leaf4524Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4524RoundedFacts : LeafRoundedFacts 8
    leaf4524Certificate.logOnePlusV leaf4524InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4524InputLogOnePlusV_eq }

private noncomputable def leaf4524Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi286InputQChi innerPair119Input
    leaf4524InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4524LowerChecked :
    lowerCheck 24 leaf4524Box leaf4524Inputs = true := by
  rfl'

private theorem leaf4524CoversExact : CoversExact 8
    leaf4524Box leaf4524Certificate leaf4524InnerLog leaf4524Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi286RoundedFacts
    innerPair119RoundedFacts leaf4524RoundedFacts (by rfl)

private theorem leaf4524FlatSound : Sound leaf4524Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4524CertificateValid
    leaf4524InnerLogValid leaf4524CoversExact leaf4524LowerChecked

private noncomputable def leaf4525Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (39/128), chiHi := (79/256) }

private noncomputable def leaf4525Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871283/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357574400) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1078656351/1073741824) }, upper := { exponent := 1, mantissa := (16645/16384) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi287LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716296959/68715148800) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf4525InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4525LocalValidity :
    LeafFacts leaf4525Box leaf4525Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4525Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357574400) }) = true
      norm_num [leaf4525Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4525CertificateValid :
    WideCertificateValid leaf4525Box leaf4525Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi287ValidityFacts
    leaf4525LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4525CoverageChecked :
    coverageCheck (innerAD leaf4525Box) leaf4525InnerLog = true := by
  rfl'

private theorem leaf4525InnerLogValid :
    leaf4525InnerLog.Valid 8 (innerAD leaf4525Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4525CoverageChecked

private noncomputable def leaf4525InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629361/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4525InputLogOnePlusV_eq :
    leaf4525InputLogOnePlusV = outerEnclosure 24
      (leaf4525Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4525RoundedFacts : LeafRoundedFacts 8
    leaf4525Certificate.logOnePlusV leaf4525InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4525InputLogOnePlusV_eq }

private noncomputable def leaf4525Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi287InputQChi innerPair116Input
    leaf4525InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4525LowerChecked :
    lowerCheck 24 leaf4525Box leaf4525Inputs = true := by
  rfl'

private theorem leaf4525CoversExact : CoversExact 8
    leaf4525Box leaf4525Certificate leaf4525InnerLog leaf4525Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi287RoundedFacts
    innerPair116RoundedFacts leaf4525RoundedFacts (by rfl)

private theorem leaf4525FlatSound : Sound leaf4525Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4525CertificateValid
    leaf4525InnerLogValid leaf4525CoversExact leaf4525LowerChecked

private noncomputable def leaf4526Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (79/256), chiHi := (5/16) }

private noncomputable def leaf4526Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871285/536870912) }, vSqrt := { lower := (65529/65536), upper := (1108345889/1108307968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1085602741/1073741824) }, upper := { exponent := 1, mantissa := (1047/1024) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi288LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (2216653857/2216615936) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf4526InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4526LocalValidity :
    LeafFacts leaf4526Box leaf4526Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4526Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (1108345889/1108307968) }) = true
      norm_num [leaf4526Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4526CertificateValid :
    WideCertificateValid leaf4526Box leaf4526Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi288ValidityFacts
    leaf4526LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4526CoverageChecked :
    coverageCheck (innerAD leaf4526Box) leaf4526InnerLog = true := by
  rfl'

private theorem leaf4526InnerLogValid :
    leaf4526InnerLog.Valid 8 (innerAD leaf4526Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4526CoverageChecked

private noncomputable def leaf4526InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453671/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf4526InputLogOnePlusV_eq :
    leaf4526InputLogOnePlusV = outerEnclosure 24
      (leaf4526Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4526RoundedFacts : LeafRoundedFacts 8
    leaf4526Certificate.logOnePlusV leaf4526InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4526InputLogOnePlusV_eq }

private noncomputable def leaf4526Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi288InputQChi innerPair116Input
    leaf4526InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4526LowerChecked :
    lowerCheck 24 leaf4526Box leaf4526Inputs = true := by
  rfl'

private theorem leaf4526CoversExact : CoversExact 8
    leaf4526Box leaf4526Certificate leaf4526InnerLog leaf4526Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi288RoundedFacts
    innerPair116RoundedFacts leaf4526RoundedFacts (by rfl)

private theorem leaf4526FlatSound : Sound leaf4526Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4526CertificateValid
    leaf4526InnerLogValid leaf4526CoversExact leaf4526LowerChecked

private noncomputable def leaf4527Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (39/128), chiHi := (79/256) }

private noncomputable def leaf4527Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871285/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357554176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1083767845/1073741824) }, upper := { exponent := 1, mantissa := (4181/4096) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi287LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716276735/68715108352) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf4527InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4527LocalValidity :
    LeafFacts leaf4527Box leaf4527Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4527Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357554176) }) = true
      norm_num [leaf4527Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4527CertificateValid :
    WideCertificateValid leaf4527Box leaf4527Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi287ValidityFacts
    leaf4527LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4527CoverageChecked :
    coverageCheck (innerAD leaf4527Box) leaf4527InnerLog = true := by
  rfl'

private theorem leaf4527InnerLogValid :
    leaf4527InnerLog.Valid 8 (innerAD leaf4527Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4527CoverageChecked

private noncomputable def leaf4527InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814683/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4527InputLogOnePlusV_eq :
    leaf4527InputLogOnePlusV = outerEnclosure 24
      (leaf4527Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4527RoundedFacts : LeafRoundedFacts 8
    leaf4527Certificate.logOnePlusV leaf4527InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4527InputLogOnePlusV_eq }

private noncomputable def leaf4527Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi287InputQChi innerPair116Input
    leaf4527InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4527LowerChecked :
    lowerCheck 24 leaf4527Box leaf4527Inputs = true := by
  rfl'

private theorem leaf4527CoversExact : CoversExact 8
    leaf4527Box leaf4527Certificate leaf4527InnerLog leaf4527Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi287RoundedFacts
    innerPair116RoundedFacts leaf4527RoundedFacts (by rfl)

private theorem leaf4527FlatSound : Sound leaf4527Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4527CertificateValid
    leaf4527InnerLogValid leaf4527CoversExact leaf4527LowerChecked

private noncomputable def leaf4528Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (79/256), chiHi := (5/16) }

private noncomputable def leaf4528Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871287/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357526528) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1090779767/1073741824) }, upper := { exponent := 1, mantissa := (263/256) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi288LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716249087/68715053056) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf4528InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4528LocalValidity :
    LeafFacts leaf4528Box leaf4528Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4528Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357526528) }) = true
      norm_num [leaf4528Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4528CertificateValid :
    WideCertificateValid leaf4528Box leaf4528Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi288ValidityFacts
    leaf4528LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4528CoverageChecked :
    coverageCheck (innerAD leaf4528Box) leaf4528InnerLog = true := by
  rfl'

private theorem leaf4528InnerLogValid :
    leaf4528InnerLog.Valid 8 (innerAD leaf4528Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4528CoverageChecked

private noncomputable def leaf4528InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629373/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4528InputLogOnePlusV_eq :
    leaf4528InputLogOnePlusV = outerEnclosure 24
      (leaf4528Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4528RoundedFacts : LeafRoundedFacts 8
    leaf4528Certificate.logOnePlusV leaf4528InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4528InputLogOnePlusV_eq }

private noncomputable def leaf4528Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi288InputQChi innerPair116Input
    leaf4528InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4528LowerChecked :
    lowerCheck 24 leaf4528Box leaf4528Inputs = true := by
  rfl'

private theorem leaf4528CoversExact : CoversExact 8
    leaf4528Box leaf4528Certificate leaf4528InnerLog leaf4528Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi288RoundedFacts
    innerPair116RoundedFacts leaf4528RoundedFacts (by rfl)

private theorem leaf4528FlatSound : Sound leaf4528Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4528CertificateValid
    leaf4528InnerLogValid leaf4528CoversExact leaf4528LowerChecked

private noncomputable def component92Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (9/32), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component92Node0_sound : Sound component92Node0Box :=
  sound_of_literal_split component92Node0Box leaf4497Box leaf4498Box
    .chi (73/256) (by rfl) (by rfl)
    leaf4497FlatSound leaf4498FlatSound

private noncomputable def component92Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (9/32), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component92Node1_sound : Sound component92Node1Box :=
  sound_of_literal_split component92Node1Box leaf4499Box leaf4500Box
    .chi (73/256) (by rfl) (by rfl)
    leaf4499FlatSound leaf4500FlatSound

private noncomputable def component92Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (9/32), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component92Node2_sound : Sound component92Node2Box :=
  sound_of_literal_split component92Node2Box component92Node0Box component92Node1Box
    .k (105/32) (by rfl) (by rfl)
    component92Node0_sound component92Node1_sound

private noncomputable def component92Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (37/128), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component92Node3_sound : Sound component92Node3Box :=
  sound_of_literal_split component92Node3Box leaf4501Box leaf4502Box
    .chi (75/256) (by rfl) (by rfl)
    leaf4501FlatSound leaf4502FlatSound

private noncomputable def component92Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (37/128), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component92Node4_sound : Sound component92Node4Box :=
  sound_of_literal_split component92Node4Box leaf4503Box leaf4504Box
    .chi (75/256) (by rfl) (by rfl)
    leaf4503FlatSound leaf4504FlatSound

private noncomputable def component92Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (37/128), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component92Node5_sound : Sound component92Node5Box :=
  sound_of_literal_split component92Node5Box component92Node3Box component92Node4Box
    .k (105/32) (by rfl) (by rfl)
    component92Node3_sound component92Node4_sound

private noncomputable def component92Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component92Node6_sound : Sound component92Node6Box :=
  sound_of_literal_split component92Node6Box component92Node2Box component92Node5Box
    .chi (37/128) (by rfl) (by rfl)
    component92Node2_sound component92Node5_sound

private noncomputable def component92Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (9/32), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component92Node7_sound : Sound component92Node7Box :=
  sound_of_literal_split component92Node7Box leaf4505Box leaf4506Box
    .chi (73/256) (by rfl) (by rfl)
    leaf4505FlatSound leaf4506FlatSound

private noncomputable def component92Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (9/32), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component92Node8_sound : Sound component92Node8Box :=
  sound_of_literal_split component92Node8Box leaf4507Box leaf4508Box
    .chi (73/256) (by rfl) (by rfl)
    leaf4507FlatSound leaf4508FlatSound

private noncomputable def component92Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (9/32), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component92Node9_sound : Sound component92Node9Box :=
  sound_of_literal_split component92Node9Box component92Node7Box component92Node8Box
    .k (107/32) (by rfl) (by rfl)
    component92Node7_sound component92Node8_sound

private noncomputable def component92Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (37/128), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component92Node10_sound : Sound component92Node10Box :=
  sound_of_literal_split component92Node10Box leaf4509Box leaf4510Box
    .chi (75/256) (by rfl) (by rfl)
    leaf4509FlatSound leaf4510FlatSound

private noncomputable def component92Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (37/128), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component92Node11_sound : Sound component92Node11Box :=
  sound_of_literal_split component92Node11Box leaf4511Box leaf4512Box
    .chi (75/256) (by rfl) (by rfl)
    leaf4511FlatSound leaf4512FlatSound

private noncomputable def component92Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (37/128), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component92Node12_sound : Sound component92Node12Box :=
  sound_of_literal_split component92Node12Box component92Node10Box component92Node11Box
    .k (107/32) (by rfl) (by rfl)
    component92Node10_sound component92Node11_sound

private noncomputable def component92Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component92Node13_sound : Sound component92Node13Box :=
  sound_of_literal_split component92Node13Box component92Node9Box component92Node12Box
    .chi (37/128) (by rfl) (by rfl)
    component92Node9_sound component92Node12_sound

private noncomputable def component92Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component92Node14_sound : Sound component92Node14Box :=
  sound_of_literal_split component92Node14Box component92Node6Box component92Node13Box
    .k (53/16) (by rfl) (by rfl)
    component92Node6_sound component92Node13_sound

private noncomputable def component92Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (19/64), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component92Node15_sound : Sound component92Node15Box :=
  sound_of_literal_split component92Node15Box leaf4513Box leaf4514Box
    .chi (77/256) (by rfl) (by rfl)
    leaf4513FlatSound leaf4514FlatSound

private noncomputable def component92Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (19/64), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component92Node16_sound : Sound component92Node16Box :=
  sound_of_literal_split component92Node16Box leaf4515Box leaf4516Box
    .chi (77/256) (by rfl) (by rfl)
    leaf4515FlatSound leaf4516FlatSound

private noncomputable def component92Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (19/64), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component92Node17_sound : Sound component92Node17Box :=
  sound_of_literal_split component92Node17Box component92Node15Box component92Node16Box
    .k (105/32) (by rfl) (by rfl)
    component92Node15_sound component92Node16_sound

private noncomputable def component92Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (39/128), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component92Node18_sound : Sound component92Node18Box :=
  sound_of_literal_split component92Node18Box leaf4517Box leaf4518Box
    .chi (79/256) (by rfl) (by rfl)
    leaf4517FlatSound leaf4518FlatSound

private noncomputable def component92Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (39/128), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component92Node19_sound : Sound component92Node19Box :=
  sound_of_literal_split component92Node19Box leaf4519Box leaf4520Box
    .chi (79/256) (by rfl) (by rfl)
    leaf4519FlatSound leaf4520FlatSound

private noncomputable def component92Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (39/128), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component92Node20_sound : Sound component92Node20Box :=
  sound_of_literal_split component92Node20Box component92Node18Box component92Node19Box
    .k (105/32) (by rfl) (by rfl)
    component92Node18_sound component92Node19_sound

private noncomputable def component92Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (19/64), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component92Node21_sound : Sound component92Node21Box :=
  sound_of_literal_split component92Node21Box component92Node17Box component92Node20Box
    .chi (39/128) (by rfl) (by rfl)
    component92Node17_sound component92Node20_sound

private noncomputable def component92Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (19/64), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component92Node22_sound : Sound component92Node22Box :=
  sound_of_literal_split component92Node22Box leaf4521Box leaf4522Box
    .chi (77/256) (by rfl) (by rfl)
    leaf4521FlatSound leaf4522FlatSound

private noncomputable def component92Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (19/64), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component92Node23_sound : Sound component92Node23Box :=
  sound_of_literal_split component92Node23Box leaf4523Box leaf4524Box
    .chi (77/256) (by rfl) (by rfl)
    leaf4523FlatSound leaf4524FlatSound

private noncomputable def component92Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (19/64), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component92Node24_sound : Sound component92Node24Box :=
  sound_of_literal_split component92Node24Box component92Node22Box component92Node23Box
    .k (107/32) (by rfl) (by rfl)
    component92Node22_sound component92Node23_sound

private noncomputable def component92Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (39/128), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component92Node25_sound : Sound component92Node25Box :=
  sound_of_literal_split component92Node25Box leaf4525Box leaf4526Box
    .chi (79/256) (by rfl) (by rfl)
    leaf4525FlatSound leaf4526FlatSound

private noncomputable def component92Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (39/128), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component92Node26_sound : Sound component92Node26Box :=
  sound_of_literal_split component92Node26Box leaf4527Box leaf4528Box
    .chi (79/256) (by rfl) (by rfl)
    leaf4527FlatSound leaf4528FlatSound

private noncomputable def component92Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (39/128), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component92Node27_sound : Sound component92Node27Box :=
  sound_of_literal_split component92Node27Box component92Node25Box component92Node26Box
    .k (107/32) (by rfl) (by rfl)
    component92Node25_sound component92Node26_sound

private noncomputable def component92Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (19/64), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component92Node28_sound : Sound component92Node28Box :=
  sound_of_literal_split component92Node28Box component92Node24Box component92Node27Box
    .chi (39/128) (by rfl) (by rfl)
    component92Node24_sound component92Node27_sound

private noncomputable def component92Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (19/64), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component92Node29_sound : Sound component92Node29Box :=
  sound_of_literal_split component92Node29Box component92Node21Box component92Node28Box
    .k (53/16) (by rfl) (by rfl)
    component92Node21_sound component92Node28_sound

noncomputable def component92Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (9/32), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
theorem component92_sound : Sound component92Box :=
  sound_of_literal_split component92Box component92Node14Box component92Node29Box
    .chi (19/64) (by rfl) (by rfl)
    component92Node14_sound component92Node29_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
