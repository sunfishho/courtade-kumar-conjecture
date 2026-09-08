import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch2
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

private noncomputable def leaf1115Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (1/8), chiHi := (17/128) }

private noncomputable def leaf1115Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435667/268435456) }, vSqrt := { lower := (32765/32768), upper := (67108928/67107351) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (360671535/268435456) }, upper := { exponent := 0, mantissa := (5609/4096) } }, logOuter := sk107LogOuterCertificate, logK := sk107LogKCertificate, logChi := chi107LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (134216279/134214702) } }, logDArg := sk107LogDArgCertificate }

private noncomputable def leaf1115InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1115LocalValidity :
    LeafFacts leaf1115Box leaf1115Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1115Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (67108928/67107351) }) = true
      norm_num [leaf1115Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1115CertificateValid :
    WideCertificateValid leaf1115Box leaf1115Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk107ValidityFacts chi107ValidityFacts
    leaf1115LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1115CoverageChecked :
    coverageCheck (innerAD leaf1115Box) leaf1115InnerLog = true := by
  rfl'

private theorem leaf1115InnerLogValid :
    leaf1115InnerLog.Valid 8 (innerAD leaf1115Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1115CoverageChecked

private noncomputable def leaf1115InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814639/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1115InputLogOnePlusV_eq :
    leaf1115InputLogOnePlusV = outerEnclosure 24
      (leaf1115Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1115RoundedFacts : LeafRoundedFacts 8
    leaf1115Certificate.logOnePlusV leaf1115InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1115InputLogOnePlusV_eq }

private noncomputable def leaf1115Inputs : Inputs :=
  inputsOfCaches globalInput sk107RoundedInputs
    chi107InputQChi innerPair21Input
    leaf1115InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1115LowerChecked :
    lowerCheck 24 leaf1115Box leaf1115Inputs = true := by
  rfl'

private theorem leaf1115CoversExact : CoversExact 8
    leaf1115Box leaf1115Certificate leaf1115InnerLog leaf1115Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk107RoundedFacts chi107RoundedFacts
    innerPair21RoundedFacts leaf1115RoundedFacts (by rfl)

private theorem leaf1115FlatSound : Sound leaf1115Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1115CertificateValid
    leaf1115InnerLogValid leaf1115CoversExact leaf1115LowerChecked

private noncomputable def leaf1116Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (1/8), chiHi := (17/128) }

private noncomputable def leaf1116Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435669/268435456) }, vSqrt := { lower := (32765/32768), upper := (33554464/33553667) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (361720045/268435456) }, upper := { exponent := 0, mantissa := (2813/2048) } }, logOuter := sk108LogOuterCertificate, logK := sk108LogKCertificate, logChi := chi107LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (67108131/67107334) } }, logDArg := sk108LogDArgCertificate }

private noncomputable def leaf1116InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1116LocalValidity :
    LeafFacts leaf1116Box leaf1116Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1116Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (33554464/33553667) }) = true
      norm_num [leaf1116Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1116CertificateValid :
    WideCertificateValid leaf1116Box leaf1116Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk108ValidityFacts chi107ValidityFacts
    leaf1116LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1116CoverageChecked :
    coverageCheck (innerAD leaf1116Box) leaf1116InnerLog = true := by
  rfl'

private theorem leaf1116InnerLogValid :
    leaf1116InnerLog.Valid 8 (innerAD leaf1116Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1116CoverageChecked

private noncomputable def leaf1116InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (363415/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf1116InputLogOnePlusV_eq :
    leaf1116InputLogOnePlusV = outerEnclosure 24
      (leaf1116Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1116RoundedFacts : LeafRoundedFacts 8
    leaf1116Certificate.logOnePlusV leaf1116InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1116InputLogOnePlusV_eq }

private noncomputable def leaf1116Inputs : Inputs :=
  inputsOfCaches globalInput sk108RoundedInputs
    chi107InputQChi innerPair21Input
    leaf1116InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1116LowerChecked :
    lowerCheck 24 leaf1116Box leaf1116Inputs = true := by
  rfl'

private theorem leaf1116CoversExact : CoversExact 8
    leaf1116Box leaf1116Certificate leaf1116InnerLog leaf1116Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk108RoundedFacts chi107RoundedFacts
    innerPair21RoundedFacts leaf1116RoundedFacts (by rfl)

private theorem leaf1116FlatSound : Sound leaf1116Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1116CertificateValid
    leaf1116InnerLogValid leaf1116CoversExact leaf1116LowerChecked

private noncomputable def leaf1117Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (17/128), chiHi := (9/64) }

private noncomputable def leaf1117Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435669/268435456) }, vSqrt := { lower := (32765/32768), upper := (1973792/1973743) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (366438349/268435456) }, upper := { exponent := 0, mantissa := (2849/2048) } }, logOuter := sk107LogOuterCertificate, logK := sk107LogKCertificate, logChi := chi108LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (3947535/3947486) } }, logDArg := sk107LogDArgCertificate }

private noncomputable def leaf1117InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf1117LocalValidity :
    LeafFacts leaf1117Box leaf1117Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1117Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (1973792/1973743) }) = true
      norm_num [leaf1117Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1117CertificateValid :
    WideCertificateValid leaf1117Box leaf1117Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk107ValidityFacts chi108ValidityFacts
    leaf1117LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1117CoverageChecked :
    coverageCheck (innerAD leaf1117Box) leaf1117InnerLog = true := by
  rfl'

private theorem leaf1117InnerLogValid :
    leaf1117InnerLog.Valid 8 (innerAD leaf1117Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf1117CoverageChecked

private noncomputable def leaf1117InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629289/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1117InputLogOnePlusV_eq :
    leaf1117InputLogOnePlusV = outerEnclosure 24
      (leaf1117Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1117RoundedFacts : LeafRoundedFacts 8
    leaf1117Certificate.logOnePlusV leaf1117InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1117InputLogOnePlusV_eq }

private noncomputable def leaf1117Inputs : Inputs :=
  inputsOfCaches globalInput sk107RoundedInputs
    chi108InputQChi innerPair22Input
    leaf1117InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1117LowerChecked :
    lowerCheck 24 leaf1117Box leaf1117Inputs = true := by
  rfl'

private theorem leaf1117CoversExact : CoversExact 8
    leaf1117Box leaf1117Certificate leaf1117InnerLog leaf1117Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk107RoundedFacts chi108RoundedFacts
    innerPair22RoundedFacts leaf1117RoundedFacts (by rfl)

private theorem leaf1117FlatSound : Sound leaf1117Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1117CertificateValid
    leaf1117InnerLogValid leaf1117CoversExact leaf1117LowerChecked

private noncomputable def leaf1118Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (17/128), chiHi := (9/64) }

private noncomputable def leaf1118Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435671/268435456) }, vSqrt := { lower := (32765/32768), upper := (16777232/16776811) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (367552391/268435456) }, upper := { exponent := 0, mantissa := (1429/1024) } }, logOuter := sk108LogOuterCertificate, logK := sk108LogKCertificate, logChi := chi108LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (33554043/33553622) } }, logDArg := sk108LogDArgCertificate }

private noncomputable def leaf1118InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf1118LocalValidity :
    LeafFacts leaf1118Box leaf1118Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1118Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (16777232/16776811) }) = true
      norm_num [leaf1118Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1118CertificateValid :
    WideCertificateValid leaf1118Box leaf1118Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk108ValidityFacts chi108ValidityFacts
    leaf1118LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1118CoverageChecked :
    coverageCheck (innerAD leaf1118Box) leaf1118InnerLog = true := by
  rfl'

private theorem leaf1118InnerLogValid :
    leaf1118InnerLog.Valid 8 (innerAD leaf1118Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf1118CoverageChecked

private noncomputable def leaf1118InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629291/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1118InputLogOnePlusV_eq :
    leaf1118InputLogOnePlusV = outerEnclosure 24
      (leaf1118Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1118RoundedFacts : LeafRoundedFacts 8
    leaf1118Certificate.logOnePlusV leaf1118InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1118InputLogOnePlusV_eq }

private noncomputable def leaf1118Inputs : Inputs :=
  inputsOfCaches globalInput sk108RoundedInputs
    chi108InputQChi innerPair22Input
    leaf1118InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1118LowerChecked :
    lowerCheck 24 leaf1118Box leaf1118Inputs = true := by
  rfl'

private theorem leaf1118CoversExact : CoversExact 8
    leaf1118Box leaf1118Certificate leaf1118InnerLog leaf1118Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk108RoundedFacts chi108RoundedFacts
    innerPair22RoundedFacts leaf1118RoundedFacts (by rfl)

private theorem leaf1118FlatSound : Sound leaf1118Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1118CertificateValid
    leaf1118InnerLogValid leaf1118CoversExact leaf1118LowerChecked

private noncomputable def leaf1119Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32), chiLo := (1/8), chiHi := (17/128) }

private noncomputable def leaf1119Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435671/268435456) }, vSqrt := { lower := (32765/32768), upper := (67108928/67107317) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (362768555/268435456) }, upper := { exponent := 0, mantissa := (5643/4096) } }, logOuter := sk109LogOuterCertificate, logK := sk109LogKCertificate, logChi := chi107LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (134216245/134214634) } }, logDArg := sk109LogDArgCertificate }

private noncomputable def leaf1119InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf1119LocalValidity :
    LeafFacts leaf1119Box leaf1119Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1119Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (67108928/67107317) }) = true
      norm_num [leaf1119Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1119CertificateValid :
    WideCertificateValid leaf1119Box leaf1119Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk109ValidityFacts chi107ValidityFacts
    leaf1119LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1119CoverageChecked :
    coverageCheck (innerAD leaf1119Box) leaf1119InnerLog = true := by
  rfl'

private theorem leaf1119InnerLogValid :
    leaf1119InnerLog.Valid 8 (innerAD leaf1119Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf1119CoverageChecked

private noncomputable def leaf1119InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814641/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1119InputLogOnePlusV_eq :
    leaf1119InputLogOnePlusV = outerEnclosure 24
      (leaf1119Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1119RoundedFacts : LeafRoundedFacts 8
    leaf1119Certificate.logOnePlusV leaf1119InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1119InputLogOnePlusV_eq }

private noncomputable def leaf1119Inputs : Inputs :=
  inputsOfCaches globalInput sk109RoundedInputs
    chi107InputQChi innerPair22Input
    leaf1119InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1119LowerChecked :
    lowerCheck 24 leaf1119Box leaf1119Inputs = true := by
  rfl'

private theorem leaf1119CoversExact : CoversExact 8
    leaf1119Box leaf1119Certificate leaf1119InnerLog leaf1119Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk109RoundedFacts chi107RoundedFacts
    innerPair22RoundedFacts leaf1119RoundedFacts (by rfl)

private theorem leaf1119FlatSound : Sound leaf1119Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1119CertificateValid
    leaf1119InnerLogValid leaf1119CoversExact leaf1119LowerChecked

private noncomputable def leaf1120Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8), chiLo := (1/8), chiHi := (17/128) }

private noncomputable def leaf1120Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435673/268435456) }, vSqrt := { lower := (32765/32768), upper := (16777232/16776825) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (363817065/268435456) }, upper := { exponent := 0, mantissa := (1415/1024) } }, logOuter := sk110LogOuterCertificate, logK := sk110LogKCertificate, logChi := chi107LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (33554057/33553650) } }, logDArg := sk110LogDArgCertificate }

private noncomputable def leaf1120InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf1120LocalValidity :
    LeafFacts leaf1120Box leaf1120Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1120Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (16777232/16776825) }) = true
      norm_num [leaf1120Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1120CertificateValid :
    WideCertificateValid leaf1120Box leaf1120Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk110ValidityFacts chi107ValidityFacts
    leaf1120LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1120CoverageChecked :
    coverageCheck (innerAD leaf1120Box) leaf1120InnerLog = true := by
  rfl'

private theorem leaf1120InnerLogValid :
    leaf1120InnerLog.Valid 8 (innerAD leaf1120Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf1120CoverageChecked

private noncomputable def leaf1120InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907321/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1120InputLogOnePlusV_eq :
    leaf1120InputLogOnePlusV = outerEnclosure 24
      (leaf1120Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1120RoundedFacts : LeafRoundedFacts 8
    leaf1120Certificate.logOnePlusV leaf1120InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1120InputLogOnePlusV_eq }

private noncomputable def leaf1120Inputs : Inputs :=
  inputsOfCaches globalInput sk110RoundedInputs
    chi107InputQChi innerPair22Input
    leaf1120InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1120LowerChecked :
    lowerCheck 24 leaf1120Box leaf1120Inputs = true := by
  rfl'

private theorem leaf1120CoversExact : CoversExact 8
    leaf1120Box leaf1120Certificate leaf1120InnerLog leaf1120Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk110RoundedFacts chi107RoundedFacts
    innerPair22RoundedFacts leaf1120RoundedFacts (by rfl)

private theorem leaf1120FlatSound : Sound leaf1120Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1120CertificateValid
    leaf1120InnerLogValid leaf1120CoversExact leaf1120LowerChecked

private noncomputable def leaf1121Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32), chiLo := (17/128), chiHi := (9/64) }

private noncomputable def leaf1121Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435673/268435456) }, vSqrt := { lower := (32765/32768), upper := (33554464/33553613) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (368666433/268435456) }, upper := { exponent := 0, mantissa := (2867/2048) } }, logOuter := sk109LogOuterCertificate, logK := sk109LogKCertificate, logChi := chi108LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (67108077/67107226) } }, logDArg := sk109LogDArgCertificate }

private noncomputable def leaf1121InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf1121LocalValidity :
    LeafFacts leaf1121Box leaf1121Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1121Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (33554464/33553613) }) = true
      norm_num [leaf1121Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1121CertificateValid :
    WideCertificateValid leaf1121Box leaf1121Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk109ValidityFacts chi108ValidityFacts
    leaf1121LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1121CoverageChecked :
    coverageCheck (innerAD leaf1121Box) leaf1121InnerLog = true := by
  rfl'

private theorem leaf1121InnerLogValid :
    leaf1121InnerLog.Valid 8 (innerAD leaf1121Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf1121CoverageChecked

private noncomputable def leaf1121InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629293/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1121InputLogOnePlusV_eq :
    leaf1121InputLogOnePlusV = outerEnclosure 24
      (leaf1121Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1121RoundedFacts : LeafRoundedFacts 8
    leaf1121Certificate.logOnePlusV leaf1121InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1121InputLogOnePlusV_eq }

private noncomputable def leaf1121Inputs : Inputs :=
  inputsOfCaches globalInput sk109RoundedInputs
    chi108InputQChi innerPair22Input
    leaf1121InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1121LowerChecked :
    lowerCheck 24 leaf1121Box leaf1121Inputs = true := by
  rfl'

private theorem leaf1121CoversExact : CoversExact 8
    leaf1121Box leaf1121Certificate leaf1121InnerLog leaf1121Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk109RoundedFacts chi108RoundedFacts
    innerPair22RoundedFacts leaf1121RoundedFacts (by rfl)

private theorem leaf1121FlatSound : Sound leaf1121Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1121CertificateValid
    leaf1121InnerLogValid leaf1121CoversExact leaf1121LowerChecked

private noncomputable def leaf1122Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8), chiLo := (17/128), chiHi := (9/64) }

private noncomputable def leaf1122Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435675/268435456) }, vSqrt := { lower := (32765/32768), upper := (8388616/8388401) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (369780475/268435456) }, upper := { exponent := 0, mantissa := (719/512) } }, logOuter := sk110LogOuterCertificate, logK := sk110LogKCertificate, logChi := chi108LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (16777017/16776802) } }, logDArg := sk110LogDArgCertificate }

private noncomputable def leaf1122InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1122LocalValidity :
    LeafFacts leaf1122Box leaf1122Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1122Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8388616/8388401) }) = true
      norm_num [leaf1122Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1122CertificateValid :
    WideCertificateValid leaf1122Box leaf1122Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk110ValidityFacts chi108ValidityFacts
    leaf1122LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1122CoverageChecked :
    coverageCheck (innerAD leaf1122Box) leaf1122InnerLog = true := by
  rfl'

private theorem leaf1122InnerLogValid :
    leaf1122InnerLog.Valid 8 (innerAD leaf1122Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1122CoverageChecked

private noncomputable def leaf1122InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (726831/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf1122InputLogOnePlusV_eq :
    leaf1122InputLogOnePlusV = outerEnclosure 24
      (leaf1122Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1122RoundedFacts : LeafRoundedFacts 8
    leaf1122Certificate.logOnePlusV leaf1122InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1122InputLogOnePlusV_eq }

private noncomputable def leaf1122Inputs : Inputs :=
  inputsOfCaches globalInput sk110RoundedInputs
    chi108InputQChi innerPair26Input
    leaf1122InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1122LowerChecked :
    lowerCheck 24 leaf1122Box leaf1122Inputs = true := by
  rfl'

private theorem leaf1122CoversExact : CoversExact 8
    leaf1122Box leaf1122Certificate leaf1122InnerLog leaf1122Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk110RoundedFacts chi108RoundedFacts
    innerPair26RoundedFacts leaf1122RoundedFacts (by rfl)

private theorem leaf1122FlatSound : Sound leaf1122Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1122CertificateValid
    leaf1122InnerLogValid leaf1122CoversExact leaf1122LowerChecked

private noncomputable def leaf1123Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (9/64), chiHi := (19/128) }

private noncomputable def leaf1123Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435671/268435456) }, vSqrt := { lower := (32765/32768), upper := (67108928/67107173) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (372205163/268435456) }, upper := { exponent := 0, mantissa := (5787/4096) } }, logOuter := sk107LogOuterCertificate, logK := sk107LogKCertificate, logChi := chi109LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (134216101/134214346) } }, logDArg := sk107LogDArgCertificate }

private noncomputable def leaf1123InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1123LocalValidity :
    LeafFacts leaf1123Box leaf1123Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1123Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (67108928/67107173) }) = true
      norm_num [leaf1123Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1123CertificateValid :
    WideCertificateValid leaf1123Box leaf1123Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk107ValidityFacts chi109ValidityFacts
    leaf1123LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1123CoverageChecked :
    coverageCheck (innerAD leaf1123Box) leaf1123InnerLog = true := by
  rfl'

private theorem leaf1123InnerLogValid :
    leaf1123InnerLog.Valid 8 (innerAD leaf1123Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1123CoverageChecked

private noncomputable def leaf1123InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907325/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1123InputLogOnePlusV_eq :
    leaf1123InputLogOnePlusV = outerEnclosure 24
      (leaf1123Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1123RoundedFacts : LeafRoundedFacts 8
    leaf1123Certificate.logOnePlusV leaf1123InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1123InputLogOnePlusV_eq }

private noncomputable def leaf1123Inputs : Inputs :=
  inputsOfCaches globalInput sk107RoundedInputs
    chi109InputQChi innerPair26Input
    leaf1123InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1123LowerChecked :
    lowerCheck 24 leaf1123Box leaf1123Inputs = true := by
  rfl'

private theorem leaf1123CoversExact : CoversExact 8
    leaf1123Box leaf1123Certificate leaf1123InnerLog leaf1123Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk107RoundedFacts chi109RoundedFacts
    innerPair26RoundedFacts leaf1123RoundedFacts (by rfl)

private theorem leaf1123FlatSound : Sound leaf1123Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1123CertificateValid
    leaf1123InnerLogValid leaf1123CoversExact leaf1123LowerChecked

private noncomputable def leaf1124Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (9/64), chiHi := (19/128) }

private noncomputable def leaf1124Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435673/268435456) }, vSqrt := { lower := (32765/32768), upper := (33554464/33553577) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (373384737/268435456) }, upper := { exponent := 0, mantissa := (2903/2048) } }, logOuter := sk108LogOuterCertificate, logK := sk108LogKCertificate, logChi := chi109LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (67108041/67107154) } }, logDArg := sk108LogDArgCertificate }

private noncomputable def leaf1124InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1124LocalValidity :
    LeafFacts leaf1124Box leaf1124Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1124Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (33554464/33553577) }) = true
      norm_num [leaf1124Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1124CertificateValid :
    WideCertificateValid leaf1124Box leaf1124Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk108ValidityFacts chi109ValidityFacts
    leaf1124LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1124CoverageChecked :
    coverageCheck (innerAD leaf1124Box) leaf1124InnerLog = true := by
  rfl'

private theorem leaf1124InnerLogValid :
    leaf1124InnerLog.Valid 8 (innerAD leaf1124Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1124CoverageChecked

private noncomputable def leaf1124InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814651/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1124InputLogOnePlusV_eq :
    leaf1124InputLogOnePlusV = outerEnclosure 24
      (leaf1124Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1124RoundedFacts : LeafRoundedFacts 8
    leaf1124Certificate.logOnePlusV leaf1124InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1124InputLogOnePlusV_eq }

private noncomputable def leaf1124Inputs : Inputs :=
  inputsOfCaches globalInput sk108RoundedInputs
    chi109InputQChi innerPair26Input
    leaf1124InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1124LowerChecked :
    lowerCheck 24 leaf1124Box leaf1124Inputs = true := by
  rfl'

private theorem leaf1124CoversExact : CoversExact 8
    leaf1124Box leaf1124Certificate leaf1124InnerLog leaf1124Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk108RoundedFacts chi109RoundedFacts
    innerPair26RoundedFacts leaf1124RoundedFacts (by rfl)

private theorem leaf1124FlatSound : Sound leaf1124Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1124CertificateValid
    leaf1124InnerLogValid leaf1124CoversExact leaf1124LowerChecked

private noncomputable def leaf1125Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (19/128), chiHi := (5/32) }

private noncomputable def leaf1125Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435673/268435456) }, vSqrt := { lower := (32765/32768), upper := (16777232/16776771) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (377971977/268435456) }, upper := { exponent := 0, mantissa := (1469/1024) } }, logOuter := sk107LogOuterCertificate, logK := sk107LogKCertificate, logChi := chi110LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (33554003/33553542) } }, logDArg := sk107LogDArgCertificate }

private noncomputable def leaf1125InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1125LocalValidity :
    LeafFacts leaf1125Box leaf1125Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1125Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (16777232/16776771) }) = true
      norm_num [leaf1125Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1125CertificateValid :
    WideCertificateValid leaf1125Box leaf1125Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk107ValidityFacts chi110ValidityFacts
    leaf1125LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1125CoverageChecked :
    coverageCheck (innerAD leaf1125Box) leaf1125InnerLog = true := by
  rfl'

private theorem leaf1125InnerLogValid :
    leaf1125InnerLog.Valid 8 (innerAD leaf1125Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1125CoverageChecked

private noncomputable def leaf1125InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629311/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1125InputLogOnePlusV_eq :
    leaf1125InputLogOnePlusV = outerEnclosure 24
      (leaf1125Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1125RoundedFacts : LeafRoundedFacts 8
    leaf1125Certificate.logOnePlusV leaf1125InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1125InputLogOnePlusV_eq }

private noncomputable def leaf1125Inputs : Inputs :=
  inputsOfCaches globalInput sk107RoundedInputs
    chi110InputQChi innerPair26Input
    leaf1125InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1125LowerChecked :
    lowerCheck 24 leaf1125Box leaf1125Inputs = true := by
  rfl'

private theorem leaf1125CoversExact : CoversExact 8
    leaf1125Box leaf1125Certificate leaf1125InnerLog leaf1125Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk107RoundedFacts chi110RoundedFacts
    innerPair26RoundedFacts leaf1125RoundedFacts (by rfl)

private theorem leaf1125FlatSound : Sound leaf1125Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1125CertificateValid
    leaf1125InnerLogValid leaf1125CoversExact leaf1125LowerChecked

private noncomputable def leaf1126Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (19/128), chiHi := (5/32) }

private noncomputable def leaf1126Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435675/268435456) }, vSqrt := { lower := (32765/32768), upper := (8388616/8388383) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (379217083/268435456) }, upper := { exponent := 0, mantissa := (737/512) } }, logOuter := sk108LogOuterCertificate, logK := sk108LogKCertificate, logChi := chi110LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (16776999/16776766) } }, logDArg := sk108LogDArgCertificate }

private noncomputable def leaf1126InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf1126LocalValidity :
    LeafFacts leaf1126Box leaf1126Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1126Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8388616/8388383) }) = true
      norm_num [leaf1126Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1126CertificateValid :
    WideCertificateValid leaf1126Box leaf1126Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk108ValidityFacts chi110ValidityFacts
    leaf1126LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1126CoverageChecked :
    coverageCheck (innerAD leaf1126Box) leaf1126InnerLog = true := by
  rfl'

private theorem leaf1126InnerLogValid :
    leaf1126InnerLog.Valid 8 (innerAD leaf1126Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf1126CoverageChecked

private noncomputable def leaf1126InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814657/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1126InputLogOnePlusV_eq :
    leaf1126InputLogOnePlusV = outerEnclosure 24
      (leaf1126Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1126RoundedFacts : LeafRoundedFacts 8
    leaf1126Certificate.logOnePlusV leaf1126InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1126InputLogOnePlusV_eq }

private noncomputable def leaf1126Inputs : Inputs :=
  inputsOfCaches globalInput sk108RoundedInputs
    chi110InputQChi innerPair27Input
    leaf1126InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1126LowerChecked :
    lowerCheck 24 leaf1126Box leaf1126Inputs = true := by
  rfl'

private theorem leaf1126CoversExact : CoversExact 8
    leaf1126Box leaf1126Certificate leaf1126InnerLog leaf1126Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk108RoundedFacts chi110RoundedFacts
    innerPair27RoundedFacts leaf1126RoundedFacts (by rfl)

private theorem leaf1126FlatSound : Sound leaf1126Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1126CertificateValid
    leaf1126InnerLogValid leaf1126CoversExact leaf1126LowerChecked

private noncomputable def leaf1127Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32), chiLo := (9/64), chiHi := (19/128) }

private noncomputable def leaf1127Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435675/268435456) }, vSqrt := { lower := (32765/32768), upper := (67108928/67107135) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (374564311/268435456) }, upper := { exponent := 0, mantissa := (5825/4096) } }, logOuter := sk109LogOuterCertificate, logK := sk109LogKCertificate, logChi := chi109LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (134216063/134214270) } }, logDArg := sk109LogDArgCertificate }

private noncomputable def leaf1127InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1127LocalValidity :
    LeafFacts leaf1127Box leaf1127Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1127Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (67108928/67107135) }) = true
      norm_num [leaf1127Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1127CertificateValid :
    WideCertificateValid leaf1127Box leaf1127Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk109ValidityFacts chi109ValidityFacts
    leaf1127LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1127CoverageChecked :
    coverageCheck (innerAD leaf1127Box) leaf1127InnerLog = true := by
  rfl'

private theorem leaf1127InnerLogValid :
    leaf1127InnerLog.Valid 8 (innerAD leaf1127Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1127CoverageChecked

private noncomputable def leaf1127InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629305/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1127InputLogOnePlusV_eq :
    leaf1127InputLogOnePlusV = outerEnclosure 24
      (leaf1127Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1127RoundedFacts : LeafRoundedFacts 8
    leaf1127Certificate.logOnePlusV leaf1127InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1127InputLogOnePlusV_eq }

private noncomputable def leaf1127Inputs : Inputs :=
  inputsOfCaches globalInput sk109RoundedInputs
    chi109InputQChi innerPair26Input
    leaf1127InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1127LowerChecked :
    lowerCheck 24 leaf1127Box leaf1127Inputs = true := by
  rfl'

private theorem leaf1127CoversExact : CoversExact 8
    leaf1127Box leaf1127Certificate leaf1127InnerLog leaf1127Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk109RoundedFacts chi109RoundedFacts
    innerPair26RoundedFacts leaf1127RoundedFacts (by rfl)

private theorem leaf1127FlatSound : Sound leaf1127Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1127CertificateValid
    leaf1127InnerLogValid leaf1127CoversExact leaf1127LowerChecked

private noncomputable def leaf1128Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8), chiLo := (9/64), chiHi := (19/128) }

private noncomputable def leaf1128Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435677/268435456) }, vSqrt := { lower := (32765/32768), upper := (16777232/16776779) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (375743885/268435456) }, upper := { exponent := 0, mantissa := (1461/1024) } }, logOuter := sk110LogOuterCertificate, logK := sk110LogKCertificate, logChi := chi109LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (33554011/33553558) } }, logDArg := sk110LogDArgCertificate }

private noncomputable def leaf1128InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1128LocalValidity :
    LeafFacts leaf1128Box leaf1128Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1128Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (16777232/16776779) }) = true
      norm_num [leaf1128Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1128CertificateValid :
    WideCertificateValid leaf1128Box leaf1128Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk110ValidityFacts chi109ValidityFacts
    leaf1128LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1128CoverageChecked :
    coverageCheck (innerAD leaf1128Box) leaf1128InnerLog = true := by
  rfl'

private theorem leaf1128InnerLogValid :
    leaf1128InnerLog.Valid 8 (innerAD leaf1128Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1128CoverageChecked

private noncomputable def leaf1128InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629307/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1128InputLogOnePlusV_eq :
    leaf1128InputLogOnePlusV = outerEnclosure 24
      (leaf1128Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1128RoundedFacts : LeafRoundedFacts 8
    leaf1128Certificate.logOnePlusV leaf1128InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1128InputLogOnePlusV_eq }

private noncomputable def leaf1128Inputs : Inputs :=
  inputsOfCaches globalInput sk110RoundedInputs
    chi109InputQChi innerPair26Input
    leaf1128InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1128LowerChecked :
    lowerCheck 24 leaf1128Box leaf1128Inputs = true := by
  rfl'

private theorem leaf1128CoversExact : CoversExact 8
    leaf1128Box leaf1128Certificate leaf1128InnerLog leaf1128Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk110RoundedFacts chi109RoundedFacts
    innerPair26RoundedFacts leaf1128RoundedFacts (by rfl)

private theorem leaf1128FlatSound : Sound leaf1128Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1128CertificateValid
    leaf1128InnerLogValid leaf1128CoversExact leaf1128LowerChecked

private noncomputable def leaf1129Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32), chiLo := (19/128), chiHi := (5/32) }

private noncomputable def leaf1129Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435677/268435456) }, vSqrt := { lower := (32765/32768), upper := (16777232/16776761) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (380462189/268435456) }, upper := { exponent := 0, mantissa := (1479/1024) } }, logOuter := sk109LogOuterCertificate, logK := sk109LogKCertificate, logChi := chi110LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (33553993/33553522) } }, logDArg := sk109LogDArgCertificate }

private noncomputable def leaf1129InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf1129LocalValidity :
    LeafFacts leaf1129Box leaf1129Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1129Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (16777232/16776761) }) = true
      norm_num [leaf1129Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1129CertificateValid :
    WideCertificateValid leaf1129Box leaf1129Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk109ValidityFacts chi110ValidityFacts
    leaf1129LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1129CoverageChecked :
    coverageCheck (innerAD leaf1129Box) leaf1129InnerLog = true := by
  rfl'

private theorem leaf1129InnerLogValid :
    leaf1129InnerLog.Valid 8 (innerAD leaf1129Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf1129CoverageChecked

private noncomputable def leaf1129InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907329/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1129InputLogOnePlusV_eq :
    leaf1129InputLogOnePlusV = outerEnclosure 24
      (leaf1129Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1129RoundedFacts : LeafRoundedFacts 8
    leaf1129Certificate.logOnePlusV leaf1129InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1129InputLogOnePlusV_eq }

private noncomputable def leaf1129Inputs : Inputs :=
  inputsOfCaches globalInput sk109RoundedInputs
    chi110InputQChi innerPair27Input
    leaf1129InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1129LowerChecked :
    lowerCheck 24 leaf1129Box leaf1129Inputs = true := by
  rfl'

private theorem leaf1129CoversExact : CoversExact 8
    leaf1129Box leaf1129Certificate leaf1129InnerLog leaf1129Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk109RoundedFacts chi110RoundedFacts
    innerPair27RoundedFacts leaf1129RoundedFacts (by rfl)

private theorem leaf1129FlatSound : Sound leaf1129Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1129CertificateValid
    leaf1129InnerLogValid leaf1129CoversExact leaf1129LowerChecked

private noncomputable def leaf1130Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8), chiLo := (19/128), chiHi := (5/32) }

private noncomputable def leaf1130Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435679/268435456) }, vSqrt := { lower := (32765/32768), upper := (246724/246717) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (381707295/268435456) }, upper := { exponent := 0, mantissa := (371/256) } }, logOuter := sk110LogOuterCertificate, logK := sk110LogKCertificate, logChi := chi110LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (493441/493434) } }, logDArg := sk110LogDArgCertificate }

private noncomputable def leaf1130InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf1130LocalValidity :
    LeafFacts leaf1130Box leaf1130Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1130Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (246724/246717) }) = true
      norm_num [leaf1130Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1130CertificateValid :
    WideCertificateValid leaf1130Box leaf1130Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk110ValidityFacts chi110ValidityFacts
    leaf1130LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1130CoverageChecked :
    coverageCheck (innerAD leaf1130Box) leaf1130InnerLog = true := by
  rfl'

private theorem leaf1130InnerLogValid :
    leaf1130InnerLog.Valid 8 (innerAD leaf1130Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf1130CoverageChecked

private noncomputable def leaf1130InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629319/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1130InputLogOnePlusV_eq :
    leaf1130InputLogOnePlusV = outerEnclosure 24
      (leaf1130Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1130RoundedFacts : LeafRoundedFacts 8
    leaf1130Certificate.logOnePlusV leaf1130InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1130InputLogOnePlusV_eq }

private noncomputable def leaf1130Inputs : Inputs :=
  inputsOfCaches globalInput sk110RoundedInputs
    chi110InputQChi innerPair27Input
    leaf1130InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1130LowerChecked :
    lowerCheck 24 leaf1130Box leaf1130Inputs = true := by
  rfl'

private theorem leaf1130CoversExact : CoversExact 8
    leaf1130Box leaf1130Certificate leaf1130InnerLog leaf1130Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk110RoundedFacts chi110RoundedFacts
    innerPair27RoundedFacts leaf1130RoundedFacts (by rfl)

private theorem leaf1130FlatSound : Sound leaf1130Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1130CertificateValid
    leaf1130InnerLogValid leaf1130CoversExact leaf1130LowerChecked

private noncomputable def leaf1131Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32), chiLo := (1/8), chiHi := (17/128) }

private noncomputable def leaf1131Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435675/268435456) }, vSqrt := { lower := (32765/32768), upper := (67108928/67107283) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (364865575/268435456) }, upper := { exponent := 0, mantissa := (5677/4096) } }, logOuter := sk111LogOuterCertificate, logK := sk111LogKCertificate, logChi := chi107LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (134216211/134214566) } }, logDArg := sk111LogDArgCertificate }

private noncomputable def leaf1131InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf1131LocalValidity :
    LeafFacts leaf1131Box leaf1131Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1131Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (67108928/67107283) }) = true
      norm_num [leaf1131Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1131CertificateValid :
    WideCertificateValid leaf1131Box leaf1131Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk111ValidityFacts chi107ValidityFacts
    leaf1131LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1131CoverageChecked :
    coverageCheck (innerAD leaf1131Box) leaf1131InnerLog = true := by
  rfl'

private theorem leaf1131InnerLogValid :
    leaf1131InnerLog.Valid 8 (innerAD leaf1131Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf1131CoverageChecked

private noncomputable def leaf1131InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814643/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1131InputLogOnePlusV_eq :
    leaf1131InputLogOnePlusV = outerEnclosure 24
      (leaf1131Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1131RoundedFacts : LeafRoundedFacts 8
    leaf1131Certificate.logOnePlusV leaf1131InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1131InputLogOnePlusV_eq }

private noncomputable def leaf1131Inputs : Inputs :=
  inputsOfCaches globalInput sk111RoundedInputs
    chi107InputQChi innerPair22Input
    leaf1131InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1131LowerChecked :
    lowerCheck 24 leaf1131Box leaf1131Inputs = true := by
  rfl'

private theorem leaf1131CoversExact : CoversExact 8
    leaf1131Box leaf1131Certificate leaf1131InnerLog leaf1131Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk111RoundedFacts chi107RoundedFacts
    innerPair22RoundedFacts leaf1131RoundedFacts (by rfl)

private theorem leaf1131FlatSound : Sound leaf1131Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1131CertificateValid
    leaf1131InnerLogValid leaf1131CoversExact leaf1131LowerChecked

private noncomputable def leaf1132Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16), chiLo := (1/8), chiHi := (17/128) }

private noncomputable def leaf1132Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435677/268435456) }, vSqrt := { lower := (32765/32768), upper := (33554464/33553633) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (365914085/268435456) }, upper := { exponent := 0, mantissa := (2847/2048) } }, logOuter := sk112LogOuterCertificate, logK := sk112LogKCertificate, logChi := chi107LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (67108097/67107266) } }, logDArg := sk112LogDArgCertificate }

private noncomputable def leaf1132InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf1132LocalValidity :
    LeafFacts leaf1132Box leaf1132Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1132Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (33554464/33553633) }) = true
      norm_num [leaf1132Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1132CertificateValid :
    WideCertificateValid leaf1132Box leaf1132Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk112ValidityFacts chi107ValidityFacts
    leaf1132LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1132CoverageChecked :
    coverageCheck (innerAD leaf1132Box) leaf1132InnerLog = true := by
  rfl'

private theorem leaf1132InnerLogValid :
    leaf1132InnerLog.Valid 8 (innerAD leaf1132Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf1132CoverageChecked

private noncomputable def leaf1132InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453661/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1132InputLogOnePlusV_eq :
    leaf1132InputLogOnePlusV = outerEnclosure 24
      (leaf1132Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1132RoundedFacts : LeafRoundedFacts 8
    leaf1132Certificate.logOnePlusV leaf1132InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1132InputLogOnePlusV_eq }

private noncomputable def leaf1132Inputs : Inputs :=
  inputsOfCaches globalInput sk112RoundedInputs
    chi107InputQChi innerPair22Input
    leaf1132InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1132LowerChecked :
    lowerCheck 24 leaf1132Box leaf1132Inputs = true := by
  rfl'

private theorem leaf1132CoversExact : CoversExact 8
    leaf1132Box leaf1132Certificate leaf1132InnerLog leaf1132Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk112RoundedFacts chi107RoundedFacts
    innerPair22RoundedFacts leaf1132RoundedFacts (by rfl)

private theorem leaf1132FlatSound : Sound leaf1132Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1132CertificateValid
    leaf1132InnerLogValid leaf1132CoversExact leaf1132LowerChecked

private noncomputable def leaf1133Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32), chiLo := (17/128), chiHi := (9/64) }

private noncomputable def leaf1133Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435677/268435456) }, vSqrt := { lower := (32765/32768), upper := (33554464/33553595) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (370894517/268435456) }, upper := { exponent := 0, mantissa := (2885/2048) } }, logOuter := sk111LogOuterCertificate, logK := sk111LogKCertificate, logChi := chi108LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (67108059/67107190) } }, logDArg := sk111LogDArgCertificate }

private noncomputable def leaf1133InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1133LocalValidity :
    LeafFacts leaf1133Box leaf1133Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1133Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (33554464/33553595) }) = true
      norm_num [leaf1133Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1133CertificateValid :
    WideCertificateValid leaf1133Box leaf1133Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk111ValidityFacts chi108ValidityFacts
    leaf1133LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1133CoverageChecked :
    coverageCheck (innerAD leaf1133Box) leaf1133InnerLog = true := by
  rfl'

private theorem leaf1133InnerLogValid :
    leaf1133InnerLog.Valid 8 (innerAD leaf1133Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1133CoverageChecked

private noncomputable def leaf1133InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814649/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1133InputLogOnePlusV_eq :
    leaf1133InputLogOnePlusV = outerEnclosure 24
      (leaf1133Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1133RoundedFacts : LeafRoundedFacts 8
    leaf1133Certificate.logOnePlusV leaf1133InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1133InputLogOnePlusV_eq }

private noncomputable def leaf1133Inputs : Inputs :=
  inputsOfCaches globalInput sk111RoundedInputs
    chi108InputQChi innerPair26Input
    leaf1133InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1133LowerChecked :
    lowerCheck 24 leaf1133Box leaf1133Inputs = true := by
  rfl'

private theorem leaf1133CoversExact : CoversExact 8
    leaf1133Box leaf1133Certificate leaf1133InnerLog leaf1133Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk111RoundedFacts chi108RoundedFacts
    innerPair26RoundedFacts leaf1133RoundedFacts (by rfl)

private theorem leaf1133FlatSound : Sound leaf1133Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1133CertificateValid
    leaf1133InnerLogValid leaf1133CoversExact leaf1133LowerChecked

private noncomputable def leaf1134Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16), chiLo := (17/128), chiHi := (9/64) }

private noncomputable def leaf1134Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435679/268435456) }, vSqrt := { lower := (32765/32768), upper := (16777232/16776793) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (372008559/268435456) }, upper := { exponent := 0, mantissa := (1447/1024) } }, logOuter := sk112LogOuterCertificate, logK := sk112LogKCertificate, logChi := chi108LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (33554025/33553586) } }, logDArg := sk112LogDArgCertificate }

private noncomputable def leaf1134InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1134LocalValidity :
    LeafFacts leaf1134Box leaf1134Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1134Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (16777232/16776793) }) = true
      norm_num [leaf1134Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1134CertificateValid :
    WideCertificateValid leaf1134Box leaf1134Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk112ValidityFacts chi108ValidityFacts
    leaf1134LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1134CoverageChecked :
    coverageCheck (innerAD leaf1134Box) leaf1134InnerLog = true := by
  rfl'

private theorem leaf1134InnerLogValid :
    leaf1134InnerLog.Valid 8 (innerAD leaf1134Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1134CoverageChecked

private noncomputable def leaf1134InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907325/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1134InputLogOnePlusV_eq :
    leaf1134InputLogOnePlusV = outerEnclosure 24
      (leaf1134Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1134RoundedFacts : LeafRoundedFacts 8
    leaf1134Certificate.logOnePlusV leaf1134InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1134InputLogOnePlusV_eq }

private noncomputable def leaf1134Inputs : Inputs :=
  inputsOfCaches globalInput sk112RoundedInputs
    chi108InputQChi innerPair26Input
    leaf1134InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1134LowerChecked :
    lowerCheck 24 leaf1134Box leaf1134Inputs = true := by
  rfl'

private theorem leaf1134CoversExact : CoversExact 8
    leaf1134Box leaf1134Certificate leaf1134InnerLog leaf1134Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk112RoundedFacts chi108RoundedFacts
    innerPair26RoundedFacts leaf1134RoundedFacts (by rfl)

private theorem leaf1134FlatSound : Sound leaf1134Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1134CertificateValid
    leaf1134InnerLogValid leaf1134CoversExact leaf1134LowerChecked

private noncomputable def leaf1135Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (95/32), chiLo := (1/8), chiHi := (17/128) }

private noncomputable def leaf1135Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435679/268435456) }, vSqrt := { lower := (32765/32768), upper := (67108928/67107249) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (366962595/268435456) }, upper := { exponent := 0, mantissa := (5711/4096) } }, logOuter := sk113LogOuterCertificate, logK := sk113LogKCertificate, logChi := chi107LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (134216177/134214498) } }, logDArg := sk113LogDArgCertificate }

private noncomputable def leaf1135InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf1135LocalValidity :
    LeafFacts leaf1135Box leaf1135Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1135Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (67108928/67107249) }) = true
      norm_num [leaf1135Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1135CertificateValid :
    WideCertificateValid leaf1135Box leaf1135Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk113ValidityFacts chi107ValidityFacts
    leaf1135LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1135CoverageChecked :
    coverageCheck (innerAD leaf1135Box) leaf1135InnerLog = true := by
  rfl'

private theorem leaf1135InnerLogValid :
    leaf1135InnerLog.Valid 8 (innerAD leaf1135Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf1135CoverageChecked

private noncomputable def leaf1135InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629291/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1135InputLogOnePlusV_eq :
    leaf1135InputLogOnePlusV = outerEnclosure 24
      (leaf1135Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1135RoundedFacts : LeafRoundedFacts 8
    leaf1135Certificate.logOnePlusV leaf1135InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1135InputLogOnePlusV_eq }

private noncomputable def leaf1135Inputs : Inputs :=
  inputsOfCaches globalInput sk113RoundedInputs
    chi107InputQChi innerPair22Input
    leaf1135InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1135LowerChecked :
    lowerCheck 24 leaf1135Box leaf1135Inputs = true := by
  rfl'

private theorem leaf1135CoversExact : CoversExact 8
    leaf1135Box leaf1135Certificate leaf1135InnerLog leaf1135Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk113RoundedFacts chi107RoundedFacts
    innerPair22RoundedFacts leaf1135RoundedFacts (by rfl)

private theorem leaf1135FlatSound : Sound leaf1135Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1135CertificateValid
    leaf1135InnerLogValid leaf1135CoversExact leaf1135LowerChecked

private noncomputable def leaf1136Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (1/8), chiHi := (17/128) }

private noncomputable def leaf1136Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435681/268435456) }, vSqrt := { lower := (65529/65536), upper := (2097154/2097101) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (368011105/268435456) }, upper := { exponent := 0, mantissa := (179/128) } }, logOuter := sk114LogOuterCertificate, logK := sk114LogKCertificate, logChi := chi107LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (4194255/4194202) } }, logDArg := sk114LogDArgCertificate }

private noncomputable def leaf1136InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf1136LocalValidity :
    LeafFacts leaf1136Box leaf1136Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1136Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (2097154/2097101) }) = true
      norm_num [leaf1136Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1136CertificateValid :
    WideCertificateValid leaf1136Box leaf1136Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk114ValidityFacts chi107ValidityFacts
    leaf1136LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1136CoverageChecked :
    coverageCheck (innerAD leaf1136Box) leaf1136InnerLog = true := by
  rfl'

private theorem leaf1136InnerLogValid :
    leaf1136InnerLog.Valid 8 (innerAD leaf1136Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf1136CoverageChecked

private noncomputable def leaf1136InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629293/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1136InputLogOnePlusV_eq :
    leaf1136InputLogOnePlusV = outerEnclosure 24
      (leaf1136Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1136RoundedFacts : LeafRoundedFacts 8
    leaf1136Certificate.logOnePlusV leaf1136InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1136InputLogOnePlusV_eq }

private noncomputable def leaf1136Inputs : Inputs :=
  inputsOfCaches globalInput sk114RoundedInputs
    chi107InputQChi innerPair22Input
    leaf1136InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1136LowerChecked :
    lowerCheck 24 leaf1136Box leaf1136Inputs = true := by
  rfl'

private theorem leaf1136CoversExact : CoversExact 8
    leaf1136Box leaf1136Certificate leaf1136InnerLog leaf1136Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk114RoundedFacts chi107RoundedFacts
    innerPair22RoundedFacts leaf1136RoundedFacts (by rfl)

private theorem leaf1136FlatSound : Sound leaf1136Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1136CertificateValid
    leaf1136InnerLogValid leaf1136CoversExact leaf1136LowerChecked

private noncomputable def leaf1137Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (95/32), chiLo := (17/128), chiHi := (9/64) }

private noncomputable def leaf1137Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435681/268435456) }, vSqrt := { lower := (32765/32768), upper := (33554464/33553577) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (373122601/268435456) }, upper := { exponent := 0, mantissa := (2903/2048) } }, logOuter := sk113LogOuterCertificate, logK := sk113LogKCertificate, logChi := chi108LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (67108041/67107154) } }, logDArg := sk113LogDArgCertificate }

private noncomputable def leaf1137InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1137LocalValidity :
    LeafFacts leaf1137Box leaf1137Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1137Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (33554464/33553577) }) = true
      norm_num [leaf1137Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1137CertificateValid :
    WideCertificateValid leaf1137Box leaf1137Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk113ValidityFacts chi108ValidityFacts
    leaf1137LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1137CoverageChecked :
    coverageCheck (innerAD leaf1137Box) leaf1137InnerLog = true := by
  rfl'

private theorem leaf1137InnerLogValid :
    leaf1137InnerLog.Valid 8 (innerAD leaf1137Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1137CoverageChecked

private noncomputable def leaf1137InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814651/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1137InputLogOnePlusV_eq :
    leaf1137InputLogOnePlusV = outerEnclosure 24
      (leaf1137Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1137RoundedFacts : LeafRoundedFacts 8
    leaf1137Certificate.logOnePlusV leaf1137InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1137InputLogOnePlusV_eq }

private noncomputable def leaf1137Inputs : Inputs :=
  inputsOfCaches globalInput sk113RoundedInputs
    chi108InputQChi innerPair26Input
    leaf1137InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1137LowerChecked :
    lowerCheck 24 leaf1137Box leaf1137Inputs = true := by
  rfl'

private theorem leaf1137CoversExact : CoversExact 8
    leaf1137Box leaf1137Certificate leaf1137InnerLog leaf1137Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk113RoundedFacts chi108RoundedFacts
    innerPair26RoundedFacts leaf1137RoundedFacts (by rfl)

private theorem leaf1137FlatSound : Sound leaf1137Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1137CertificateValid
    leaf1137InnerLogValid leaf1137CoversExact leaf1137LowerChecked

private noncomputable def leaf1138Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (17/128), chiHi := (9/64) }

private noncomputable def leaf1138Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435683/268435456) }, vSqrt := { lower := (65529/65536), upper := (1048577/1048549) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (374236643/268435456) }, upper := { exponent := 0, mantissa := (91/64) } }, logOuter := sk114LogOuterCertificate, logK := sk114LogKCertificate, logChi := chi108LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (1048563/1048549) } }, logDArg := sk114LogDArgCertificate }

private noncomputable def leaf1138InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1138LocalValidity :
    LeafFacts leaf1138Box leaf1138Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1138Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (1048577/1048549) }) = true
      norm_num [leaf1138Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1138CertificateValid :
    WideCertificateValid leaf1138Box leaf1138Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk114ValidityFacts chi108ValidityFacts
    leaf1138LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1138CoverageChecked :
    coverageCheck (innerAD leaf1138Box) leaf1138InnerLog = true := by
  rfl'

private theorem leaf1138InnerLogValid :
    leaf1138InnerLog.Valid 8 (innerAD leaf1138Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1138CoverageChecked

private noncomputable def leaf1138InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629305/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1138InputLogOnePlusV_eq :
    leaf1138InputLogOnePlusV = outerEnclosure 24
      (leaf1138Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1138RoundedFacts : LeafRoundedFacts 8
    leaf1138Certificate.logOnePlusV leaf1138InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1138InputLogOnePlusV_eq }

private noncomputable def leaf1138Inputs : Inputs :=
  inputsOfCaches globalInput sk114RoundedInputs
    chi108InputQChi innerPair26Input
    leaf1138InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1138LowerChecked :
    lowerCheck 24 leaf1138Box leaf1138Inputs = true := by
  rfl'

private theorem leaf1138CoversExact : CoversExact 8
    leaf1138Box leaf1138Certificate leaf1138InnerLog leaf1138Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk114RoundedFacts chi108RoundedFacts
    innerPair26RoundedFacts leaf1138RoundedFacts (by rfl)

private theorem leaf1138FlatSound : Sound leaf1138Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1138CertificateValid
    leaf1138InnerLogValid leaf1138CoversExact leaf1138LowerChecked

private noncomputable def leaf1139Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32), chiLo := (9/64), chiHi := (19/128) }

private noncomputable def leaf1139Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435679/268435456) }, vSqrt := { lower := (32765/32768), upper := (67108928/67107097) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (376923459/268435456) }, upper := { exponent := 0, mantissa := (5863/4096) } }, logOuter := sk111LogOuterCertificate, logK := sk111LogKCertificate, logChi := chi109LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (134216025/134214194) } }, logDArg := sk111LogDArgCertificate }

private noncomputable def leaf1139InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1139LocalValidity :
    LeafFacts leaf1139Box leaf1139Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1139Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (67108928/67107097) }) = true
      norm_num [leaf1139Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1139CertificateValid :
    WideCertificateValid leaf1139Box leaf1139Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk111ValidityFacts chi109ValidityFacts
    leaf1139LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1139CoverageChecked :
    coverageCheck (innerAD leaf1139Box) leaf1139InnerLog = true := by
  rfl'

private theorem leaf1139InnerLogValid :
    leaf1139InnerLog.Valid 8 (innerAD leaf1139Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1139CoverageChecked

private noncomputable def leaf1139InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814655/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1139InputLogOnePlusV_eq :
    leaf1139InputLogOnePlusV = outerEnclosure 24
      (leaf1139Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1139RoundedFacts : LeafRoundedFacts 8
    leaf1139Certificate.logOnePlusV leaf1139InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1139InputLogOnePlusV_eq }

private noncomputable def leaf1139Inputs : Inputs :=
  inputsOfCaches globalInput sk111RoundedInputs
    chi109InputQChi innerPair26Input
    leaf1139InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1139LowerChecked :
    lowerCheck 24 leaf1139Box leaf1139Inputs = true := by
  rfl'

private theorem leaf1139CoversExact : CoversExact 8
    leaf1139Box leaf1139Certificate leaf1139InnerLog leaf1139Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk111RoundedFacts chi109RoundedFacts
    innerPair26RoundedFacts leaf1139RoundedFacts (by rfl)

private theorem leaf1139FlatSound : Sound leaf1139Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1139CertificateValid
    leaf1139InnerLogValid leaf1139CoversExact leaf1139LowerChecked

private noncomputable def leaf1140Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16), chiLo := (9/64), chiHi := (19/128) }

private noncomputable def leaf1140Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435681/268435456) }, vSqrt := { lower := (32765/32768), upper := (33554464/33553539) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (378103033/268435456) }, upper := { exponent := 0, mantissa := (2941/2048) } }, logOuter := sk112LogOuterCertificate, logK := sk112LogKCertificate, logChi := chi109LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (67108003/67107078) } }, logDArg := sk112LogDArgCertificate }

private noncomputable def leaf1140InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1140LocalValidity :
    LeafFacts leaf1140Box leaf1140Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1140Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (33554464/33553539) }) = true
      norm_num [leaf1140Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1140CertificateValid :
    WideCertificateValid leaf1140Box leaf1140Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk112ValidityFacts chi109ValidityFacts
    leaf1140LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1140CoverageChecked :
    coverageCheck (innerAD leaf1140Box) leaf1140InnerLog = true := by
  rfl'

private theorem leaf1140InnerLogValid :
    leaf1140InnerLog.Valid 8 (innerAD leaf1140Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1140CoverageChecked

private noncomputable def leaf1140InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (45427/65536) }

set_option maxRecDepth 1000000 in
private theorem leaf1140InputLogOnePlusV_eq :
    leaf1140InputLogOnePlusV = outerEnclosure 24
      (leaf1140Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1140RoundedFacts : LeafRoundedFacts 8
    leaf1140Certificate.logOnePlusV leaf1140InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1140InputLogOnePlusV_eq }

private noncomputable def leaf1140Inputs : Inputs :=
  inputsOfCaches globalInput sk112RoundedInputs
    chi109InputQChi innerPair26Input
    leaf1140InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1140LowerChecked :
    lowerCheck 24 leaf1140Box leaf1140Inputs = true := by
  rfl'

private theorem leaf1140CoversExact : CoversExact 8
    leaf1140Box leaf1140Certificate leaf1140InnerLog leaf1140Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk112RoundedFacts chi109RoundedFacts
    innerPair26RoundedFacts leaf1140RoundedFacts (by rfl)

private theorem leaf1140FlatSound : Sound leaf1140Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1140CertificateValid
    leaf1140InnerLogValid leaf1140CoversExact leaf1140LowerChecked

private noncomputable def leaf1141Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32), chiLo := (19/128), chiHi := (5/32) }

private noncomputable def leaf1141Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435681/268435456) }, vSqrt := { lower := (32765/32768), upper := (16777232/16776751) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (382952401/268435456) }, upper := { exponent := 0, mantissa := (1489/1024) } }, logOuter := sk111LogOuterCertificate, logK := sk111LogKCertificate, logChi := chi110LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (33553983/33553502) } }, logDArg := sk111LogDArgCertificate }

private noncomputable def leaf1141InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf1141LocalValidity :
    LeafFacts leaf1141Box leaf1141Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1141Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (16777232/16776751) }) = true
      norm_num [leaf1141Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1141CertificateValid :
    WideCertificateValid leaf1141Box leaf1141Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk111ValidityFacts chi110ValidityFacts
    leaf1141LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1141CoverageChecked :
    coverageCheck (innerAD leaf1141Box) leaf1141InnerLog = true := by
  rfl'

private theorem leaf1141InnerLogValid :
    leaf1141InnerLog.Valid 8 (innerAD leaf1141Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf1141CoverageChecked

private noncomputable def leaf1141InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629321/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1141InputLogOnePlusV_eq :
    leaf1141InputLogOnePlusV = outerEnclosure 24
      (leaf1141Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1141RoundedFacts : LeafRoundedFacts 8
    leaf1141Certificate.logOnePlusV leaf1141InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1141InputLogOnePlusV_eq }

private noncomputable def leaf1141Inputs : Inputs :=
  inputsOfCaches globalInput sk111RoundedInputs
    chi110InputQChi innerPair27Input
    leaf1141InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1141LowerChecked :
    lowerCheck 24 leaf1141Box leaf1141Inputs = true := by
  rfl'

private theorem leaf1141CoversExact : CoversExact 8
    leaf1141Box leaf1141Certificate leaf1141InnerLog leaf1141Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk111RoundedFacts chi110RoundedFacts
    innerPair27RoundedFacts leaf1141RoundedFacts (by rfl)

private theorem leaf1141FlatSound : Sound leaf1141Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1141CertificateValid
    leaf1141InnerLogValid leaf1141CoversExact leaf1141LowerChecked

private noncomputable def leaf1142Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16), chiLo := (19/128), chiHi := (5/32) }

private noncomputable def leaf1142Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435683/268435456) }, vSqrt := { lower := (32765/32768), upper := (8388616/8388373) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (384197507/268435456) }, upper := { exponent := 0, mantissa := (747/512) } }, logOuter := sk112LogOuterCertificate, logK := sk112LogKCertificate, logChi := chi110LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (16776989/16776746) } }, logDArg := sk112LogDArgCertificate }

private noncomputable def leaf1142InnerLog : WideLogData :=
  innerPair406Data

set_option maxRecDepth 1000000 in
private theorem leaf1142LocalValidity :
    LeafFacts leaf1142Box leaf1142Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1142Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8388616/8388373) }) = true
      norm_num [leaf1142Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1142CertificateValid :
    WideCertificateValid leaf1142Box leaf1142Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk112ValidityFacts chi110ValidityFacts
    leaf1142LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1142CoverageChecked :
    coverageCheck (innerAD leaf1142Box) leaf1142InnerLog = true := by
  rfl'

private theorem leaf1142InnerLogValid :
    leaf1142InnerLog.Valid 8 (innerAD leaf1142Box) :=
  wideLogDataValid_of_cachedCheck endpoint119PositiveFacts
    endpoint42PositiveFacts.valid leaf1142CoverageChecked

private noncomputable def leaf1142InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907331/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1142InputLogOnePlusV_eq :
    leaf1142InputLogOnePlusV = outerEnclosure 24
      (leaf1142Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1142RoundedFacts : LeafRoundedFacts 8
    leaf1142Certificate.logOnePlusV leaf1142InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1142InputLogOnePlusV_eq }

private noncomputable def leaf1142Inputs : Inputs :=
  inputsOfCaches globalInput sk112RoundedInputs
    chi110InputQChi innerPair406Input
    leaf1142InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1142LowerChecked :
    lowerCheck 24 leaf1142Box leaf1142Inputs = true := by
  rfl'

private theorem leaf1142CoversExact : CoversExact 8
    leaf1142Box leaf1142Certificate leaf1142InnerLog leaf1142Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk112RoundedFacts chi110RoundedFacts
    innerPair406RoundedFacts leaf1142RoundedFacts (by rfl)

private theorem leaf1142FlatSound : Sound leaf1142Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1142CertificateValid
    leaf1142InnerLogValid leaf1142CoversExact leaf1142LowerChecked

private noncomputable def leaf1143Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (95/32), chiLo := (9/64), chiHi := (19/128) }

private noncomputable def leaf1143Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435683/268435456) }, vSqrt := { lower := (32765/32768), upper := (67108928/67107059) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (379282607/268435456) }, upper := { exponent := 0, mantissa := (5901/4096) } }, logOuter := sk113LogOuterCertificate, logK := sk113LogKCertificate, logChi := chi109LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (134215987/134214118) } }, logDArg := sk113LogDArgCertificate }

private noncomputable def leaf1143InnerLog : WideLogData :=
  innerPair144Data

set_option maxRecDepth 1000000 in
private theorem leaf1143LocalValidity :
    LeafFacts leaf1143Box leaf1143Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1143Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (67108928/67107059) }) = true
      norm_num [leaf1143Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1143CertificateValid :
    WideCertificateValid leaf1143Box leaf1143Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk113ValidityFacts chi109ValidityFacts
    leaf1143LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1143CoverageChecked :
    coverageCheck (innerAD leaf1143Box) leaf1143InnerLog = true := by
  rfl'

private theorem leaf1143InnerLogValid :
    leaf1143InnerLog.Valid 8 (innerAD leaf1143Box) :=
  wideLogDataValid_of_cachedCheck endpoint38PositiveFacts
    endpoint41PositiveFacts.valid leaf1143CoverageChecked

private noncomputable def leaf1143InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814657/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1143InputLogOnePlusV_eq :
    leaf1143InputLogOnePlusV = outerEnclosure 24
      (leaf1143Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1143RoundedFacts : LeafRoundedFacts 8
    leaf1143Certificate.logOnePlusV leaf1143InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1143InputLogOnePlusV_eq }

private noncomputable def leaf1143Inputs : Inputs :=
  inputsOfCaches globalInput sk113RoundedInputs
    chi109InputQChi innerPair144Input
    leaf1143InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1143LowerChecked :
    lowerCheck 24 leaf1143Box leaf1143Inputs = true := by
  rfl'

private theorem leaf1143CoversExact : CoversExact 8
    leaf1143Box leaf1143Certificate leaf1143InnerLog leaf1143Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk113RoundedFacts chi109RoundedFacts
    innerPair144RoundedFacts leaf1143RoundedFacts (by rfl)

private theorem leaf1143FlatSound : Sound leaf1143Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1143CertificateValid
    leaf1143InnerLogValid leaf1143CoversExact leaf1143LowerChecked

private noncomputable def leaf1144Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (9/64), chiHi := (19/128) }

private noncomputable def leaf1144Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435685/268435456) }, vSqrt := { lower := (65529/65536), upper := (2097154/2097095) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (380462181/268435456) }, upper := { exponent := 0, mantissa := (185/128) } }, logOuter := sk114LogOuterCertificate, logK := sk114LogKCertificate, logChi := chi109LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (4194249/4194190) } }, logDArg := sk114LogDArgCertificate }

private noncomputable def leaf1144InnerLog : WideLogData :=
  innerPair144Data

set_option maxRecDepth 1000000 in
private theorem leaf1144LocalValidity :
    LeafFacts leaf1144Box leaf1144Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1144Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (2097154/2097095) }) = true
      norm_num [leaf1144Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1144CertificateValid :
    WideCertificateValid leaf1144Box leaf1144Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk114ValidityFacts chi109ValidityFacts
    leaf1144LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1144CoverageChecked :
    coverageCheck (innerAD leaf1144Box) leaf1144InnerLog = true := by
  rfl'

private theorem leaf1144InnerLogValid :
    leaf1144InnerLog.Valid 8 (innerAD leaf1144Box) :=
  wideLogDataValid_of_cachedCheck endpoint38PositiveFacts
    endpoint41PositiveFacts.valid leaf1144CoverageChecked

private noncomputable def leaf1144InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629317/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1144InputLogOnePlusV_eq :
    leaf1144InputLogOnePlusV = outerEnclosure 24
      (leaf1144Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1144RoundedFacts : LeafRoundedFacts 8
    leaf1144Certificate.logOnePlusV leaf1144InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1144InputLogOnePlusV_eq }

private noncomputable def leaf1144Inputs : Inputs :=
  inputsOfCaches globalInput sk114RoundedInputs
    chi109InputQChi innerPair144Input
    leaf1144InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1144LowerChecked :
    lowerCheck 24 leaf1144Box leaf1144Inputs = true := by
  rfl'

private theorem leaf1144CoversExact : CoversExact 8
    leaf1144Box leaf1144Certificate leaf1144InnerLog leaf1144Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk114RoundedFacts chi109RoundedFacts
    innerPair144RoundedFacts leaf1144RoundedFacts (by rfl)

private theorem leaf1144FlatSound : Sound leaf1144Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1144CertificateValid
    leaf1144InnerLogValid leaf1144CoversExact leaf1144LowerChecked

private noncomputable def leaf1145Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (95/32), chiLo := (19/128), chiHi := (5/32) }

private noncomputable def leaf1145Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435685/268435456) }, vSqrt := { lower := (32765/32768), upper := (16777232/16776741) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (385442613/268435456) }, upper := { exponent := 0, mantissa := (1499/1024) } }, logOuter := sk113LogOuterCertificate, logK := sk113LogKCertificate, logChi := chi110LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (33553973/33553482) } }, logDArg := sk113LogDArgCertificate }

private noncomputable def leaf1145InnerLog : WideLogData :=
  innerPair406Data

set_option maxRecDepth 1000000 in
private theorem leaf1145LocalValidity :
    LeafFacts leaf1145Box leaf1145Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1145Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (16777232/16776741) }) = true
      norm_num [leaf1145Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1145CertificateValid :
    WideCertificateValid leaf1145Box leaf1145Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk113ValidityFacts chi110ValidityFacts
    leaf1145LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1145CoverageChecked :
    coverageCheck (innerAD leaf1145Box) leaf1145InnerLog = true := by
  rfl'

private theorem leaf1145InnerLogValid :
    leaf1145InnerLog.Valid 8 (innerAD leaf1145Box) :=
  wideLogDataValid_of_cachedCheck endpoint119PositiveFacts
    endpoint42PositiveFacts.valid leaf1145CoverageChecked

private noncomputable def leaf1145InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814663/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1145InputLogOnePlusV_eq :
    leaf1145InputLogOnePlusV = outerEnclosure 24
      (leaf1145Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1145RoundedFacts : LeafRoundedFacts 8
    leaf1145Certificate.logOnePlusV leaf1145InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1145InputLogOnePlusV_eq }

private noncomputable def leaf1145Inputs : Inputs :=
  inputsOfCaches globalInput sk113RoundedInputs
    chi110InputQChi innerPair406Input
    leaf1145InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1145LowerChecked :
    lowerCheck 24 leaf1145Box leaf1145Inputs = true := by
  rfl'

private theorem leaf1145CoversExact : CoversExact 8
    leaf1145Box leaf1145Certificate leaf1145InnerLog leaf1145Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk113RoundedFacts chi110RoundedFacts
    innerPair406RoundedFacts leaf1145RoundedFacts (by rfl)

private theorem leaf1145FlatSound : Sound leaf1145Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1145CertificateValid
    leaf1145InnerLogValid leaf1145CoversExact leaf1145LowerChecked

private noncomputable def leaf1146Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (19/128), chiHi := (5/32) }

private noncomputable def leaf1146Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435687/268435456) }, vSqrt := { lower := (65529/65536), upper := (1048577/1048546) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (386687719/268435456) }, upper := { exponent := 0, mantissa := (47/32) } }, logOuter := sk114LogOuterCertificate, logK := sk114LogKCertificate, logChi := chi110LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (2097123/2097092) } }, logDArg := sk114LogDArgCertificate }

private noncomputable def leaf1146InnerLog : WideLogData :=
  innerPair37Data

set_option maxRecDepth 1000000 in
private theorem leaf1146LocalValidity :
    LeafFacts leaf1146Box leaf1146Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1146Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (1048577/1048546) }) = true
      norm_num [leaf1146Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1146CertificateValid :
    WideCertificateValid leaf1146Box leaf1146Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk114ValidityFacts chi110ValidityFacts
    leaf1146LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1146CoverageChecked :
    coverageCheck (innerAD leaf1146Box) leaf1146InnerLog = true := by
  rfl'

private theorem leaf1146InnerLogValid :
    leaf1146InnerLog.Valid 8 (innerAD leaf1146Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint42PositiveFacts.valid leaf1146CoverageChecked

private noncomputable def leaf1146InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629329/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1146InputLogOnePlusV_eq :
    leaf1146InputLogOnePlusV = outerEnclosure 24
      (leaf1146Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1146RoundedFacts : LeafRoundedFacts 8
    leaf1146Certificate.logOnePlusV leaf1146InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1146InputLogOnePlusV_eq }

private noncomputable def leaf1146Inputs : Inputs :=
  inputsOfCaches globalInput sk114RoundedInputs
    chi110InputQChi innerPair37Input
    leaf1146InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1146LowerChecked :
    lowerCheck 24 leaf1146Box leaf1146Inputs = true := by
  rfl'

private theorem leaf1146CoversExact : CoversExact 8
    leaf1146Box leaf1146Certificate leaf1146InnerLog leaf1146Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk114RoundedFacts chi110RoundedFacts
    innerPair37RoundedFacts leaf1146RoundedFacts (by rfl)

private theorem leaf1146FlatSound : Sound leaf1146Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1146CertificateValid
    leaf1146InnerLogValid leaf1146CoversExact leaf1146LowerChecked

private noncomputable def component26Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (1/8), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component26Node0_sound : Sound component26Node0Box :=
  sound_of_literal_split component26Node0Box leaf1115Box leaf1116Box
    .k (89/32) (by rfl) (by rfl)
    leaf1115FlatSound leaf1116FlatSound

private noncomputable def component26Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (17/128), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component26Node1_sound : Sound component26Node1Box :=
  sound_of_literal_split component26Node1Box leaf1117Box leaf1118Box
    .k (89/32) (by rfl) (by rfl)
    leaf1117FlatSound leaf1118FlatSound

private noncomputable def component26Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (1/8), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component26Node2_sound : Sound component26Node2Box :=
  sound_of_literal_split component26Node2Box component26Node0Box component26Node1Box
    .chi (17/128) (by rfl) (by rfl)
    component26Node0_sound component26Node1_sound

private noncomputable def component26Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (1/8), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component26Node3_sound : Sound component26Node3Box :=
  sound_of_literal_split component26Node3Box leaf1119Box leaf1120Box
    .k (91/32) (by rfl) (by rfl)
    leaf1119FlatSound leaf1120FlatSound

private noncomputable def component26Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (17/128), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component26Node4_sound : Sound component26Node4Box :=
  sound_of_literal_split component26Node4Box leaf1121Box leaf1122Box
    .k (91/32) (by rfl) (by rfl)
    leaf1121FlatSound leaf1122FlatSound

private noncomputable def component26Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (1/8), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component26Node5_sound : Sound component26Node5Box :=
  sound_of_literal_split component26Node5Box component26Node3Box component26Node4Box
    .chi (17/128) (by rfl) (by rfl)
    component26Node3_sound component26Node4_sound

private noncomputable def component26Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (1/8), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component26Node6_sound : Sound component26Node6Box :=
  sound_of_literal_split component26Node6Box component26Node2Box component26Node5Box
    .k (45/16) (by rfl) (by rfl)
    component26Node2_sound component26Node5_sound

private noncomputable def component26Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (9/64), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component26Node7_sound : Sound component26Node7Box :=
  sound_of_literal_split component26Node7Box leaf1123Box leaf1124Box
    .k (89/32) (by rfl) (by rfl)
    leaf1123FlatSound leaf1124FlatSound

private noncomputable def component26Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component26Node8_sound : Sound component26Node8Box :=
  sound_of_literal_split component26Node8Box leaf1125Box leaf1126Box
    .k (89/32) (by rfl) (by rfl)
    leaf1125FlatSound leaf1126FlatSound

private noncomputable def component26Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (9/64), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component26Node9_sound : Sound component26Node9Box :=
  sound_of_literal_split component26Node9Box component26Node7Box component26Node8Box
    .chi (19/128) (by rfl) (by rfl)
    component26Node7_sound component26Node8_sound

private noncomputable def component26Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (9/64), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component26Node10_sound : Sound component26Node10Box :=
  sound_of_literal_split component26Node10Box leaf1127Box leaf1128Box
    .k (91/32) (by rfl) (by rfl)
    leaf1127FlatSound leaf1128FlatSound

private noncomputable def component26Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component26Node11_sound : Sound component26Node11Box :=
  sound_of_literal_split component26Node11Box leaf1129Box leaf1130Box
    .k (91/32) (by rfl) (by rfl)
    leaf1129FlatSound leaf1130FlatSound

private noncomputable def component26Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (9/64), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component26Node12_sound : Sound component26Node12Box :=
  sound_of_literal_split component26Node12Box component26Node10Box component26Node11Box
    .chi (19/128) (by rfl) (by rfl)
    component26Node10_sound component26Node11_sound

private noncomputable def component26Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (9/64), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component26Node13_sound : Sound component26Node13Box :=
  sound_of_literal_split component26Node13Box component26Node9Box component26Node12Box
    .k (45/16) (by rfl) (by rfl)
    component26Node9_sound component26Node12_sound

private noncomputable def component26Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (1/8), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component26Node14_sound : Sound component26Node14Box :=
  sound_of_literal_split component26Node14Box component26Node6Box component26Node13Box
    .chi (9/64) (by rfl) (by rfl)
    component26Node6_sound component26Node13_sound

private noncomputable def component26Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (1/8), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component26Node15_sound : Sound component26Node15Box :=
  sound_of_literal_split component26Node15Box leaf1131Box leaf1132Box
    .k (93/32) (by rfl) (by rfl)
    leaf1131FlatSound leaf1132FlatSound

private noncomputable def component26Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (17/128), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component26Node16_sound : Sound component26Node16Box :=
  sound_of_literal_split component26Node16Box leaf1133Box leaf1134Box
    .k (93/32) (by rfl) (by rfl)
    leaf1133FlatSound leaf1134FlatSound

private noncomputable def component26Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (1/8), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component26Node17_sound : Sound component26Node17Box :=
  sound_of_literal_split component26Node17Box component26Node15Box component26Node16Box
    .chi (17/128) (by rfl) (by rfl)
    component26Node15_sound component26Node16_sound

private noncomputable def component26Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (1/8), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component26Node18_sound : Sound component26Node18Box :=
  sound_of_literal_split component26Node18Box leaf1135Box leaf1136Box
    .k (95/32) (by rfl) (by rfl)
    leaf1135FlatSound leaf1136FlatSound

private noncomputable def component26Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (17/128), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component26Node19_sound : Sound component26Node19Box :=
  sound_of_literal_split component26Node19Box leaf1137Box leaf1138Box
    .k (95/32) (by rfl) (by rfl)
    leaf1137FlatSound leaf1138FlatSound

private noncomputable def component26Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (1/8), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component26Node20_sound : Sound component26Node20Box :=
  sound_of_literal_split component26Node20Box component26Node18Box component26Node19Box
    .chi (17/128) (by rfl) (by rfl)
    component26Node18_sound component26Node19_sound

private noncomputable def component26Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (1/8), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component26Node21_sound : Sound component26Node21Box :=
  sound_of_literal_split component26Node21Box component26Node17Box component26Node20Box
    .k (47/16) (by rfl) (by rfl)
    component26Node17_sound component26Node20_sound

private noncomputable def component26Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (9/64), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component26Node22_sound : Sound component26Node22Box :=
  sound_of_literal_split component26Node22Box leaf1139Box leaf1140Box
    .k (93/32) (by rfl) (by rfl)
    leaf1139FlatSound leaf1140FlatSound

private noncomputable def component26Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component26Node23_sound : Sound component26Node23Box :=
  sound_of_literal_split component26Node23Box leaf1141Box leaf1142Box
    .k (93/32) (by rfl) (by rfl)
    leaf1141FlatSound leaf1142FlatSound

private noncomputable def component26Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (9/64), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component26Node24_sound : Sound component26Node24Box :=
  sound_of_literal_split component26Node24Box component26Node22Box component26Node23Box
    .chi (19/128) (by rfl) (by rfl)
    component26Node22_sound component26Node23_sound

private noncomputable def component26Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (9/64), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component26Node25_sound : Sound component26Node25Box :=
  sound_of_literal_split component26Node25Box leaf1143Box leaf1144Box
    .k (95/32) (by rfl) (by rfl)
    leaf1143FlatSound leaf1144FlatSound

private noncomputable def component26Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component26Node26_sound : Sound component26Node26Box :=
  sound_of_literal_split component26Node26Box leaf1145Box leaf1146Box
    .k (95/32) (by rfl) (by rfl)
    leaf1145FlatSound leaf1146FlatSound

private noncomputable def component26Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (9/64), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component26Node27_sound : Sound component26Node27Box :=
  sound_of_literal_split component26Node27Box component26Node25Box component26Node26Box
    .chi (19/128) (by rfl) (by rfl)
    component26Node25_sound component26Node26_sound

private noncomputable def component26Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (9/64), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component26Node28_sound : Sound component26Node28Box :=
  sound_of_literal_split component26Node28Box component26Node24Box component26Node27Box
    .k (47/16) (by rfl) (by rfl)
    component26Node24_sound component26Node27_sound

private noncomputable def component26Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (1/8), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component26Node29_sound : Sound component26Node29Box :=
  sound_of_literal_split component26Node29Box component26Node21Box component26Node28Box
    .chi (9/64) (by rfl) (by rfl)
    component26Node21_sound component26Node28_sound

noncomputable def component26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (3), chiLo := (1/8), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
theorem component26_sound : Sound component26Box :=
  sound_of_literal_split component26Box component26Node14Box component26Node29Box
    .k (23/8) (by rfl) (by rfl)
    component26Node14_sound component26Node29_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
