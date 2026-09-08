import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheSKBatch0

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

private noncomputable def leaf107Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (9/8), chiLo := (0), chiHi := (1/16) }

private noncomputable def leaf107Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (8388627/8388608) }, vSqrt := { lower := (65533/65536), upper := (2097160/2097143) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := -1, mantissa := (8355823/4194304) }, upper := { exponent := 0, mantissa := (137/128) } }, logOuter := sk17LogOuterCertificate, logK := sk17LogKCertificate, logChi := chi12LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (4194303/4194286) } }, logDArg := sk17LogDArgCertificate }

private noncomputable def leaf107InnerLog : WideLogData :=
  innerPair0Data

set_option maxRecDepth 1000000 in
private theorem leaf107LocalValidity :
    LeafFacts leaf107Box leaf107Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf107Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (2097160/2097143) }) = true
      norm_num [leaf107Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf107CertificateValid :
    WideCertificateValid leaf107Box leaf107Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk17ValidityFacts chi12ValidityFacts
    leaf107LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf107CoverageChecked :
    coverageCheck (innerAD leaf107Box) leaf107InnerLog = true := by
  rfl'

private theorem leaf107InnerLogValid :
    leaf107InnerLog.Valid 8 (innerAD leaf107Box) :=
  wideLogDataValid_of_cachedCheck endpoint0PositiveFacts
    endpoint1PositiveFacts.valid leaf107CoverageChecked

private noncomputable def leaf107InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629149/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf107InputLogOnePlusV_eq :
    leaf107InputLogOnePlusV = outerEnclosure 24
      (leaf107Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf107RoundedFacts : LeafRoundedFacts 8
    leaf107Certificate.logOnePlusV leaf107InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf107InputLogOnePlusV_eq }

private noncomputable def leaf107Inputs : Inputs :=
  inputsOfCaches globalInput sk17RoundedInputs
    chi12InputQChi innerPair0Input
    leaf107InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf107LowerChecked :
    lowerCheck 24 leaf107Box leaf107Inputs = true := by
  rfl'

private theorem leaf107CoversExact : CoversExact 8
    leaf107Box leaf107Certificate leaf107InnerLog leaf107Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk17RoundedFacts chi12RoundedFacts
    innerPair0RoundedFacts leaf107RoundedFacts (by rfl)

private theorem leaf107FlatSound : Sound leaf107Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf107CertificateValid
    leaf107InnerLogValid leaf107CoversExact leaf107LowerChecked

private noncomputable def leaf108Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (17/16), chiLo := (1/16), chiHi := (3/32) }

private noncomputable def leaf108Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554471/33554432) }, vSqrt := { lower := (65533/65536), upper := (8388624/8388557) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (35618651/33554432) }, upper := { exponent := 0, mantissa := (563/512) } }, logOuter := sk18LogOuterCertificate, logK := sk18LogKCertificate, logChi := chi13LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (16777181/16777114) } }, logDArg := sk18LogDArgCertificate }

private noncomputable def leaf108InnerLog : WideLogData :=
  innerPair9Data

set_option maxRecDepth 1000000 in
private theorem leaf108LocalValidity :
    LeafFacts leaf108Box leaf108Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf108Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (8388624/8388557) }) = true
      norm_num [leaf108Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf108CertificateValid :
    WideCertificateValid leaf108Box leaf108Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk18ValidityFacts chi13ValidityFacts
    leaf108LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf108CoverageChecked :
    coverageCheck (innerAD leaf108Box) leaf108InnerLog = true := by
  rfl'

private theorem leaf108InnerLogValid :
    leaf108InnerLog.Valid 8 (innerAD leaf108Box) :=
  wideLogDataValid_of_cachedCheck endpoint3PositiveFacts
    endpoint1PositiveFacts.valid leaf108CoverageChecked

private noncomputable def leaf108InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (2907287/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf108InputLogOnePlusV_eq :
    leaf108InputLogOnePlusV = outerEnclosure 24
      (leaf108Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf108RoundedFacts : LeafRoundedFacts 8
    leaf108Certificate.logOnePlusV leaf108InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf108InputLogOnePlusV_eq }

private noncomputable def leaf108Inputs : Inputs :=
  inputsOfCaches globalInput sk18RoundedInputs
    chi13InputQChi innerPair9Input
    leaf108InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf108LowerChecked :
    lowerCheck 24 leaf108Box leaf108Inputs = true := by
  rfl'

private theorem leaf108CoversExact : CoversExact 8
    leaf108Box leaf108Certificate leaf108InnerLog leaf108Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk18RoundedFacts chi13RoundedFacts
    innerPair9RoundedFacts leaf108RoundedFacts (by rfl)

private theorem leaf108FlatSound : Sound leaf108Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf108CertificateValid
    leaf108InnerLogValid leaf108CoversExact leaf108LowerChecked

private noncomputable def leaf109Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/16), kHi := (9/8), chiLo := (1/16), chiHi := (3/32) }

private noncomputable def leaf109Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554473/33554432) }, vSqrt := { lower := (65533/65536), upper := (4194312/4194277) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (35749713/33554432) }, upper := { exponent := 0, mantissa := (283/256) } }, logOuter := sk19LogOuterCertificate, logK := sk19LogKCertificate, logChi := chi13LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (8388589/8388554) } }, logDArg := sk19LogDArgCertificate }

private noncomputable def leaf109InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf109LocalValidity :
    LeafFacts leaf109Box leaf109Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf109Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (4194312/4194277) }) = true
      norm_num [leaf109Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf109CertificateValid :
    WideCertificateValid leaf109Box leaf109Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk19ValidityFacts chi13ValidityFacts
    leaf109LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf109CoverageChecked :
    coverageCheck (innerAD leaf109Box) leaf109InnerLog = true := by
  rfl'

private theorem leaf109InnerLogValid :
    leaf109InnerLog.Valid 8 (innerAD leaf109Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf109CoverageChecked

private noncomputable def leaf109InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629151/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf109InputLogOnePlusV_eq :
    leaf109InputLogOnePlusV = outerEnclosure 24
      (leaf109Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf109RoundedFacts : LeafRoundedFacts 8
    leaf109Certificate.logOnePlusV leaf109InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf109InputLogOnePlusV_eq }

private noncomputable def leaf109Inputs : Inputs :=
  inputsOfCaches globalInput sk19RoundedInputs
    chi13InputQChi innerPair5Input
    leaf109InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf109LowerChecked :
    lowerCheck 24 leaf109Box leaf109Inputs = true := by
  rfl'

private theorem leaf109CoversExact : CoversExact 8
    leaf109Box leaf109Certificate leaf109InnerLog leaf109Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk19RoundedFacts chi13RoundedFacts
    innerPair5RoundedFacts leaf109RoundedFacts (by rfl)

private theorem leaf109FlatSound : Sound leaf109Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf109CertificateValid
    leaf109InnerLogValid leaf109CoversExact leaf109LowerChecked

private noncomputable def leaf110Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (17/16), chiLo := (3/32), chiHi := (1/8) }

private noncomputable def leaf110Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554473/33554432) }, vSqrt := { lower := (65533/65536), upper := (699052/699045) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (36667161/33554432) }, upper := { exponent := 0, mantissa := (145/128) } }, logOuter := sk18LogOuterCertificate, logK := sk18LogKCertificate, logChi := chi14LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (1398097/1398090) } }, logDArg := sk18LogDArgCertificate }

private noncomputable def leaf110InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf110LocalValidity :
    LeafFacts leaf110Box leaf110Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf110Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (699052/699045) }) = true
      norm_num [leaf110Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf110CertificateValid :
    WideCertificateValid leaf110Box leaf110Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk18ValidityFacts chi14ValidityFacts
    leaf110LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf110CoverageChecked :
    coverageCheck (innerAD leaf110Box) leaf110InnerLog = true := by
  rfl'

private theorem leaf110InnerLogValid :
    leaf110InnerLog.Valid 8 (innerAD leaf110Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf110CoverageChecked

private noncomputable def leaf110InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629165/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf110InputLogOnePlusV_eq :
    leaf110InputLogOnePlusV = outerEnclosure 24
      (leaf110Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf110RoundedFacts : LeafRoundedFacts 8
    leaf110Certificate.logOnePlusV leaf110InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf110InputLogOnePlusV_eq }

private noncomputable def leaf110Inputs : Inputs :=
  inputsOfCaches globalInput sk18RoundedInputs
    chi14InputQChi innerPair6Input
    leaf110InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf110LowerChecked :
    lowerCheck 24 leaf110Box leaf110Inputs = true := by
  rfl'

private theorem leaf110CoversExact : CoversExact 8
    leaf110Box leaf110Certificate leaf110InnerLog leaf110Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk18RoundedFacts chi14RoundedFacts
    innerPair6RoundedFacts leaf110RoundedFacts (by rfl)

private theorem leaf110FlatSound : Sound leaf110Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf110CertificateValid
    leaf110InnerLogValid leaf110CoversExact leaf110LowerChecked

private noncomputable def leaf111Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/16), kHi := (9/8), chiLo := (3/32), chiHi := (1/8) }

private noncomputable def leaf111Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554475/33554432) }, vSqrt := { lower := (65533/65536), upper := (1048578/1048567) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (36863755/33554432) }, upper := { exponent := 0, mantissa := (73/64) } }, logOuter := sk19LogOuterCertificate, logK := sk19LogKCertificate, logChi := chi14LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (2097145/2097134) } }, logDArg := sk19LogDArgCertificate }

private noncomputable def leaf111InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf111LocalValidity :
    LeafFacts leaf111Box leaf111Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf111Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (1048578/1048567) }) = true
      norm_num [leaf111Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf111CertificateValid :
    WideCertificateValid leaf111Box leaf111Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk19ValidityFacts chi14ValidityFacts
    leaf111LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf111CoverageChecked :
    coverageCheck (innerAD leaf111Box) leaf111InnerLog = true := by
  rfl'

private theorem leaf111InnerLogValid :
    leaf111InnerLog.Valid 8 (innerAD leaf111Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf111CoverageChecked

private noncomputable def leaf111InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629169/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf111InputLogOnePlusV_eq :
    leaf111InputLogOnePlusV = outerEnclosure 24
      (leaf111Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf111RoundedFacts : LeafRoundedFacts 8
    leaf111Certificate.logOnePlusV leaf111InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf111InputLogOnePlusV_eq }

private noncomputable def leaf111Inputs : Inputs :=
  inputsOfCaches globalInput sk19RoundedInputs
    chi14InputQChi innerPair6Input
    leaf111InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf111LowerChecked :
    lowerCheck 24 leaf111Box leaf111Inputs = true := by
  rfl'

private theorem leaf111CoversExact : CoversExact 8
    leaf111Box leaf111Certificate leaf111InnerLog leaf111Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk19RoundedFacts chi14RoundedFacts
    innerPair6RoundedFacts leaf111RoundedFacts (by rfl)

private theorem leaf111FlatSound : Sound leaf111Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf111CertificateValid
    leaf111InnerLogValid leaf111CoversExact leaf111LowerChecked

private noncomputable def leaf112Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (5/4), chiLo := (0), chiHi := (1/16) }

private noncomputable def leaf112Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (8388629/8388608) }, vSqrt := { lower := (65533/65536), upper := (1048580/1048571) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := -1, mantissa := (8355821/4194304) }, upper := { exponent := 0, mantissa := (69/64) } }, logOuter := sk20LogOuterCertificate, logK := sk20LogKCertificate, logChi := chi12LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (2097151/2097142) } }, logDArg := sk20LogDArgCertificate }

private noncomputable def leaf112InnerLog : WideLogData :=
  innerPair0Data

set_option maxRecDepth 1000000 in
private theorem leaf112LocalValidity :
    LeafFacts leaf112Box leaf112Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf112Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (1048580/1048571) }) = true
      norm_num [leaf112Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf112CertificateValid :
    WideCertificateValid leaf112Box leaf112Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk20ValidityFacts chi12ValidityFacts
    leaf112LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf112CoverageChecked :
    coverageCheck (innerAD leaf112Box) leaf112InnerLog = true := by
  rfl'

private theorem leaf112InnerLogValid :
    leaf112InnerLog.Valid 8 (innerAD leaf112Box) :=
  wideLogDataValid_of_cachedCheck endpoint0PositiveFacts
    endpoint1PositiveFacts.valid leaf112CoverageChecked

private noncomputable def leaf112InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629153/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf112InputLogOnePlusV_eq :
    leaf112InputLogOnePlusV = outerEnclosure 24
      (leaf112Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf112RoundedFacts : LeafRoundedFacts 8
    leaf112Certificate.logOnePlusV leaf112InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf112InputLogOnePlusV_eq }

private noncomputable def leaf112Inputs : Inputs :=
  inputsOfCaches globalInput sk20RoundedInputs
    chi12InputQChi innerPair0Input
    leaf112InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf112LowerChecked :
    lowerCheck 24 leaf112Box leaf112Inputs = true := by
  rfl'

private theorem leaf112CoversExact : CoversExact 8
    leaf112Box leaf112Certificate leaf112InnerLog leaf112Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk20RoundedFacts chi12RoundedFacts
    innerPair0RoundedFacts leaf112RoundedFacts (by rfl)

private theorem leaf112FlatSound : Sound leaf112Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf112CertificateValid
    leaf112InnerLogValid leaf112CoversExact leaf112LowerChecked

private noncomputable def leaf113Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (19/16), chiLo := (1/16), chiHi := (3/32) }

private noncomputable def leaf113Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554475/33554432) }, vSqrt := { lower := (65533/65536), upper := (8388624/8388551) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (35880775/33554432) }, upper := { exponent := 0, mantissa := (569/512) } }, logOuter := sk21LogOuterCertificate, logK := sk21LogKCertificate, logChi := chi13LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (16777175/16777102) } }, logDArg := sk21LogDArgCertificate }

private noncomputable def leaf113InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf113LocalValidity :
    LeafFacts leaf113Box leaf113Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf113Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (8388624/8388551) }) = true
      norm_num [leaf113Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf113CertificateValid :
    WideCertificateValid leaf113Box leaf113Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk21ValidityFacts chi13ValidityFacts
    leaf113LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf113CoverageChecked :
    coverageCheck (innerAD leaf113Box) leaf113InnerLog = true := by
  rfl'

private theorem leaf113InnerLogValid :
    leaf113InnerLog.Valid 8 (innerAD leaf113Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf113CoverageChecked

private noncomputable def leaf113InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (5814577/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf113InputLogOnePlusV_eq :
    leaf113InputLogOnePlusV = outerEnclosure 24
      (leaf113Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf113RoundedFacts : LeafRoundedFacts 8
    leaf113Certificate.logOnePlusV leaf113InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf113InputLogOnePlusV_eq }

private noncomputable def leaf113Inputs : Inputs :=
  inputsOfCaches globalInput sk21RoundedInputs
    chi13InputQChi innerPair5Input
    leaf113InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf113LowerChecked :
    lowerCheck 24 leaf113Box leaf113Inputs = true := by
  rfl'

private theorem leaf113CoversExact : CoversExact 8
    leaf113Box leaf113Certificate leaf113InnerLog leaf113Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk21RoundedFacts chi13RoundedFacts
    innerPair5RoundedFacts leaf113RoundedFacts (by rfl)

private theorem leaf113FlatSound : Sound leaf113Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf113CertificateValid
    leaf113InnerLogValid leaf113CoversExact leaf113LowerChecked

private noncomputable def leaf114Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/16), kHi := (5/4), chiLo := (1/16), chiHi := (3/32) }

private noncomputable def leaf114Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554477/33554432) }, vSqrt := { lower := (65533/65536), upper := (2097156/2097137) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (36011837/33554432) }, upper := { exponent := 0, mantissa := (143/128) } }, logOuter := sk22LogOuterCertificate, logK := sk22LogKCertificate, logChi := chi13LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (4194293/4194274) } }, logDArg := sk22LogDArgCertificate }

private noncomputable def leaf114InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf114LocalValidity :
    LeafFacts leaf114Box leaf114Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf114Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (2097156/2097137) }) = true
      norm_num [leaf114Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf114CertificateValid :
    WideCertificateValid leaf114Box leaf114Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk22ValidityFacts chi13ValidityFacts
    leaf114LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf114CoverageChecked :
    coverageCheck (innerAD leaf114Box) leaf114InnerLog = true := by
  rfl'

private theorem leaf114InnerLogValid :
    leaf114InnerLog.Valid 8 (innerAD leaf114Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf114CoverageChecked

private noncomputable def leaf114InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629157/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf114InputLogOnePlusV_eq :
    leaf114InputLogOnePlusV = outerEnclosure 24
      (leaf114Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf114RoundedFacts : LeafRoundedFacts 8
    leaf114Certificate.logOnePlusV leaf114InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf114InputLogOnePlusV_eq }

private noncomputable def leaf114Inputs : Inputs :=
  inputsOfCaches globalInput sk22RoundedInputs
    chi13InputQChi innerPair5Input
    leaf114InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf114LowerChecked :
    lowerCheck 24 leaf114Box leaf114Inputs = true := by
  rfl'

private theorem leaf114CoversExact : CoversExact 8
    leaf114Box leaf114Certificate leaf114InnerLog leaf114Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk22RoundedFacts chi13RoundedFacts
    innerPair5RoundedFacts leaf114RoundedFacts (by rfl)

private theorem leaf114FlatSound : Sound leaf114Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf114CertificateValid
    leaf114InnerLogValid leaf114CoversExact leaf114LowerChecked

private noncomputable def leaf115Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (19/16), chiLo := (3/32), chiHi := (1/8) }

private noncomputable def leaf115Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554477/33554432) }, vSqrt := { lower := (65533/65536), upper := (2097156/2097133) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (37060349/33554432) }, upper := { exponent := 0, mantissa := (147/128) } }, logOuter := sk21LogOuterCertificate, logK := sk21LogKCertificate, logChi := chi14LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (4194289/4194266) } }, logDArg := sk21LogDArgCertificate }

private noncomputable def leaf115InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf115LocalValidity :
    LeafFacts leaf115Box leaf115Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf115Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (2097156/2097133) }) = true
      norm_num [leaf115Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf115CertificateValid :
    WideCertificateValid leaf115Box leaf115Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk21ValidityFacts chi14ValidityFacts
    leaf115LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf115CoverageChecked :
    coverageCheck (innerAD leaf115Box) leaf115InnerLog = true := by
  rfl'

private theorem leaf115InnerLogValid :
    leaf115InnerLog.Valid 8 (innerAD leaf115Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf115CoverageChecked

private noncomputable def leaf115InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629173/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf115InputLogOnePlusV_eq :
    leaf115InputLogOnePlusV = outerEnclosure 24
      (leaf115Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf115RoundedFacts : LeafRoundedFacts 8
    leaf115Certificate.logOnePlusV leaf115InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf115InputLogOnePlusV_eq }

private noncomputable def leaf115Inputs : Inputs :=
  inputsOfCaches globalInput sk21RoundedInputs
    chi14InputQChi innerPair6Input
    leaf115InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf115LowerChecked :
    lowerCheck 24 leaf115Box leaf115Inputs = true := by
  rfl'

private theorem leaf115CoversExact : CoversExact 8
    leaf115Box leaf115Certificate leaf115InnerLog leaf115Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk21RoundedFacts chi14RoundedFacts
    innerPair6RoundedFacts leaf115RoundedFacts (by rfl)

private theorem leaf115FlatSound : Sound leaf115Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf115CertificateValid
    leaf115InnerLogValid leaf115CoversExact leaf115LowerChecked

private noncomputable def leaf116Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/16), kHi := (5/4), chiLo := (3/32), chiHi := (1/8) }

private noncomputable def leaf116Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554479/33554432) }, vSqrt := { lower := (65533/65536), upper := (174763/174761) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (37256943/33554432) }, upper := { exponent := 0, mantissa := (37/32) } }, logOuter := sk22LogOuterCertificate, logK := sk22LogKCertificate, logChi := chi14LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (174762/174761) } }, logDArg := sk22LogDArgCertificate }

private noncomputable def leaf116InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf116LocalValidity :
    LeafFacts leaf116Box leaf116Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf116Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (174763/174761) }) = true
      norm_num [leaf116Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf116CertificateValid :
    WideCertificateValid leaf116Box leaf116Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk22ValidityFacts chi14ValidityFacts
    leaf116LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf116CoverageChecked :
    coverageCheck (innerAD leaf116Box) leaf116InnerLog = true := by
  rfl'

private theorem leaf116InnerLogValid :
    leaf116InnerLog.Valid 8 (innerAD leaf116Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf116CoverageChecked

private noncomputable def leaf116InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629177/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf116InputLogOnePlusV_eq :
    leaf116InputLogOnePlusV = outerEnclosure 24
      (leaf116Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf116RoundedFacts : LeafRoundedFacts 8
    leaf116Certificate.logOnePlusV leaf116InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf116InputLogOnePlusV_eq }

private noncomputable def leaf116Inputs : Inputs :=
  inputsOfCaches globalInput sk22RoundedInputs
    chi14InputQChi innerPair6Input
    leaf116InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf116LowerChecked :
    lowerCheck 24 leaf116Box leaf116Inputs = true := by
  rfl'

private theorem leaf116CoversExact : CoversExact 8
    leaf116Box leaf116Certificate leaf116InnerLog leaf116Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk22RoundedFacts chi14RoundedFacts
    innerPair6RoundedFacts leaf116RoundedFacts (by rfl)

private theorem leaf116FlatSound : Sound leaf116Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf116CertificateValid
    leaf116InnerLogValid leaf116CoversExact leaf116LowerChecked

private noncomputable def leaf117Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (17/16), chiLo := (1/8), chiHi := (3/16) }

private noncomputable def leaf117Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (16777255/16777216) }, vSqrt := { lower := (65533/65536), upper := (4194312/4194253) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (18841435/16777216) }, upper := { exponent := 0, mantissa := (307/256) } }, logOuter := sk18LogOuterCertificate, logK := sk18LogKCertificate, logChi := chi10LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (8388565/8388506) } }, logDArg := sk18LogDArgCertificate }

private noncomputable def leaf117InnerLog : WideLogData :=
  innerPair124Data

set_option maxRecDepth 1000000 in
private theorem leaf117LocalValidity :
    LeafFacts leaf117Box leaf117Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf117Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (4194312/4194253) }) = true
      norm_num [leaf117Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf117CertificateValid :
    WideCertificateValid leaf117Box leaf117Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk18ValidityFacts chi10ValidityFacts
    leaf117LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf117CoverageChecked :
    coverageCheck (innerAD leaf117Box) leaf117InnerLog = true := by
  rfl'

private theorem leaf117InnerLogValid :
    leaf117InnerLog.Valid 8 (innerAD leaf117Box) :=
  wideLogDataValid_of_cachedCheck endpoint25PositiveFacts
    endpoint26PositiveFacts.valid leaf117CoverageChecked

private noncomputable def leaf117InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629199/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf117InputLogOnePlusV_eq :
    leaf117InputLogOnePlusV = outerEnclosure 24
      (leaf117Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf117RoundedFacts : LeafRoundedFacts 8
    leaf117Certificate.logOnePlusV leaf117InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf117InputLogOnePlusV_eq }

private noncomputable def leaf117Inputs : Inputs :=
  inputsOfCaches globalInput sk18RoundedInputs
    chi10InputQChi innerPair124Input
    leaf117InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf117LowerChecked :
    lowerCheck 24 leaf117Box leaf117Inputs = true := by
  rfl'

private theorem leaf117CoversExact : CoversExact 8
    leaf117Box leaf117Certificate leaf117InnerLog leaf117Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk18RoundedFacts chi10RoundedFacts
    innerPair124RoundedFacts leaf117RoundedFacts (by rfl)

private theorem leaf117FlatSound : Sound leaf117Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf117CertificateValid
    leaf117InnerLogValid leaf117CoversExact leaf117LowerChecked

private noncomputable def leaf118Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/16), kHi := (9/8), chiLo := (1/8), chiHi := (5/32) }

private noncomputable def leaf118Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554477/33554432) }, vSqrt := { lower := (65533/65536), upper := (4194312/4194259) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (37977797/33554432) }, upper := { exponent := 0, mantissa := (301/256) } }, logOuter := sk19LogOuterCertificate, logK := sk19LogKCertificate, logChi := chi25LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (8388571/8388518) } }, logDArg := sk19LogDArgCertificate }

private noncomputable def leaf118InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf118LocalValidity :
    LeafFacts leaf118Box leaf118Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf118Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (4194312/4194259) }) = true
      norm_num [leaf118Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf118CertificateValid :
    WideCertificateValid leaf118Box leaf118Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk19ValidityFacts chi25ValidityFacts
    leaf118LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf118CoverageChecked :
    coverageCheck (innerAD leaf118Box) leaf118InnerLog = true := by
  rfl'

private theorem leaf118InnerLogValid :
    leaf118InnerLog.Valid 8 (innerAD leaf118Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf118CoverageChecked

private noncomputable def leaf118InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629187/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf118InputLogOnePlusV_eq :
    leaf118InputLogOnePlusV = outerEnclosure 24
      (leaf118Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf118RoundedFacts : LeafRoundedFacts 8
    leaf118Certificate.logOnePlusV leaf118InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf118InputLogOnePlusV_eq }

private noncomputable def leaf118Inputs : Inputs :=
  inputsOfCaches globalInput sk19RoundedInputs
    chi25InputQChi innerPair2Input
    leaf118InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf118LowerChecked :
    lowerCheck 24 leaf118Box leaf118Inputs = true := by
  rfl'

private theorem leaf118CoversExact : CoversExact 8
    leaf118Box leaf118Certificate leaf118InnerLog leaf118Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk19RoundedFacts chi25RoundedFacts
    innerPair2RoundedFacts leaf118RoundedFacts (by rfl)

private theorem leaf118FlatSound : Sound leaf118Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf118CertificateValid
    leaf118InnerLogValid leaf118CoversExact leaf118LowerChecked

private noncomputable def leaf119Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/16), kHi := (9/8), chiLo := (5/32), chiHi := (3/16) }

private noncomputable def leaf119Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554479/33554432) }, vSqrt := { lower := (65533/65536), upper := (2097156/2097125) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (39091839/33554432) }, upper := { exponent := 0, mantissa := (155/128) } }, logOuter := sk19LogOuterCertificate, logK := sk19LogKCertificate, logChi := chi26LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (4194281/4194250) } }, logDArg := sk19LogDArgCertificate }

private noncomputable def leaf119InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf119LocalValidity :
    LeafFacts leaf119Box leaf119Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf119Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (2097156/2097125) }) = true
      norm_num [leaf119Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf119CertificateValid :
    WideCertificateValid leaf119Box leaf119Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk19ValidityFacts chi26ValidityFacts
    leaf119LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf119CoverageChecked :
    coverageCheck (innerAD leaf119Box) leaf119InnerLog = true := by
  rfl'

private theorem leaf119InnerLogValid :
    leaf119InnerLog.Valid 8 (innerAD leaf119Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf119CoverageChecked

private noncomputable def leaf119InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629205/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf119InputLogOnePlusV_eq :
    leaf119InputLogOnePlusV = outerEnclosure 24
      (leaf119Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf119RoundedFacts : LeafRoundedFacts 8
    leaf119Certificate.logOnePlusV leaf119InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf119InputLogOnePlusV_eq }

private noncomputable def leaf119Inputs : Inputs :=
  inputsOfCaches globalInput sk19RoundedInputs
    chi26InputQChi innerPair3Input
    leaf119InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf119LowerChecked :
    lowerCheck 24 leaf119Box leaf119Inputs = true := by
  rfl'

private theorem leaf119CoversExact : CoversExact 8
    leaf119Box leaf119Certificate leaf119InnerLog leaf119Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk19RoundedFacts chi26RoundedFacts
    innerPair3RoundedFacts leaf119RoundedFacts (by rfl)

private theorem leaf119FlatSound : Sound leaf119Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf119CertificateValid
    leaf119InnerLogValid leaf119CoversExact leaf119LowerChecked

private noncomputable def leaf120Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (17/16), chiLo := (3/16), chiHi := (7/32) }

private noncomputable def leaf120Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554479/33554432) }, vSqrt := { lower := (65533/65536), upper := (2796208/2796163) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (39812691/33554432) }, upper := { exponent := 0, mantissa := (631/512) } }, logOuter := sk18LogOuterCertificate, logK := sk18LogKCertificate, logChi := chi27LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (5592371/5592326) } }, logDArg := sk18LogDArgCertificate }

private noncomputable def leaf120InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf120LocalValidity :
    LeafFacts leaf120Box leaf120Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf120Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (2796208/2796163) }) = true
      norm_num [leaf120Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf120CertificateValid :
    WideCertificateValid leaf120Box leaf120Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk18ValidityFacts chi27ValidityFacts
    leaf120LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf120CoverageChecked :
    coverageCheck (innerAD leaf120Box) leaf120InnerLog = true := by
  rfl'

private theorem leaf120InnerLogValid :
    leaf120InnerLog.Valid 8 (innerAD leaf120Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf120CoverageChecked

private noncomputable def leaf120InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (363413/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf120InputLogOnePlusV_eq :
    leaf120InputLogOnePlusV = outerEnclosure 24
      (leaf120Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf120RoundedFacts : LeafRoundedFacts 8
    leaf120Certificate.logOnePlusV leaf120InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf120InputLogOnePlusV_eq }

private noncomputable def leaf120Inputs : Inputs :=
  inputsOfCaches globalInput sk18RoundedInputs
    chi27InputQChi innerPair3Input
    leaf120InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf120LowerChecked :
    lowerCheck 24 leaf120Box leaf120Inputs = true := by
  rfl'

private theorem leaf120CoversExact : CoversExact 8
    leaf120Box leaf120Certificate leaf120InnerLog leaf120Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk18RoundedFacts chi27RoundedFacts
    innerPair3RoundedFacts leaf120RoundedFacts (by rfl)

private theorem leaf120FlatSound : Sound leaf120Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf120CertificateValid
    leaf120InnerLogValid leaf120CoversExact leaf120LowerChecked

private noncomputable def leaf121Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (17/16), chiLo := (7/32), chiHi := (1/4) }

private noncomputable def leaf121Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554481/33554432) }, vSqrt := { lower := (65533/65536), upper := (1048578/1048559) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (40861201/33554432) }, upper := { exponent := 0, mantissa := (81/64) } }, logOuter := sk18LogOuterCertificate, logK := sk18LogKCertificate, logChi := chi28LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (2097137/2097118) } }, logDArg := sk18LogDArgCertificate }

private noncomputable def leaf121InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf121LocalValidity :
    LeafFacts leaf121Box leaf121Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf121Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (1048578/1048559) }) = true
      norm_num [leaf121Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf121CertificateValid :
    WideCertificateValid leaf121Box leaf121Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk18ValidityFacts chi28ValidityFacts
    leaf121LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf121CoverageChecked :
    coverageCheck (innerAD leaf121Box) leaf121InnerLog = true := by
  rfl'

private theorem leaf121InnerLogValid :
    leaf121InnerLog.Valid 8 (innerAD leaf121Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf121CoverageChecked

private noncomputable def leaf121InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629233/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf121InputLogOnePlusV_eq :
    leaf121InputLogOnePlusV = outerEnclosure 24
      (leaf121Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf121RoundedFacts : LeafRoundedFacts 8
    leaf121Certificate.logOnePlusV leaf121InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf121InputLogOnePlusV_eq }

private noncomputable def leaf121Inputs : Inputs :=
  inputsOfCaches globalInput sk18RoundedInputs
    chi28InputQChi innerPair13Input
    leaf121InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf121LowerChecked :
    lowerCheck 24 leaf121Box leaf121Inputs = true := by
  rfl'

private theorem leaf121CoversExact : CoversExact 8
    leaf121Box leaf121Certificate leaf121InnerLog leaf121Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk18RoundedFacts chi28RoundedFacts
    innerPair13RoundedFacts leaf121RoundedFacts (by rfl)

private theorem leaf121FlatSound : Sound leaf121Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf121CertificateValid
    leaf121InnerLogValid leaf121CoversExact leaf121LowerChecked

private noncomputable def leaf122Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/16), kHi := (9/8), chiLo := (3/16), chiHi := (7/32) }

private noncomputable def leaf122Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554481/33554432) }, vSqrt := { lower := (65533/65536), upper := (4194312/4194241) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (40205881/33554432) }, upper := { exponent := 0, mantissa := (319/256) } }, logOuter := sk19LogOuterCertificate, logK := sk19LogKCertificate, logChi := chi27LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (8388553/8388482) } }, logDArg := sk19LogDArgCertificate }

private noncomputable def leaf122InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf122LocalValidity :
    LeafFacts leaf122Box leaf122Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf122Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (4194312/4194241) }) = true
      norm_num [leaf122Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf122CertificateValid :
    WideCertificateValid leaf122Box leaf122Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk19ValidityFacts chi27ValidityFacts
    leaf122LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf122CoverageChecked :
    coverageCheck (innerAD leaf122Box) leaf122InnerLog = true := by
  rfl'

private theorem leaf122InnerLogValid :
    leaf122InnerLog.Valid 8 (innerAD leaf122Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf122CoverageChecked

private noncomputable def leaf122InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629223/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf122InputLogOnePlusV_eq :
    leaf122InputLogOnePlusV = outerEnclosure 24
      (leaf122Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf122RoundedFacts : LeafRoundedFacts 8
    leaf122Certificate.logOnePlusV leaf122InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf122InputLogOnePlusV_eq }

private noncomputable def leaf122Inputs : Inputs :=
  inputsOfCaches globalInput sk19RoundedInputs
    chi27InputQChi innerPair12Input
    leaf122InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf122LowerChecked :
    lowerCheck 24 leaf122Box leaf122Inputs = true := by
  rfl'

private theorem leaf122CoversExact : CoversExact 8
    leaf122Box leaf122Certificate leaf122InnerLog leaf122Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk19RoundedFacts chi27RoundedFacts
    innerPair12RoundedFacts leaf122RoundedFacts (by rfl)

private theorem leaf122FlatSound : Sound leaf122Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf122CertificateValid
    leaf122InnerLogValid leaf122CoversExact leaf122LowerChecked

private noncomputable def leaf123Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/16), kHi := (9/8), chiLo := (7/32), chiHi := (1/4) }

private noncomputable def leaf123Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554483/33554432) }, vSqrt := { lower := (65533/65536), upper := (524289/524279) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (41319923/33554432) }, upper := { exponent := 0, mantissa := (41/32) } }, logOuter := sk19LogOuterCertificate, logK := sk19LogKCertificate, logChi := chi28LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (524284/524279) } }, logDArg := sk19LogDArgCertificate }

private noncomputable def leaf123InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf123LocalValidity :
    LeafFacts leaf123Box leaf123Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf123Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (524289/524279) }) = true
      norm_num [leaf123Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf123CertificateValid :
    WideCertificateValid leaf123Box leaf123Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk19ValidityFacts chi28ValidityFacts
    leaf123LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf123CoverageChecked :
    coverageCheck (innerAD leaf123Box) leaf123InnerLog = true := by
  rfl'

private theorem leaf123InnerLogValid :
    leaf123InnerLog.Valid 8 (innerAD leaf123Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf123CoverageChecked

private noncomputable def leaf123InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629241/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf123InputLogOnePlusV_eq :
    leaf123InputLogOnePlusV = outerEnclosure 24
      (leaf123Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf123RoundedFacts : LeafRoundedFacts 8
    leaf123Certificate.logOnePlusV leaf123InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf123InputLogOnePlusV_eq }

private noncomputable def leaf123Inputs : Inputs :=
  inputsOfCaches globalInput sk19RoundedInputs
    chi28InputQChi innerPair13Input
    leaf123InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf123LowerChecked :
    lowerCheck 24 leaf123Box leaf123Inputs = true := by
  rfl'

private theorem leaf123CoversExact : CoversExact 8
    leaf123Box leaf123Certificate leaf123InnerLog leaf123Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk19RoundedFacts chi28RoundedFacts
    innerPair13RoundedFacts leaf123RoundedFacts (by rfl)

private theorem leaf123FlatSound : Sound leaf123Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf123CertificateValid
    leaf123InnerLogValid leaf123CoversExact leaf123LowerChecked

private noncomputable def leaf124Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (19/16), chiLo := (1/8), chiHi := (5/32) }

private noncomputable def leaf124Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554479/33554432) }, vSqrt := { lower := (65533/65536), upper := (2796208/2796171) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (38239923/33554432) }, upper := { exponent := 0, mantissa := (607/512) } }, logOuter := sk21LogOuterCertificate, logK := sk21LogKCertificate, logChi := chi25LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (5592379/5592342) } }, logDArg := sk21LogDArgCertificate }

private noncomputable def leaf124InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf124LocalValidity :
    LeafFacts leaf124Box leaf124Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf124Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (2796208/2796171) }) = true
      norm_num [leaf124Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf124CertificateValid :
    WideCertificateValid leaf124Box leaf124Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk21ValidityFacts chi25ValidityFacts
    leaf124LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf124CoverageChecked :
    coverageCheck (innerAD leaf124Box) leaf124InnerLog = true := by
  rfl'

private theorem leaf124InnerLogValid :
    leaf124InnerLog.Valid 8 (innerAD leaf124Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf124CoverageChecked

private noncomputable def leaf124InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (1453649/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf124InputLogOnePlusV_eq :
    leaf124InputLogOnePlusV = outerEnclosure 24
      (leaf124Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf124RoundedFacts : LeafRoundedFacts 8
    leaf124Certificate.logOnePlusV leaf124InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf124InputLogOnePlusV_eq }

private noncomputable def leaf124Inputs : Inputs :=
  inputsOfCaches globalInput sk21RoundedInputs
    chi25InputQChi innerPair2Input
    leaf124InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf124LowerChecked :
    lowerCheck 24 leaf124Box leaf124Inputs = true := by
  rfl'

private theorem leaf124CoversExact : CoversExact 8
    leaf124Box leaf124Certificate leaf124InnerLog leaf124Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk21RoundedFacts chi25RoundedFacts
    innerPair2RoundedFacts leaf124RoundedFacts (by rfl)

private theorem leaf124FlatSound : Sound leaf124Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf124CertificateValid
    leaf124InnerLogValid leaf124CoversExact leaf124LowerChecked

private noncomputable def leaf125Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/16), kHi := (5/4), chiLo := (1/8), chiHi := (5/32) }

private noncomputable def leaf125Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554481/33554432) }, vSqrt := { lower := (65533/65536), upper := (2097156/2097127) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (38502049/33554432) }, upper := { exponent := 0, mantissa := (153/128) } }, logOuter := sk22LogOuterCertificate, logK := sk22LogKCertificate, logChi := chi25LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (4194283/4194254) } }, logDArg := sk22LogDArgCertificate }

private noncomputable def leaf125InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf125LocalValidity :
    LeafFacts leaf125Box leaf125Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf125Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (2097156/2097127) }) = true
      norm_num [leaf125Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf125CertificateValid :
    WideCertificateValid leaf125Box leaf125Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk22ValidityFacts chi25ValidityFacts
    leaf125LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf125CoverageChecked :
    coverageCheck (innerAD leaf125Box) leaf125InnerLog = true := by
  rfl'

private theorem leaf125InnerLogValid :
    leaf125InnerLog.Valid 8 (innerAD leaf125Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf125CoverageChecked

private noncomputable def leaf125InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629197/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf125InputLogOnePlusV_eq :
    leaf125InputLogOnePlusV = outerEnclosure 24
      (leaf125Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf125RoundedFacts : LeafRoundedFacts 8
    leaf125Certificate.logOnePlusV leaf125InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf125InputLogOnePlusV_eq }

private noncomputable def leaf125Inputs : Inputs :=
  inputsOfCaches globalInput sk22RoundedInputs
    chi25InputQChi innerPair3Input
    leaf125InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf125LowerChecked :
    lowerCheck 24 leaf125Box leaf125Inputs = true := by
  rfl'

private theorem leaf125CoversExact : CoversExact 8
    leaf125Box leaf125Certificate leaf125InnerLog leaf125Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk22RoundedFacts chi25RoundedFacts
    innerPair3RoundedFacts leaf125RoundedFacts (by rfl)

private theorem leaf125FlatSound : Sound leaf125Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf125CertificateValid
    leaf125InnerLogValid leaf125CoversExact leaf125LowerChecked

private noncomputable def leaf126Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (19/16), chiLo := (5/32), chiHi := (3/16) }

private noncomputable def leaf126Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554481/33554432) }, vSqrt := { lower := (65533/65536), upper := (4194312/4194247) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (39419497/33554432) }, upper := { exponent := 0, mantissa := (313/256) } }, logOuter := sk21LogOuterCertificate, logK := sk21LogKCertificate, logChi := chi26LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (8388559/8388494) } }, logDArg := sk21LogDArgCertificate }

private noncomputable def leaf126InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf126LocalValidity :
    LeafFacts leaf126Box leaf126Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf126Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (4194312/4194247) }) = true
      norm_num [leaf126Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf126CertificateValid :
    WideCertificateValid leaf126Box leaf126Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk21ValidityFacts chi26ValidityFacts
    leaf126LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf126CoverageChecked :
    coverageCheck (innerAD leaf126Box) leaf126InnerLog = true := by
  rfl'

private theorem leaf126InnerLogValid :
    leaf126InnerLog.Valid 8 (innerAD leaf126Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf126CoverageChecked

private noncomputable def leaf126InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629211/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf126InputLogOnePlusV_eq :
    leaf126InputLogOnePlusV = outerEnclosure 24
      (leaf126Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf126RoundedFacts : LeafRoundedFacts 8
    leaf126Certificate.logOnePlusV leaf126InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf126InputLogOnePlusV_eq }

private noncomputable def leaf126Inputs : Inputs :=
  inputsOfCaches globalInput sk21RoundedInputs
    chi26InputQChi innerPair3Input
    leaf126InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf126LowerChecked :
    lowerCheck 24 leaf126Box leaf126Inputs = true := by
  rfl'

private theorem leaf126CoversExact : CoversExact 8
    leaf126Box leaf126Certificate leaf126InnerLog leaf126Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk21RoundedFacts chi26RoundedFacts
    innerPair3RoundedFacts leaf126RoundedFacts (by rfl)

private theorem leaf126FlatSound : Sound leaf126Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf126CertificateValid
    leaf126InnerLogValid leaf126CoversExact leaf126LowerChecked

private noncomputable def leaf127Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/16), kHi := (5/4), chiLo := (5/32), chiHi := (3/16) }

private noncomputable def leaf127Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554483/33554432) }, vSqrt := { lower := (65533/65536), upper := (1048578/1048561) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (39747155/33554432) }, upper := { exponent := 0, mantissa := (79/64) } }, logOuter := sk22LogOuterCertificate, logK := sk22LogKCertificate, logChi := chi26LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (2097139/2097122) } }, logDArg := sk22LogDArgCertificate }

private noncomputable def leaf127InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf127LocalValidity :
    LeafFacts leaf127Box leaf127Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf127Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (1048578/1048561) }) = true
      norm_num [leaf127Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf127CertificateValid :
    WideCertificateValid leaf127Box leaf127Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk22ValidityFacts chi26ValidityFacts
    leaf127LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf127CoverageChecked :
    coverageCheck (innerAD leaf127Box) leaf127InnerLog = true := by
  rfl'

private theorem leaf127InnerLogValid :
    leaf127InnerLog.Valid 8 (innerAD leaf127Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf127CoverageChecked

private noncomputable def leaf127InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629217/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf127InputLogOnePlusV_eq :
    leaf127InputLogOnePlusV = outerEnclosure 24
      (leaf127Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf127RoundedFacts : LeafRoundedFacts 8
    leaf127Certificate.logOnePlusV leaf127InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf127InputLogOnePlusV_eq }

private noncomputable def leaf127Inputs : Inputs :=
  inputsOfCaches globalInput sk22RoundedInputs
    chi26InputQChi innerPair3Input
    leaf127InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf127LowerChecked :
    lowerCheck 24 leaf127Box leaf127Inputs = true := by
  rfl'

private theorem leaf127CoversExact : CoversExact 8
    leaf127Box leaf127Certificate leaf127InnerLog leaf127Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk22RoundedFacts chi26RoundedFacts
    innerPair3RoundedFacts leaf127RoundedFacts (by rfl)

private theorem leaf127FlatSound : Sound leaf127Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf127CertificateValid
    leaf127InnerLogValid leaf127CoversExact leaf127LowerChecked

private noncomputable def leaf128Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (19/16), chiLo := (3/16), chiHi := (7/32) }

private noncomputable def leaf128Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554483/33554432) }, vSqrt := { lower := (65533/65536), upper := (8388624/8388475) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (40599071/33554432) }, upper := { exponent := 0, mantissa := (645/512) } }, logOuter := sk21LogOuterCertificate, logK := sk21LogKCertificate, logChi := chi27LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (16777099/16776950) } }, logDArg := sk21LogDArgCertificate }

private noncomputable def leaf128InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf128LocalValidity :
    LeafFacts leaf128Box leaf128Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf128Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (8388624/8388475) }) = true
      norm_num [leaf128Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf128CertificateValid :
    WideCertificateValid leaf128Box leaf128Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk21ValidityFacts chi27ValidityFacts
    leaf128LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf128CoverageChecked :
    coverageCheck (innerAD leaf128Box) leaf128InnerLog = true := by
  rfl'

private theorem leaf128InnerLogValid :
    leaf128InnerLog.Valid 8 (innerAD leaf128Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf128CoverageChecked

private noncomputable def leaf128InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (5814615/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf128InputLogOnePlusV_eq :
    leaf128InputLogOnePlusV = outerEnclosure 24
      (leaf128Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf128RoundedFacts : LeafRoundedFacts 8
    leaf128Certificate.logOnePlusV leaf128InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf128InputLogOnePlusV_eq }

private noncomputable def leaf128Inputs : Inputs :=
  inputsOfCaches globalInput sk21RoundedInputs
    chi27InputQChi innerPair13Input
    leaf128InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf128LowerChecked :
    lowerCheck 24 leaf128Box leaf128Inputs = true := by
  rfl'

private theorem leaf128CoversExact : CoversExact 8
    leaf128Box leaf128Certificate leaf128InnerLog leaf128Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk21RoundedFacts chi27RoundedFacts
    innerPair13RoundedFacts leaf128RoundedFacts (by rfl)

private theorem leaf128FlatSound : Sound leaf128Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf128CertificateValid
    leaf128InnerLogValid leaf128CoversExact leaf128LowerChecked

private noncomputable def leaf129Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (19/16), chiLo := (7/32), chiHi := (1/4) }

private noncomputable def leaf129Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554485/33554432) }, vSqrt := { lower := (65533/65536), upper := (349526/349519) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (41778645/33554432) }, upper := { exponent := 0, mantissa := (83/64) } }, logOuter := sk21LogOuterCertificate, logK := sk21LogKCertificate, logChi := chi28LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (699045/699038) } }, logDArg := sk21LogDArgCertificate }

private noncomputable def leaf129InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf129LocalValidity :
    LeafFacts leaf129Box leaf129Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf129Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (349526/349519) }) = true
      norm_num [leaf129Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf129CertificateValid :
    WideCertificateValid leaf129Box leaf129Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk21ValidityFacts chi28ValidityFacts
    leaf129LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf129CoverageChecked :
    coverageCheck (innerAD leaf129Box) leaf129InnerLog = true := by
  rfl'

private theorem leaf129InnerLogValid :
    leaf129InnerLog.Valid 8 (innerAD leaf129Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf129CoverageChecked

private noncomputable def leaf129InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629249/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf129InputLogOnePlusV_eq :
    leaf129InputLogOnePlusV = outerEnclosure 24
      (leaf129Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf129RoundedFacts : LeafRoundedFacts 8
    leaf129Certificate.logOnePlusV leaf129InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf129InputLogOnePlusV_eq }

private noncomputable def leaf129Inputs : Inputs :=
  inputsOfCaches globalInput sk21RoundedInputs
    chi28InputQChi innerPair13Input
    leaf129InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf129LowerChecked :
    lowerCheck 24 leaf129Box leaf129Inputs = true := by
  rfl'

private theorem leaf129CoversExact : CoversExact 8
    leaf129Box leaf129Certificate leaf129InnerLog leaf129Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk21RoundedFacts chi28RoundedFacts
    innerPair13RoundedFacts leaf129RoundedFacts (by rfl)

private theorem leaf129FlatSound : Sound leaf129Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf129CertificateValid
    leaf129InnerLogValid leaf129CoversExact leaf129LowerChecked

private noncomputable def leaf130Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/16), kHi := (5/4), chiLo := (3/16), chiHi := (7/32) }

private noncomputable def leaf130Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554485/33554432) }, vSqrt := { lower := (65533/65536), upper := (699052/699039) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (40992261/33554432) }, upper := { exponent := 0, mantissa := (163/128) } }, logOuter := sk22LogOuterCertificate, logK := sk22LogKCertificate, logChi := chi27LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (1398091/1398078) } }, logDArg := sk22LogDArgCertificate }

private noncomputable def leaf130InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf130LocalValidity :
    LeafFacts leaf130Box leaf130Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf130Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (699052/699039) }) = true
      norm_num [leaf130Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf130CertificateValid :
    WideCertificateValid leaf130Box leaf130Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk22ValidityFacts chi27ValidityFacts
    leaf130LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf130CoverageChecked :
    coverageCheck (innerAD leaf130Box) leaf130InnerLog = true := by
  rfl'

private theorem leaf130InnerLogValid :
    leaf130InnerLog.Valid 8 (innerAD leaf130Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf130CoverageChecked

private noncomputable def leaf130InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629237/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf130InputLogOnePlusV_eq :
    leaf130InputLogOnePlusV = outerEnclosure 24
      (leaf130Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf130RoundedFacts : LeafRoundedFacts 8
    leaf130Certificate.logOnePlusV leaf130InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf130InputLogOnePlusV_eq }

private noncomputable def leaf130Inputs : Inputs :=
  inputsOfCaches globalInput sk22RoundedInputs
    chi27InputQChi innerPair13Input
    leaf130InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf130LowerChecked :
    lowerCheck 24 leaf130Box leaf130Inputs = true := by
  rfl'

private theorem leaf130CoversExact : CoversExact 8
    leaf130Box leaf130Certificate leaf130InnerLog leaf130Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk22RoundedFacts chi27RoundedFacts
    innerPair13RoundedFacts leaf130RoundedFacts (by rfl)

private theorem leaf130FlatSound : Sound leaf130Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf130CertificateValid
    leaf130InnerLogValid leaf130CoversExact leaf130LowerChecked

private noncomputable def leaf131Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/16), kHi := (5/4), chiLo := (7/32), chiHi := (1/4) }

private noncomputable def leaf131Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554487/33554432) }, vSqrt := { lower := (65533/65536), upper := (524289/524278) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (42237367/33554432) }, upper := { exponent := 0, mantissa := (21/16) } }, logOuter := sk22LogOuterCertificate, logK := sk22LogKCertificate, logChi := chi28LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (1048567/1048556) } }, logDArg := sk22LogDArgCertificate }

private noncomputable def leaf131InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf131LocalValidity :
    LeafFacts leaf131Box leaf131Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf131Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (524289/524278) }) = true
      norm_num [leaf131Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf131CertificateValid :
    WideCertificateValid leaf131Box leaf131Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk22ValidityFacts chi28ValidityFacts
    leaf131LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf131CoverageChecked :
    coverageCheck (innerAD leaf131Box) leaf131InnerLog = true := by
  rfl'

private theorem leaf131InnerLogValid :
    leaf131InnerLog.Valid 8 (innerAD leaf131Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf131CoverageChecked

private noncomputable def leaf131InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629257/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf131InputLogOnePlusV_eq :
    leaf131InputLogOnePlusV = outerEnclosure 24
      (leaf131Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf131RoundedFacts : LeafRoundedFacts 8
    leaf131Certificate.logOnePlusV leaf131InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf131InputLogOnePlusV_eq }

private noncomputable def leaf131Inputs : Inputs :=
  inputsOfCaches globalInput sk22RoundedInputs
    chi28InputQChi innerPair16Input
    leaf131InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf131LowerChecked :
    lowerCheck 24 leaf131Box leaf131Inputs = true := by
  rfl'

private theorem leaf131CoversExact : CoversExact 8
    leaf131Box leaf131Certificate leaf131InnerLog leaf131Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk22RoundedFacts chi28RoundedFacts
    innerPair16RoundedFacts leaf131RoundedFacts (by rfl)

private theorem leaf131FlatSound : Sound leaf131Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf131CertificateValid
    leaf131InnerLogValid leaf131CoversExact leaf131LowerChecked

private noncomputable def leaf132Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (11/8), chiLo := (0), chiHi := (1/16) }

private noncomputable def leaf132Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (8388631/8388608) }, vSqrt := { lower := (65533/65536), upper := (2097160/2097141) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := -1, mantissa := (8355819/4194304) }, upper := { exponent := 0, mantissa := (139/128) } }, logOuter := sk23LogOuterCertificate, logK := sk23LogKCertificate, logChi := chi12LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (4194301/4194282) } }, logDArg := sk23LogDArgCertificate }

private noncomputable def leaf132InnerLog : WideLogData :=
  innerPair0Data

set_option maxRecDepth 1000000 in
private theorem leaf132LocalValidity :
    LeafFacts leaf132Box leaf132Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf132Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (2097160/2097141) }) = true
      norm_num [leaf132Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf132CertificateValid :
    WideCertificateValid leaf132Box leaf132Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk23ValidityFacts chi12ValidityFacts
    leaf132LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf132CoverageChecked :
    coverageCheck (innerAD leaf132Box) leaf132InnerLog = true := by
  rfl'

private theorem leaf132InnerLogValid :
    leaf132InnerLog.Valid 8 (innerAD leaf132Box) :=
  wideLogDataValid_of_cachedCheck endpoint0PositiveFacts
    endpoint1PositiveFacts.valid leaf132CoverageChecked

private noncomputable def leaf132InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629157/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf132InputLogOnePlusV_eq :
    leaf132InputLogOnePlusV = outerEnclosure 24
      (leaf132Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf132RoundedFacts : LeafRoundedFacts 8
    leaf132Certificate.logOnePlusV leaf132InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf132InputLogOnePlusV_eq }

private noncomputable def leaf132Inputs : Inputs :=
  inputsOfCaches globalInput sk23RoundedInputs
    chi12InputQChi innerPair0Input
    leaf132InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf132LowerChecked :
    lowerCheck 24 leaf132Box leaf132Inputs = true := by
  rfl'

private theorem leaf132CoversExact : CoversExact 8
    leaf132Box leaf132Certificate leaf132InnerLog leaf132Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk23RoundedFacts chi12RoundedFacts
    innerPair0RoundedFacts leaf132RoundedFacts (by rfl)

private theorem leaf132FlatSound : Sound leaf132Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf132CertificateValid
    leaf132InnerLogValid leaf132CoversExact leaf132LowerChecked

private noncomputable def leaf133Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (3/2), chiLo := (0), chiHi := (1/32) }

private noncomputable def leaf133Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (16777241/16777216) }, vSqrt := { lower := (16383/16384), upper := (1048580/1048573) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := -1, mantissa := (16744425/8388608) }, upper := { exponent := 0, mantissa := (67/64) } }, logOuter := sk24LogOuterCertificate, logK := sk24LogKCertificate, logChi := chi29LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (2097153/2097146) } }, logDArg := sk24LogDArgCertificate }

private noncomputable def leaf133InnerLog : WideLogData :=
  innerPair1Data

set_option maxRecDepth 1000000 in
private theorem leaf133LocalValidity :
    LeafFacts leaf133Box leaf133Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf133Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (1048580/1048573) }) = true
      norm_num [leaf133Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf133CertificateValid :
    WideCertificateValid leaf133Box leaf133Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk24ValidityFacts chi29ValidityFacts
    leaf133LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf133CoverageChecked :
    coverageCheck (innerAD leaf133Box) leaf133InnerLog = true := by
  rfl'

private theorem leaf133InnerLogValid :
    leaf133InnerLog.Valid 8 (innerAD leaf133Box) :=
  wideLogDataValid_of_cachedCheck endpoint0PositiveFacts
    endpoint2PositiveFacts.valid leaf133CoverageChecked

private noncomputable def leaf133InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629137/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf133InputLogOnePlusV_eq :
    leaf133InputLogOnePlusV = outerEnclosure 24
      (leaf133Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf133RoundedFacts : LeafRoundedFacts 8
    leaf133Certificate.logOnePlusV leaf133InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf133InputLogOnePlusV_eq }

private noncomputable def leaf133Inputs : Inputs :=
  inputsOfCaches globalInput sk24RoundedInputs
    chi29InputQChi innerPair1Input
    leaf133InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf133LowerChecked :
    lowerCheck 24 leaf133Box leaf133Inputs = true := by
  rfl'

private theorem leaf133CoversExact : CoversExact 8
    leaf133Box leaf133Certificate leaf133InnerLog leaf133Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk24RoundedFacts chi29RoundedFacts
    innerPair1RoundedFacts leaf133RoundedFacts (by rfl)

private theorem leaf133FlatSound : Sound leaf133Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf133CertificateValid
    leaf133InnerLogValid leaf133CoversExact leaf133LowerChecked

private noncomputable def leaf134Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (3/2), chiLo := (1/32), chiHi := (3/64) }

private noncomputable def leaf134Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554461/33554432) }, vSqrt := { lower := (16383/16384), upper := (2097160/2097143) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (34963341/33554432) }, upper := { exponent := 0, mantissa := (137/128) } }, logOuter := sk24LogOuterCertificate, logK := sk24LogKCertificate, logChi := chi30LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (4194303/4194286) } }, logDArg := sk24LogDArgCertificate }

private noncomputable def leaf134InnerLog : WideLogData :=
  innerPair9Data

set_option maxRecDepth 1000000 in
private theorem leaf134LocalValidity :
    LeafFacts leaf134Box leaf134Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf134Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (2097160/2097143) }) = true
      norm_num [leaf134Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf134CertificateValid :
    WideCertificateValid leaf134Box leaf134Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk24ValidityFacts chi30ValidityFacts
    leaf134LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf134CoverageChecked :
    coverageCheck (innerAD leaf134Box) leaf134InnerLog = true := by
  rfl'

private theorem leaf134InnerLogValid :
    leaf134InnerLog.Valid 8 (innerAD leaf134Box) :=
  wideLogDataValid_of_cachedCheck endpoint3PositiveFacts
    endpoint1PositiveFacts.valid leaf134CoverageChecked

private noncomputable def leaf134InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629149/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf134InputLogOnePlusV_eq :
    leaf134InputLogOnePlusV = outerEnclosure 24
      (leaf134Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf134RoundedFacts : LeafRoundedFacts 8
    leaf134Certificate.logOnePlusV leaf134InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf134InputLogOnePlusV_eq }

private noncomputable def leaf134Inputs : Inputs :=
  inputsOfCaches globalInput sk24RoundedInputs
    chi30InputQChi innerPair9Input
    leaf134InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf134LowerChecked :
    lowerCheck 24 leaf134Box leaf134Inputs = true := by
  rfl'

private theorem leaf134CoversExact : CoversExact 8
    leaf134Box leaf134Certificate leaf134InnerLog leaf134Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk24RoundedFacts chi30RoundedFacts
    innerPair9RoundedFacts leaf134RoundedFacts (by rfl)

private theorem leaf134FlatSound : Sound leaf134Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf134CertificateValid
    leaf134InnerLogValid leaf134CoversExact leaf134LowerChecked

private noncomputable def leaf135Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (3/2), chiLo := (3/64), chiHi := (1/16) }

private noncomputable def leaf135Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554463/33554432) }, vSqrt := { lower := (16383/16384), upper := (104858/104857) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (35684191/33554432) }, upper := { exponent := 0, mantissa := (35/32) } }, logOuter := sk24LogOuterCertificate, logK := sk24LogKCertificate, logChi := chi31LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (209715/209714) } }, logDArg := sk24LogDArgCertificate }

private noncomputable def leaf135InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf135LocalValidity :
    LeafFacts leaf135Box leaf135Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf135Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (104858/104857) }) = true
      norm_num [leaf135Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf135CertificateValid :
    WideCertificateValid leaf135Box leaf135Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk24ValidityFacts chi31ValidityFacts
    leaf135LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf135CoverageChecked :
    coverageCheck (innerAD leaf135Box) leaf135InnerLog = true := by
  rfl'

private theorem leaf135InnerLogValid :
    leaf135InnerLog.Valid 8 (innerAD leaf135Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf135CoverageChecked

private noncomputable def leaf135InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629161/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf135InputLogOnePlusV_eq :
    leaf135InputLogOnePlusV = outerEnclosure 24
      (leaf135Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf135RoundedFacts : LeafRoundedFacts 8
    leaf135Certificate.logOnePlusV leaf135InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf135InputLogOnePlusV_eq }

private noncomputable def leaf135Inputs : Inputs :=
  inputsOfCaches globalInput sk24RoundedInputs
    chi31InputQChi innerPair5Input
    leaf135InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf135LowerChecked :
    lowerCheck 24 leaf135Box leaf135Inputs = true := by
  rfl'

private theorem leaf135CoversExact : CoversExact 8
    leaf135Box leaf135Certificate leaf135InnerLog leaf135Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk24RoundedFacts chi31RoundedFacts
    innerPair5RoundedFacts leaf135RoundedFacts (by rfl)

private theorem leaf135FlatSound : Sound leaf135Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf135CertificateValid
    leaf135InnerLogValid leaf135CoversExact leaf135LowerChecked

private noncomputable def leaf136Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (21/16), chiLo := (1/16), chiHi := (3/32) }

private noncomputable def leaf136Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554479/33554432) }, vSqrt := { lower := (65533/65536), upper := (8388624/8388545) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (36142899/33554432) }, upper := { exponent := 0, mantissa := (575/512) } }, logOuter := sk25LogOuterCertificate, logK := sk25LogKCertificate, logChi := chi13LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (16777169/16777090) } }, logDArg := sk25LogDArgCertificate }

private noncomputable def leaf136InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf136LocalValidity :
    LeafFacts leaf136Box leaf136Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf136Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (8388624/8388545) }) = true
      norm_num [leaf136Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf136CertificateValid :
    WideCertificateValid leaf136Box leaf136Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk25ValidityFacts chi13ValidityFacts
    leaf136LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf136CoverageChecked :
    coverageCheck (innerAD leaf136Box) leaf136InnerLog = true := by
  rfl'

private theorem leaf136InnerLogValid :
    leaf136InnerLog.Valid 8 (innerAD leaf136Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf136CoverageChecked

private noncomputable def leaf136InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (1453645/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf136InputLogOnePlusV_eq :
    leaf136InputLogOnePlusV = outerEnclosure 24
      (leaf136Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf136RoundedFacts : LeafRoundedFacts 8
    leaf136Certificate.logOnePlusV leaf136InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf136InputLogOnePlusV_eq }

private noncomputable def leaf136Inputs : Inputs :=
  inputsOfCaches globalInput sk25RoundedInputs
    chi13InputQChi innerPair5Input
    leaf136InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf136LowerChecked :
    lowerCheck 24 leaf136Box leaf136Inputs = true := by
  rfl'

private theorem leaf136CoversExact : CoversExact 8
    leaf136Box leaf136Certificate leaf136InnerLog leaf136Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk25RoundedFacts chi13RoundedFacts
    innerPair5RoundedFacts leaf136RoundedFacts (by rfl)

private theorem leaf136FlatSound : Sound leaf136Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf136CertificateValid
    leaf136InnerLogValid leaf136CoversExact leaf136LowerChecked

private noncomputable def leaf137Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/16), kHi := (11/8), chiLo := (1/16), chiHi := (3/32) }

private noncomputable def leaf137Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554481/33554432) }, vSqrt := { lower := (65533/65536), upper := (4194312/4194271) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (36273961/33554432) }, upper := { exponent := 0, mantissa := (289/256) } }, logOuter := sk26LogOuterCertificate, logK := sk26LogKCertificate, logChi := chi13LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (8388583/8388542) } }, logDArg := sk26LogDArgCertificate }

private noncomputable def leaf137InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf137LocalValidity :
    LeafFacts leaf137Box leaf137Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf137Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (4194312/4194271) }) = true
      norm_num [leaf137Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf137CertificateValid :
    WideCertificateValid leaf137Box leaf137Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk26ValidityFacts chi13ValidityFacts
    leaf137LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf137CoverageChecked :
    coverageCheck (innerAD leaf137Box) leaf137InnerLog = true := by
  rfl'

private theorem leaf137InnerLogValid :
    leaf137InnerLog.Valid 8 (innerAD leaf137Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf137CoverageChecked

private noncomputable def leaf137InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629163/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf137InputLogOnePlusV_eq :
    leaf137InputLogOnePlusV = outerEnclosure 24
      (leaf137Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf137RoundedFacts : LeafRoundedFacts 8
    leaf137Certificate.logOnePlusV leaf137InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf137InputLogOnePlusV_eq }

private noncomputable def leaf137Inputs : Inputs :=
  inputsOfCaches globalInput sk26RoundedInputs
    chi13InputQChi innerPair6Input
    leaf137InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf137LowerChecked :
    lowerCheck 24 leaf137Box leaf137Inputs = true := by
  rfl'

private theorem leaf137CoversExact : CoversExact 8
    leaf137Box leaf137Certificate leaf137InnerLog leaf137Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk26RoundedFacts chi13RoundedFacts
    innerPair6RoundedFacts leaf137RoundedFacts (by rfl)

private theorem leaf137FlatSound : Sound leaf137Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf137CertificateValid
    leaf137InnerLogValid leaf137CoversExact leaf137LowerChecked

private noncomputable def leaf138Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (21/16), chiLo := (3/32), chiHi := (1/8) }

private noncomputable def leaf138Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554481/33554432) }, vSqrt := { lower := (65533/65536), upper := (2097156/2097131) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (37453537/33554432) }, upper := { exponent := 0, mantissa := (149/128) } }, logOuter := sk25LogOuterCertificate, logK := sk25LogKCertificate, logChi := chi14LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (4194287/4194262) } }, logDArg := sk25LogDArgCertificate }

private noncomputable def leaf138InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf138LocalValidity :
    LeafFacts leaf138Box leaf138Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf138Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (2097156/2097131) }) = true
      norm_num [leaf138Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf138CertificateValid :
    WideCertificateValid leaf138Box leaf138Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk25ValidityFacts chi14ValidityFacts
    leaf138LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf138CoverageChecked :
    coverageCheck (innerAD leaf138Box) leaf138InnerLog = true := by
  rfl'

private theorem leaf138InnerLogValid :
    leaf138InnerLog.Valid 8 (innerAD leaf138Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf138CoverageChecked

private noncomputable def leaf138InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629181/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf138InputLogOnePlusV_eq :
    leaf138InputLogOnePlusV = outerEnclosure 24
      (leaf138Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf138RoundedFacts : LeafRoundedFacts 8
    leaf138Certificate.logOnePlusV leaf138InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf138InputLogOnePlusV_eq }

private noncomputable def leaf138Inputs : Inputs :=
  inputsOfCaches globalInput sk25RoundedInputs
    chi14InputQChi innerPair6Input
    leaf138InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf138LowerChecked :
    lowerCheck 24 leaf138Box leaf138Inputs = true := by
  rfl'

private theorem leaf138CoversExact : CoversExact 8
    leaf138Box leaf138Certificate leaf138InnerLog leaf138Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk25RoundedFacts chi14RoundedFacts
    innerPair6RoundedFacts leaf138RoundedFacts (by rfl)

private theorem leaf138FlatSound : Sound leaf138Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf138CertificateValid
    leaf138InnerLogValid leaf138CoversExact leaf138LowerChecked

private noncomputable def leaf139Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/16), kHi := (11/8), chiLo := (3/32), chiHi := (1/8) }

private noncomputable def leaf139Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554483/33554432) }, vSqrt := { lower := (65533/65536), upper := (1048578/1048565) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (37650131/33554432) }, upper := { exponent := 0, mantissa := (75/64) } }, logOuter := sk26LogOuterCertificate, logK := sk26LogKCertificate, logChi := chi14LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (2097143/2097130) } }, logDArg := sk26LogDArgCertificate }

private noncomputable def leaf139InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf139LocalValidity :
    LeafFacts leaf139Box leaf139Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf139Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (1048578/1048565) }) = true
      norm_num [leaf139Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf139CertificateValid :
    WideCertificateValid leaf139Box leaf139Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk26ValidityFacts chi14ValidityFacts
    leaf139LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf139CoverageChecked :
    coverageCheck (innerAD leaf139Box) leaf139InnerLog = true := by
  rfl'

private theorem leaf139InnerLogValid :
    leaf139InnerLog.Valid 8 (innerAD leaf139Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf139CoverageChecked

private noncomputable def leaf139InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629185/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf139InputLogOnePlusV_eq :
    leaf139InputLogOnePlusV = outerEnclosure 24
      (leaf139Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf139RoundedFacts : LeafRoundedFacts 8
    leaf139Certificate.logOnePlusV leaf139InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf139InputLogOnePlusV_eq }

private noncomputable def leaf139Inputs : Inputs :=
  inputsOfCaches globalInput sk26RoundedInputs
    chi14InputQChi innerPair6Input
    leaf139InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf139LowerChecked :
    lowerCheck 24 leaf139Box leaf139Inputs = true := by
  rfl'

private theorem leaf139CoversExact : CoversExact 8
    leaf139Box leaf139Certificate leaf139InnerLog leaf139Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk26RoundedFacts chi14RoundedFacts
    innerPair6RoundedFacts leaf139RoundedFacts (by rfl)

private theorem leaf139FlatSound : Sound leaf139Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf139CertificateValid
    leaf139InnerLogValid leaf139CoversExact leaf139LowerChecked

private noncomputable def leaf140Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (3/2), chiLo := (1/16), chiHi := (5/64) }

private noncomputable def leaf140Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554465/33554432) }, vSqrt := { lower := (16383/16384), upper := (2097160/2097137) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (36405041/33554432) }, upper := { exponent := 0, mantissa := (143/128) } }, logOuter := sk24LogOuterCertificate, logK := sk24LogKCertificate, logChi := chi32LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (4194297/4194274) } }, logDArg := sk24LogDArgCertificate }

private noncomputable def leaf140InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf140LocalValidity :
    LeafFacts leaf140Box leaf140Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf140Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (2097160/2097137) }) = true
      norm_num [leaf140Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf140CertificateValid :
    WideCertificateValid leaf140Box leaf140Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk24ValidityFacts chi32ValidityFacts
    leaf140LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf140CoverageChecked :
    coverageCheck (innerAD leaf140Box) leaf140InnerLog = true := by
  rfl'

private theorem leaf140InnerLogValid :
    leaf140InnerLog.Valid 8 (innerAD leaf140Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf140CoverageChecked

private noncomputable def leaf140InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629173/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf140InputLogOnePlusV_eq :
    leaf140InputLogOnePlusV = outerEnclosure 24
      (leaf140Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf140RoundedFacts : LeafRoundedFacts 8
    leaf140Certificate.logOnePlusV leaf140InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf140InputLogOnePlusV_eq }

private noncomputable def leaf140Inputs : Inputs :=
  inputsOfCaches globalInput sk24RoundedInputs
    chi32InputQChi innerPair5Input
    leaf140InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf140LowerChecked :
    lowerCheck 24 leaf140Box leaf140Inputs = true := by
  rfl'

private theorem leaf140CoversExact : CoversExact 8
    leaf140Box leaf140Certificate leaf140InnerLog leaf140Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk24RoundedFacts chi32RoundedFacts
    innerPair5RoundedFacts leaf140RoundedFacts (by rfl)

private theorem leaf140FlatSound : Sound leaf140Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf140CertificateValid
    leaf140InnerLogValid leaf140CoversExact leaf140LowerChecked

private noncomputable def leaf141Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (23/16), chiLo := (5/64), chiHi := (3/32) }

private noncomputable def leaf141Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108921/67108864) }, vSqrt := { lower := (65533/65536), upper := (8388624/8388539) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (74284561/67108864) }, upper := { exponent := 0, mantissa := (581/512) } }, logOuter := sk27LogOuterCertificate, logK := sk27LogKCertificate, logChi := chi33LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (16777163/16777078) } }, logDArg := sk27LogDArgCertificate }

private noncomputable def leaf141InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf141LocalValidity :
    LeafFacts leaf141Box leaf141Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf141Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (8388624/8388539) }) = true
      norm_num [leaf141Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf141CertificateValid :
    WideCertificateValid leaf141Box leaf141Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk27ValidityFacts chi33ValidityFacts
    leaf141LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf141CoverageChecked :
    coverageCheck (innerAD leaf141Box) leaf141InnerLog = true := by
  rfl'

private theorem leaf141InnerLogValid :
    leaf141InnerLog.Valid 8 (innerAD leaf141Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf141CoverageChecked

private noncomputable def leaf141InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (5814583/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf141InputLogOnePlusV_eq :
    leaf141InputLogOnePlusV = outerEnclosure 24
      (leaf141Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf141RoundedFacts : LeafRoundedFacts 8
    leaf141Certificate.logOnePlusV leaf141InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf141InputLogOnePlusV_eq }

private noncomputable def leaf141Inputs : Inputs :=
  inputsOfCaches globalInput sk27RoundedInputs
    chi33InputQChi innerPair6Input
    leaf141InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf141LowerChecked :
    lowerCheck 24 leaf141Box leaf141Inputs = true := by
  rfl'

private theorem leaf141CoversExact : CoversExact 8
    leaf141Box leaf141Certificate leaf141InnerLog leaf141Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk27RoundedFacts chi33RoundedFacts
    innerPair6RoundedFacts leaf141RoundedFacts (by rfl)

private theorem leaf141FlatSound : Sound leaf141Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf141CertificateValid
    leaf141InnerLogValid leaf141CoversExact leaf141LowerChecked

private noncomputable def leaf142Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/16), kHi := (3/2), chiLo := (5/64), chiHi := (3/32) }

private noncomputable def leaf142Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108923/67108864) }, vSqrt := { lower := (16383/16384), upper := (1048578/1048567) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (74612219/67108864) }, upper := { exponent := 0, mantissa := (73/64) } }, logOuter := sk28LogOuterCertificate, logK := sk28LogKCertificate, logChi := chi33LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (2097145/2097134) } }, logDArg := sk28LogDArgCertificate }

private noncomputable def leaf142InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf142LocalValidity :
    LeafFacts leaf142Box leaf142Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf142Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (1048578/1048567) }) = true
      norm_num [leaf142Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf142CertificateValid :
    WideCertificateValid leaf142Box leaf142Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk28ValidityFacts chi33ValidityFacts
    leaf142LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf142CoverageChecked :
    coverageCheck (innerAD leaf142Box) leaf142InnerLog = true := by
  rfl'

private theorem leaf142InnerLogValid :
    leaf142InnerLog.Valid 8 (innerAD leaf142Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf142CoverageChecked

private noncomputable def leaf142InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629169/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf142InputLogOnePlusV_eq :
    leaf142InputLogOnePlusV = outerEnclosure 24
      (leaf142Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf142RoundedFacts : LeafRoundedFacts 8
    leaf142Certificate.logOnePlusV leaf142InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf142InputLogOnePlusV_eq }

private noncomputable def leaf142Inputs : Inputs :=
  inputsOfCaches globalInput sk28RoundedInputs
    chi33InputQChi innerPair6Input
    leaf142InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf142LowerChecked :
    lowerCheck 24 leaf142Box leaf142Inputs = true := by
  rfl'

private theorem leaf142CoversExact : CoversExact 8
    leaf142Box leaf142Certificate leaf142InnerLog leaf142Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk28RoundedFacts chi33RoundedFacts
    innerPair6RoundedFacts leaf142RoundedFacts (by rfl)

private theorem leaf142FlatSound : Sound leaf142Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf142CertificateValid
    leaf142InnerLogValid leaf142CoversExact leaf142LowerChecked

private noncomputable def leaf143Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (23/16), chiLo := (3/32), chiHi := (1/8) }

private noncomputable def leaf143Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554485/33554432) }, vSqrt := { lower := (65533/65536), upper := (699052/699043) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (37846725/33554432) }, upper := { exponent := 0, mantissa := (151/128) } }, logOuter := sk27LogOuterCertificate, logK := sk27LogKCertificate, logChi := chi14LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (1398095/1398086) } }, logDArg := sk27LogDArgCertificate }

private noncomputable def leaf143InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf143LocalValidity :
    LeafFacts leaf143Box leaf143Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf143Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (699052/699043) }) = true
      norm_num [leaf143Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf143CertificateValid :
    WideCertificateValid leaf143Box leaf143Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk27ValidityFacts chi14ValidityFacts
    leaf143LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf143CoverageChecked :
    coverageCheck (innerAD leaf143Box) leaf143InnerLog = true := by
  rfl'

private theorem leaf143InnerLogValid :
    leaf143InnerLog.Valid 8 (innerAD leaf143Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf143CoverageChecked

private noncomputable def leaf143InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629189/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf143InputLogOnePlusV_eq :
    leaf143InputLogOnePlusV = outerEnclosure 24
      (leaf143Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf143RoundedFacts : LeafRoundedFacts 8
    leaf143Certificate.logOnePlusV leaf143InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf143InputLogOnePlusV_eq }

private noncomputable def leaf143Inputs : Inputs :=
  inputsOfCaches globalInput sk27RoundedInputs
    chi14InputQChi innerPair2Input
    leaf143InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf143LowerChecked :
    lowerCheck 24 leaf143Box leaf143Inputs = true := by
  rfl'

private theorem leaf143CoversExact : CoversExact 8
    leaf143Box leaf143Certificate leaf143InnerLog leaf143Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk27RoundedFacts chi14RoundedFacts
    innerPair2RoundedFacts leaf143RoundedFacts (by rfl)

private theorem leaf143FlatSound : Sound leaf143Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf143CertificateValid
    leaf143InnerLogValid leaf143CoversExact leaf143LowerChecked

private noncomputable def leaf144Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/16), kHi := (3/2), chiLo := (3/32), chiHi := (1/8) }

private noncomputable def leaf144Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554487/33554432) }, vSqrt := { lower := (16383/16384), upper := (524289/524282) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (38043319/33554432) }, upper := { exponent := 0, mantissa := (19/16) } }, logOuter := sk28LogOuterCertificate, logK := sk28LogKCertificate, logChi := chi14LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (1048571/1048564) } }, logDArg := sk28LogDArgCertificate }

private noncomputable def leaf144InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf144LocalValidity :
    LeafFacts leaf144Box leaf144Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf144Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (524289/524282) }) = true
      norm_num [leaf144Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf144CertificateValid :
    WideCertificateValid leaf144Box leaf144Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk28ValidityFacts chi14ValidityFacts
    leaf144LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf144CoverageChecked :
    coverageCheck (innerAD leaf144Box) leaf144InnerLog = true := by
  rfl'

private theorem leaf144InnerLogValid :
    leaf144InnerLog.Valid 8 (innerAD leaf144Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf144CoverageChecked

private noncomputable def leaf144InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629193/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf144InputLogOnePlusV_eq :
    leaf144InputLogOnePlusV = outerEnclosure 24
      (leaf144Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf144RoundedFacts : LeafRoundedFacts 8
    leaf144Certificate.logOnePlusV leaf144InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf144InputLogOnePlusV_eq }

private noncomputable def leaf144Inputs : Inputs :=
  inputsOfCaches globalInput sk28RoundedInputs
    chi14InputQChi innerPair2Input
    leaf144InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf144LowerChecked :
    lowerCheck 24 leaf144Box leaf144Inputs = true := by
  rfl'

private theorem leaf144CoversExact : CoversExact 8
    leaf144Box leaf144Certificate leaf144InnerLog leaf144Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk28RoundedFacts chi14RoundedFacts
    innerPair2RoundedFacts leaf144RoundedFacts (by rfl)

private theorem leaf144FlatSound : Sound leaf144Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf144CertificateValid
    leaf144InnerLogValid leaf144CoversExact leaf144LowerChecked

private noncomputable def leaf145Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (21/16), chiLo := (1/8), chiHi := (5/32) }

private noncomputable def leaf145Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554483/33554432) }, vSqrt := { lower := (65533/65536), upper := (8388624/8388503) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (38764175/33554432) }, upper := { exponent := 0, mantissa := (617/512) } }, logOuter := sk25LogOuterCertificate, logK := sk25LogKCertificate, logChi := chi25LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (16777127/16777006) } }, logDArg := sk25LogDArgCertificate }

private noncomputable def leaf145InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf145LocalValidity :
    LeafFacts leaf145Box leaf145Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf145Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (8388624/8388503) }) = true
      norm_num [leaf145Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf145CertificateValid :
    WideCertificateValid leaf145Box leaf145Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk25ValidityFacts chi25ValidityFacts
    leaf145LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf145CoverageChecked :
    coverageCheck (innerAD leaf145Box) leaf145InnerLog = true := by
  rfl'

private theorem leaf145InnerLogValid :
    leaf145InnerLog.Valid 8 (innerAD leaf145Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf145CoverageChecked

private noncomputable def leaf145InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (5814601/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf145InputLogOnePlusV_eq :
    leaf145InputLogOnePlusV = outerEnclosure 24
      (leaf145Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf145RoundedFacts : LeafRoundedFacts 8
    leaf145Certificate.logOnePlusV leaf145InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf145InputLogOnePlusV_eq }

private noncomputable def leaf145Inputs : Inputs :=
  inputsOfCaches globalInput sk25RoundedInputs
    chi25InputQChi innerPair3Input
    leaf145InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf145LowerChecked :
    lowerCheck 24 leaf145Box leaf145Inputs = true := by
  rfl'

private theorem leaf145CoversExact : CoversExact 8
    leaf145Box leaf145Certificate leaf145InnerLog leaf145Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk25RoundedFacts chi25RoundedFacts
    innerPair3RoundedFacts leaf145RoundedFacts (by rfl)

private theorem leaf145FlatSound : Sound leaf145Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf145CertificateValid
    leaf145InnerLogValid leaf145CoversExact leaf145LowerChecked

private noncomputable def leaf146Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/16), kHi := (11/8), chiLo := (1/8), chiHi := (5/32) }

private noncomputable def leaf146Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554485/33554432) }, vSqrt := { lower := (65533/65536), upper := (1398104/1398083) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (39026301/33554432) }, upper := { exponent := 0, mantissa := (311/256) } }, logOuter := sk26LogOuterCertificate, logK := sk26LogKCertificate, logChi := chi25LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (2796187/2796166) } }, logDArg := sk26LogDArgCertificate }

private noncomputable def leaf146InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf146LocalValidity :
    LeafFacts leaf146Box leaf146Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf146Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (1398104/1398083) }) = true
      norm_num [leaf146Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf146CertificateValid :
    WideCertificateValid leaf146Box leaf146Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk26ValidityFacts chi25ValidityFacts
    leaf146LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf146CoverageChecked :
    coverageCheck (innerAD leaf146Box) leaf146InnerLog = true := by
  rfl'

private theorem leaf146InnerLogValid :
    leaf146InnerLog.Valid 8 (innerAD leaf146Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf146CoverageChecked

private noncomputable def leaf146InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629207/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf146InputLogOnePlusV_eq :
    leaf146InputLogOnePlusV = outerEnclosure 24
      (leaf146Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf146RoundedFacts : LeafRoundedFacts 8
    leaf146Certificate.logOnePlusV leaf146InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf146InputLogOnePlusV_eq }

private noncomputable def leaf146Inputs : Inputs :=
  inputsOfCaches globalInput sk26RoundedInputs
    chi25InputQChi innerPair3Input
    leaf146InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf146LowerChecked :
    lowerCheck 24 leaf146Box leaf146Inputs = true := by
  rfl'

private theorem leaf146CoversExact : CoversExact 8
    leaf146Box leaf146Certificate leaf146InnerLog leaf146Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk26RoundedFacts chi25RoundedFacts
    innerPair3RoundedFacts leaf146RoundedFacts (by rfl)

private theorem leaf146FlatSound : Sound leaf146Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf146CertificateValid
    leaf146InnerLogValid leaf146CoversExact leaf146LowerChecked

private noncomputable def leaf147Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (21/16), chiLo := (5/32), chiHi := (3/16) }

private noncomputable def leaf147Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554485/33554432) }, vSqrt := { lower := (65533/65536), upper := (4194312/4194241) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (40074813/33554432) }, upper := { exponent := 0, mantissa := (319/256) } }, logOuter := sk25LogOuterCertificate, logK := sk25LogKCertificate, logChi := chi26LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (8388553/8388482) } }, logDArg := sk25LogDArgCertificate }

private noncomputable def leaf147InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf147LocalValidity :
    LeafFacts leaf147Box leaf147Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf147Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (4194312/4194241) }) = true
      norm_num [leaf147Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf147CertificateValid :
    WideCertificateValid leaf147Box leaf147Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk25ValidityFacts chi26ValidityFacts
    leaf147LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf147CoverageChecked :
    coverageCheck (innerAD leaf147Box) leaf147InnerLog = true := by
  rfl'

private theorem leaf147InnerLogValid :
    leaf147InnerLog.Valid 8 (innerAD leaf147Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf147CoverageChecked

private noncomputable def leaf147InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629223/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf147InputLogOnePlusV_eq :
    leaf147InputLogOnePlusV = outerEnclosure 24
      (leaf147Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf147RoundedFacts : LeafRoundedFacts 8
    leaf147Certificate.logOnePlusV leaf147InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf147InputLogOnePlusV_eq }

private noncomputable def leaf147Inputs : Inputs :=
  inputsOfCaches globalInput sk25RoundedInputs
    chi26InputQChi innerPair12Input
    leaf147InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf147LowerChecked :
    lowerCheck 24 leaf147Box leaf147Inputs = true := by
  rfl'

private theorem leaf147CoversExact : CoversExact 8
    leaf147Box leaf147Certificate leaf147InnerLog leaf147Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk25RoundedFacts chi26RoundedFacts
    innerPair12RoundedFacts leaf147RoundedFacts (by rfl)

private theorem leaf147FlatSound : Sound leaf147Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf147CertificateValid
    leaf147InnerLogValid leaf147CoversExact leaf147LowerChecked

private noncomputable def leaf148Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/16), kHi := (11/8), chiLo := (5/32), chiHi := (3/16) }

private noncomputable def leaf148Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554487/33554432) }, vSqrt := { lower := (65533/65536), upper := (2097156/2097119) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (40402471/33554432) }, upper := { exponent := 0, mantissa := (161/128) } }, logOuter := sk26LogOuterCertificate, logK := sk26LogKCertificate, logChi := chi26LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (4194275/4194238) } }, logDArg := sk26LogDArgCertificate }

private noncomputable def leaf148InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf148LocalValidity :
    LeafFacts leaf148Box leaf148Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf148Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (2097156/2097119) }) = true
      norm_num [leaf148Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf148CertificateValid :
    WideCertificateValid leaf148Box leaf148Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk26ValidityFacts chi26ValidityFacts
    leaf148LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf148CoverageChecked :
    coverageCheck (innerAD leaf148Box) leaf148InnerLog = true := by
  rfl'

private theorem leaf148InnerLogValid :
    leaf148InnerLog.Valid 8 (innerAD leaf148Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf148CoverageChecked

private noncomputable def leaf148InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629229/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf148InputLogOnePlusV_eq :
    leaf148InputLogOnePlusV = outerEnclosure 24
      (leaf148Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf148RoundedFacts : LeafRoundedFacts 8
    leaf148Certificate.logOnePlusV leaf148InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf148InputLogOnePlusV_eq }

private noncomputable def leaf148Inputs : Inputs :=
  inputsOfCaches globalInput sk26RoundedInputs
    chi26InputQChi innerPair13Input
    leaf148InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf148LowerChecked :
    lowerCheck 24 leaf148Box leaf148Inputs = true := by
  rfl'

private theorem leaf148CoversExact : CoversExact 8
    leaf148Box leaf148Certificate leaf148InnerLog leaf148Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk26RoundedFacts chi26RoundedFacts
    innerPair13RoundedFacts leaf148RoundedFacts (by rfl)

private theorem leaf148FlatSound : Sound leaf148Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf148CertificateValid
    leaf148InnerLogValid leaf148CoversExact leaf148LowerChecked

private noncomputable def leaf149Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (23/16), chiLo := (1/8), chiHi := (5/32) }

private noncomputable def leaf149Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554487/33554432) }, vSqrt := { lower := (65533/65536), upper := (8388624/8388493) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (39288427/33554432) }, upper := { exponent := 0, mantissa := (627/512) } }, logOuter := sk27LogOuterCertificate, logK := sk27LogKCertificate, logChi := chi25LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (16777117/16776986) } }, logDArg := sk27LogDArgCertificate }

private noncomputable def leaf149InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf149LocalValidity :
    LeafFacts leaf149Box leaf149Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf149Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (8388624/8388493) }) = true
      norm_num [leaf149Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf149CertificateValid :
    WideCertificateValid leaf149Box leaf149Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk27ValidityFacts chi25ValidityFacts
    leaf149LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf149CoverageChecked :
    coverageCheck (innerAD leaf149Box) leaf149InnerLog = true := by
  rfl'

private theorem leaf149InnerLogValid :
    leaf149InnerLog.Valid 8 (innerAD leaf149Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf149CoverageChecked

private noncomputable def leaf149InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (2907303/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf149InputLogOnePlusV_eq :
    leaf149InputLogOnePlusV = outerEnclosure 24
      (leaf149Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf149RoundedFacts : LeafRoundedFacts 8
    leaf149Certificate.logOnePlusV leaf149InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf149InputLogOnePlusV_eq }

private noncomputable def leaf149Inputs : Inputs :=
  inputsOfCaches globalInput sk27RoundedInputs
    chi25InputQChi innerPair3Input
    leaf149InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf149LowerChecked :
    lowerCheck 24 leaf149Box leaf149Inputs = true := by
  rfl'

private theorem leaf149CoversExact : CoversExact 8
    leaf149Box leaf149Certificate leaf149InnerLog leaf149Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk27RoundedFacts chi25RoundedFacts
    innerPair3RoundedFacts leaf149RoundedFacts (by rfl)

private theorem leaf149FlatSound : Sound leaf149Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf149CertificateValid
    leaf149InnerLogValid leaf149CoversExact leaf149LowerChecked

private noncomputable def leaf150Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/16), kHi := (3/2), chiLo := (1/8), chiHi := (5/32) }

private noncomputable def leaf150Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554489/33554432) }, vSqrt := { lower := (16383/16384), upper := (1048578/1048561) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (39550553/33554432) }, upper := { exponent := 0, mantissa := (79/64) } }, logOuter := sk28LogOuterCertificate, logK := sk28LogKCertificate, logChi := chi25LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (2097139/2097122) } }, logDArg := sk28LogDArgCertificate }

private noncomputable def leaf150InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf150LocalValidity :
    LeafFacts leaf150Box leaf150Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf150Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (1048578/1048561) }) = true
      norm_num [leaf150Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf150CertificateValid :
    WideCertificateValid leaf150Box leaf150Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk28ValidityFacts chi25ValidityFacts
    leaf150LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf150CoverageChecked :
    coverageCheck (innerAD leaf150Box) leaf150InnerLog = true := by
  rfl'

private theorem leaf150InnerLogValid :
    leaf150InnerLog.Valid 8 (innerAD leaf150Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf150CoverageChecked

private noncomputable def leaf150InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629217/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf150InputLogOnePlusV_eq :
    leaf150InputLogOnePlusV = outerEnclosure 24
      (leaf150Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf150RoundedFacts : LeafRoundedFacts 8
    leaf150Certificate.logOnePlusV leaf150InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf150InputLogOnePlusV_eq }

private noncomputable def leaf150Inputs : Inputs :=
  inputsOfCaches globalInput sk28RoundedInputs
    chi25InputQChi innerPair3Input
    leaf150InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf150LowerChecked :
    lowerCheck 24 leaf150Box leaf150Inputs = true := by
  rfl'

private theorem leaf150CoversExact : CoversExact 8
    leaf150Box leaf150Certificate leaf150InnerLog leaf150Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk28RoundedFacts chi25RoundedFacts
    innerPair3RoundedFacts leaf150RoundedFacts (by rfl)

private theorem leaf150FlatSound : Sound leaf150Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf150CertificateValid
    leaf150InnerLogValid leaf150CoversExact leaf150LowerChecked

private noncomputable def leaf151Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (23/16), chiLo := (5/32), chiHi := (3/16) }

private noncomputable def leaf151Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554489/33554432) }, vSqrt := { lower := (65533/65536), upper := (4194312/4194235) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (40730129/33554432) }, upper := { exponent := 0, mantissa := (325/256) } }, logOuter := sk27LogOuterCertificate, logK := sk27LogKCertificate, logChi := chi26LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (8388547/8388470) } }, logDArg := sk27LogDArgCertificate }

private noncomputable def leaf151InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf151LocalValidity :
    LeafFacts leaf151Box leaf151Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf151Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (4194312/4194235) }) = true
      norm_num [leaf151Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf151CertificateValid :
    WideCertificateValid leaf151Box leaf151Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk27ValidityFacts chi26ValidityFacts
    leaf151LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf151CoverageChecked :
    coverageCheck (innerAD leaf151Box) leaf151InnerLog = true := by
  rfl'

private theorem leaf151InnerLogValid :
    leaf151InnerLog.Valid 8 (innerAD leaf151Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf151CoverageChecked

private noncomputable def leaf151InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629235/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf151InputLogOnePlusV_eq :
    leaf151InputLogOnePlusV = outerEnclosure 24
      (leaf151Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf151RoundedFacts : LeafRoundedFacts 8
    leaf151Certificate.logOnePlusV leaf151InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf151InputLogOnePlusV_eq }

private noncomputable def leaf151Inputs : Inputs :=
  inputsOfCaches globalInput sk27RoundedInputs
    chi26InputQChi innerPair13Input
    leaf151InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf151LowerChecked :
    lowerCheck 24 leaf151Box leaf151Inputs = true := by
  rfl'

private theorem leaf151CoversExact : CoversExact 8
    leaf151Box leaf151Certificate leaf151InnerLog leaf151Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk27RoundedFacts chi26RoundedFacts
    innerPair13RoundedFacts leaf151RoundedFacts (by rfl)

private theorem leaf151FlatSound : Sound leaf151Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf151CertificateValid
    leaf151InnerLogValid leaf151CoversExact leaf151LowerChecked

private noncomputable def leaf152Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/16), kHi := (3/2), chiLo := (5/32), chiHi := (3/16) }

private noncomputable def leaf152Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554491/33554432) }, vSqrt := { lower := (16383/16384), upper := (524289/524279) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (41057787/33554432) }, upper := { exponent := 0, mantissa := (41/32) } }, logOuter := sk28LogOuterCertificate, logK := sk28LogKCertificate, logChi := chi26LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (524284/524279) } }, logDArg := sk28LogDArgCertificate }

private noncomputable def leaf152InnerLog : WideLogData :=
  innerPair127Data

set_option maxRecDepth 1000000 in
private theorem leaf152LocalValidity :
    LeafFacts leaf152Box leaf152Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf152Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (524289/524279) }) = true
      norm_num [leaf152Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf152CertificateValid :
    WideCertificateValid leaf152Box leaf152Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk28ValidityFacts chi26ValidityFacts
    leaf152LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf152CoverageChecked :
    coverageCheck (innerAD leaf152Box) leaf152InnerLog = true := by
  rfl'

private theorem leaf152InnerLogValid :
    leaf152InnerLog.Valid 8 (innerAD leaf152Box) :=
  wideLogDataValid_of_cachedCheck endpoint27PositiveFacts
    endpoint28PositiveFacts.valid leaf152CoverageChecked

private noncomputable def leaf152InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629241/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf152InputLogOnePlusV_eq :
    leaf152InputLogOnePlusV = outerEnclosure 24
      (leaf152Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf152RoundedFacts : LeafRoundedFacts 8
    leaf152Certificate.logOnePlusV leaf152InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf152InputLogOnePlusV_eq }

private noncomputable def leaf152Inputs : Inputs :=
  inputsOfCaches globalInput sk28RoundedInputs
    chi26InputQChi innerPair127Input
    leaf152InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf152LowerChecked :
    lowerCheck 24 leaf152Box leaf152Inputs = true := by
  rfl'

private theorem leaf152CoversExact : CoversExact 8
    leaf152Box leaf152Certificate leaf152InnerLog leaf152Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk28RoundedFacts chi26RoundedFacts
    innerPair127RoundedFacts leaf152RoundedFacts (by rfl)

private theorem leaf152FlatSound : Sound leaf152Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf152CertificateValid
    leaf152InnerLogValid leaf152CoversExact leaf152LowerChecked

private noncomputable def leaf153Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (21/16), chiLo := (3/16), chiHi := (7/32) }

private noncomputable def leaf153Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554487/33554432) }, vSqrt := { lower := (65533/65536), upper := (8388624/8388461) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (41385451/33554432) }, upper := { exponent := 0, mantissa := (659/512) } }, logOuter := sk25LogOuterCertificate, logK := sk25LogKCertificate, logChi := chi27LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (16777085/16776922) } }, logDArg := sk25LogDArgCertificate }

private noncomputable def leaf153InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf153LocalValidity :
    LeafFacts leaf153Box leaf153Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf153Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (8388624/8388461) }) = true
      norm_num [leaf153Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf153CertificateValid :
    WideCertificateValid leaf153Box leaf153Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk25ValidityFacts chi27ValidityFacts
    leaf153LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf153CoverageChecked :
    coverageCheck (innerAD leaf153Box) leaf153InnerLog = true := by
  rfl'

private theorem leaf153InnerLogValid :
    leaf153InnerLog.Valid 8 (innerAD leaf153Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf153CoverageChecked

private noncomputable def leaf153InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (2907311/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf153InputLogOnePlusV_eq :
    leaf153InputLogOnePlusV = outerEnclosure 24
      (leaf153Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf153RoundedFacts : LeafRoundedFacts 8
    leaf153Certificate.logOnePlusV leaf153InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf153InputLogOnePlusV_eq }

private noncomputable def leaf153Inputs : Inputs :=
  inputsOfCaches globalInput sk25RoundedInputs
    chi27InputQChi innerPair13Input
    leaf153InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf153LowerChecked :
    lowerCheck 24 leaf153Box leaf153Inputs = true := by
  rfl'

private theorem leaf153CoversExact : CoversExact 8
    leaf153Box leaf153Certificate leaf153InnerLog leaf153Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk25RoundedFacts chi27RoundedFacts
    innerPair13RoundedFacts leaf153RoundedFacts (by rfl)

private theorem leaf153FlatSound : Sound leaf153Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf153CertificateValid
    leaf153InnerLogValid leaf153CoversExact leaf153LowerChecked

private noncomputable def leaf154Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (21/16), chiLo := (7/32), chiHi := (1/4) }

private noncomputable def leaf154Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554489/33554432) }, vSqrt := { lower := (65533/65536), upper := (1048578/1048555) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (42696089/33554432) }, upper := { exponent := 0, mantissa := (85/64) } }, logOuter := sk25LogOuterCertificate, logK := sk25LogKCertificate, logChi := chi28LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (2097133/2097110) } }, logDArg := sk25LogDArgCertificate }

private noncomputable def leaf154InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf154LocalValidity :
    LeafFacts leaf154Box leaf154Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf154Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (1048578/1048555) }) = true
      norm_num [leaf154Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf154CertificateValid :
    WideCertificateValid leaf154Box leaf154Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk25ValidityFacts chi28ValidityFacts
    leaf154LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf154CoverageChecked :
    coverageCheck (innerAD leaf154Box) leaf154InnerLog = true := by
  rfl'

private theorem leaf154InnerLogValid :
    leaf154InnerLog.Valid 8 (innerAD leaf154Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf154CoverageChecked

private noncomputable def leaf154InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629265/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf154InputLogOnePlusV_eq :
    leaf154InputLogOnePlusV = outerEnclosure 24
      (leaf154Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf154RoundedFacts : LeafRoundedFacts 8
    leaf154Certificate.logOnePlusV leaf154InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf154InputLogOnePlusV_eq }

private noncomputable def leaf154Inputs : Inputs :=
  inputsOfCaches globalInput sk25RoundedInputs
    chi28InputQChi innerPair17Input
    leaf154InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf154LowerChecked :
    lowerCheck 24 leaf154Box leaf154Inputs = true := by
  rfl'

private theorem leaf154CoversExact : CoversExact 8
    leaf154Box leaf154Certificate leaf154InnerLog leaf154Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk25RoundedFacts chi28RoundedFacts
    innerPair17RoundedFacts leaf154RoundedFacts (by rfl)

private theorem leaf154FlatSound : Sound leaf154Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf154CertificateValid
    leaf154InnerLogValid leaf154CoversExact leaf154LowerChecked

private noncomputable def leaf155Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/16), kHi := (11/8), chiLo := (3/16), chiHi := (7/32) }

private noncomputable def leaf155Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554489/33554432) }, vSqrt := { lower := (65533/65536), upper := (4194312/4194227) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (41778641/33554432) }, upper := { exponent := 0, mantissa := (333/256) } }, logOuter := sk26LogOuterCertificate, logK := sk26LogKCertificate, logChi := chi27LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (8388539/8388454) } }, logDArg := sk26LogDArgCertificate }

private noncomputable def leaf155InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf155LocalValidity :
    LeafFacts leaf155Box leaf155Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf155Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (4194312/4194227) }) = true
      norm_num [leaf155Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf155CertificateValid :
    WideCertificateValid leaf155Box leaf155Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk26ValidityFacts chi27ValidityFacts
    leaf155LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf155CoverageChecked :
    coverageCheck (innerAD leaf155Box) leaf155InnerLog = true := by
  rfl'

private theorem leaf155InnerLogValid :
    leaf155InnerLog.Valid 8 (innerAD leaf155Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf155CoverageChecked

private noncomputable def leaf155InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629251/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf155InputLogOnePlusV_eq :
    leaf155InputLogOnePlusV = outerEnclosure 24
      (leaf155Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf155RoundedFacts : LeafRoundedFacts 8
    leaf155Certificate.logOnePlusV leaf155InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf155InputLogOnePlusV_eq }

private noncomputable def leaf155Inputs : Inputs :=
  inputsOfCaches globalInput sk26RoundedInputs
    chi27InputQChi innerPair13Input
    leaf155InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf155LowerChecked :
    lowerCheck 24 leaf155Box leaf155Inputs = true := by
  rfl'

private theorem leaf155CoversExact : CoversExact 8
    leaf155Box leaf155Certificate leaf155InnerLog leaf155Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk26RoundedFacts chi27RoundedFacts
    innerPair13RoundedFacts leaf155RoundedFacts (by rfl)

private theorem leaf155FlatSound : Sound leaf155Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf155CertificateValid
    leaf155InnerLogValid leaf155CoversExact leaf155LowerChecked

private noncomputable def leaf156Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/16), kHi := (11/8), chiLo := (7/32), chiHi := (1/4) }

private noncomputable def leaf156Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554491/33554432) }, vSqrt := { lower := (65533/65536), upper := (174763/174759) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (43154811/33554432) }, upper := { exponent := 0, mantissa := (43/32) } }, logOuter := sk26LogOuterCertificate, logK := sk26LogKCertificate, logChi := chi28LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (174761/174759) } }, logDArg := sk26LogDArgCertificate }

private noncomputable def leaf156InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf156LocalValidity :
    LeafFacts leaf156Box leaf156Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf156Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (174763/174759) }) = true
      norm_num [leaf156Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf156CertificateValid :
    WideCertificateValid leaf156Box leaf156Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk26ValidityFacts chi28ValidityFacts
    leaf156LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf156CoverageChecked :
    coverageCheck (innerAD leaf156Box) leaf156InnerLog = true := by
  rfl'

private theorem leaf156InnerLogValid :
    leaf156InnerLog.Valid 8 (innerAD leaf156Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf156CoverageChecked

private noncomputable def leaf156InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629273/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf156InputLogOnePlusV_eq :
    leaf156InputLogOnePlusV = outerEnclosure 24
      (leaf156Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf156RoundedFacts : LeafRoundedFacts 8
    leaf156Certificate.logOnePlusV leaf156InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf156InputLogOnePlusV_eq }

private noncomputable def leaf156Inputs : Inputs :=
  inputsOfCaches globalInput sk26RoundedInputs
    chi28InputQChi innerPair17Input
    leaf156InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf156LowerChecked :
    lowerCheck 24 leaf156Box leaf156Inputs = true := by
  rfl'

private theorem leaf156CoversExact : CoversExact 8
    leaf156Box leaf156Certificate leaf156InnerLog leaf156Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk26RoundedFacts chi28RoundedFacts
    innerPair17RoundedFacts leaf156RoundedFacts (by rfl)

private theorem leaf156FlatSound : Sound leaf156Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf156CertificateValid
    leaf156InnerLogValid leaf156CoversExact leaf156LowerChecked

private noncomputable def leaf157Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (23/16), chiLo := (3/16), chiHi := (7/32) }

private noncomputable def leaf157Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554491/33554432) }, vSqrt := { lower := (65533/65536), upper := (2796208/2796149) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (42171831/33554432) }, upper := { exponent := 0, mantissa := (673/512) } }, logOuter := sk27LogOuterCertificate, logK := sk27LogKCertificate, logChi := chi27LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (5592357/5592298) } }, logDArg := sk27LogDArgCertificate }

private noncomputable def leaf157InnerLog : WideLogData :=
  innerPair18Data

set_option maxRecDepth 1000000 in
private theorem leaf157LocalValidity :
    LeafFacts leaf157Box leaf157Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf157Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (2796208/2796149) }) = true
      norm_num [leaf157Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf157CertificateValid :
    WideCertificateValid leaf157Box leaf157Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk27ValidityFacts chi27ValidityFacts
    leaf157LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf157CoverageChecked :
    coverageCheck (innerAD leaf157Box) leaf157InnerLog = true := by
  rfl'

private theorem leaf157InnerLogValid :
    leaf157InnerLog.Valid 8 (innerAD leaf157Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint9PositiveFacts.valid leaf157CoverageChecked

private noncomputable def leaf157InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (5814629/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf157InputLogOnePlusV_eq :
    leaf157InputLogOnePlusV = outerEnclosure 24
      (leaf157Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf157RoundedFacts : LeafRoundedFacts 8
    leaf157Certificate.logOnePlusV leaf157InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf157InputLogOnePlusV_eq }

private noncomputable def leaf157Inputs : Inputs :=
  inputsOfCaches globalInput sk27RoundedInputs
    chi27InputQChi innerPair18Input
    leaf157InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf157LowerChecked :
    lowerCheck 24 leaf157Box leaf157Inputs = true := by
  rfl'

private theorem leaf157CoversExact : CoversExact 8
    leaf157Box leaf157Certificate leaf157InnerLog leaf157Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk27RoundedFacts chi27RoundedFacts
    innerPair18RoundedFacts leaf157RoundedFacts (by rfl)

private theorem leaf157FlatSound : Sound leaf157Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf157CertificateValid
    leaf157InnerLogValid leaf157CoversExact leaf157LowerChecked

private noncomputable def leaf158Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (23/16), chiLo := (7/32), chiHi := (1/4) }

private noncomputable def leaf158Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554493/33554432) }, vSqrt := { lower := (65533/65536), upper := (1048578/1048553) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (43613533/33554432) }, upper := { exponent := 0, mantissa := (87/64) } }, logOuter := sk27LogOuterCertificate, logK := sk27LogKCertificate, logChi := chi28LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (2097131/2097106) } }, logDArg := sk27LogDArgCertificate }

private noncomputable def leaf158InnerLog : WideLogData :=
  innerPair130Data

set_option maxRecDepth 1000000 in
private theorem leaf158LocalValidity :
    LeafFacts leaf158Box leaf158Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf158Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (1048578/1048553) }) = true
      norm_num [leaf158Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf158CertificateValid :
    WideCertificateValid leaf158Box leaf158Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk27ValidityFacts chi28ValidityFacts
    leaf158LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf158CoverageChecked :
    coverageCheck (innerAD leaf158Box) leaf158InnerLog = true := by
  rfl'

private theorem leaf158InnerLogValid :
    leaf158InnerLog.Valid 8 (innerAD leaf158Box) :=
  wideLogDataValid_of_cachedCheck endpoint29PositiveFacts
    endpoint30PositiveFacts.valid leaf158CoverageChecked

private noncomputable def leaf158InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629281/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf158InputLogOnePlusV_eq :
    leaf158InputLogOnePlusV = outerEnclosure 24
      (leaf158Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf158RoundedFacts : LeafRoundedFacts 8
    leaf158Certificate.logOnePlusV leaf158InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf158InputLogOnePlusV_eq }

private noncomputable def leaf158Inputs : Inputs :=
  inputsOfCaches globalInput sk27RoundedInputs
    chi28InputQChi innerPair130Input
    leaf158InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf158LowerChecked :
    lowerCheck 24 leaf158Box leaf158Inputs = true := by
  rfl'

private theorem leaf158CoversExact : CoversExact 8
    leaf158Box leaf158Certificate leaf158InnerLog leaf158Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk27RoundedFacts chi28RoundedFacts
    innerPair130RoundedFacts leaf158RoundedFacts (by rfl)

private theorem leaf158FlatSound : Sound leaf158Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf158CertificateValid
    leaf158InnerLogValid leaf158CoversExact leaf158LowerChecked

private noncomputable def leaf159Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/16), kHi := (3/2), chiLo := (3/16), chiHi := (13/64) }

private noncomputable def leaf159Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108937/67108864) }, vSqrt := { lower := (16383/16384), upper := (2097156/2097113) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (85162857/67108864) }, upper := { exponent := 0, mantissa := (167/128) } }, logOuter := sk28LogOuterCertificate, logK := sk28LogKCertificate, logChi := chi34LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (4194269/4194226) } }, logDArg := sk28LogDArgCertificate }

private noncomputable def leaf159InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf159LocalValidity :
    LeafFacts leaf159Box leaf159Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf159Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (2097156/2097113) }) = true
      norm_num [leaf159Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf159CertificateValid :
    WideCertificateValid leaf159Box leaf159Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk28ValidityFacts chi34ValidityFacts
    leaf159LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf159CoverageChecked :
    coverageCheck (innerAD leaf159Box) leaf159InnerLog = true := by
  rfl'

private theorem leaf159InnerLogValid :
    leaf159InnerLog.Valid 8 (innerAD leaf159Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf159CoverageChecked

private noncomputable def leaf159InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629253/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf159InputLogOnePlusV_eq :
    leaf159InputLogOnePlusV = outerEnclosure 24
      (leaf159Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf159RoundedFacts : LeafRoundedFacts 8
    leaf159Certificate.logOnePlusV leaf159InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf159InputLogOnePlusV_eq }

private noncomputable def leaf159Inputs : Inputs :=
  inputsOfCaches globalInput sk28RoundedInputs
    chi34InputQChi innerPair16Input
    leaf159InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf159LowerChecked :
    lowerCheck 24 leaf159Box leaf159Inputs = true := by
  rfl'

private theorem leaf159CoversExact : CoversExact 8
    leaf159Box leaf159Certificate leaf159InnerLog leaf159Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk28RoundedFacts chi34RoundedFacts
    innerPair16RoundedFacts leaf159RoundedFacts (by rfl)

private theorem leaf159FlatSound : Sound leaf159Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf159CertificateValid
    leaf159InnerLogValid leaf159CoversExact leaf159LowerChecked

private noncomputable def leaf160Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/16), kHi := (3/2), chiLo := (13/64), chiHi := (7/32) }

private noncomputable def leaf160Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108939/67108864) }, vSqrt := { lower := (16383/16384), upper := (1048578/1048555) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (86670091/67108864) }, upper := { exponent := 0, mantissa := (85/64) } }, logOuter := sk28LogOuterCertificate, logK := sk28LogKCertificate, logChi := chi35LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (2097133/2097110) } }, logDArg := sk28LogDArgCertificate }

private noncomputable def leaf160InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf160LocalValidity :
    LeafFacts leaf160Box leaf160Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf160Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (1048578/1048555) }) = true
      norm_num [leaf160Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf160CertificateValid :
    WideCertificateValid leaf160Box leaf160Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk28ValidityFacts chi35ValidityFacts
    leaf160LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf160CoverageChecked :
    coverageCheck (innerAD leaf160Box) leaf160InnerLog = true := by
  rfl'

private theorem leaf160InnerLogValid :
    leaf160InnerLog.Valid 8 (innerAD leaf160Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf160CoverageChecked

private noncomputable def leaf160InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629265/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf160InputLogOnePlusV_eq :
    leaf160InputLogOnePlusV = outerEnclosure 24
      (leaf160Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf160RoundedFacts : LeafRoundedFacts 8
    leaf160Certificate.logOnePlusV leaf160InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf160InputLogOnePlusV_eq }

private noncomputable def leaf160Inputs : Inputs :=
  inputsOfCaches globalInput sk28RoundedInputs
    chi35InputQChi innerPair17Input
    leaf160InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf160LowerChecked :
    lowerCheck 24 leaf160Box leaf160Inputs = true := by
  rfl'

private theorem leaf160CoversExact : CoversExact 8
    leaf160Box leaf160Certificate leaf160InnerLog leaf160Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk28RoundedFacts chi35RoundedFacts
    innerPair17RoundedFacts leaf160RoundedFacts (by rfl)

private theorem leaf160FlatSound : Sound leaf160Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf160CertificateValid
    leaf160InnerLogValid leaf160CoversExact leaf160LowerChecked

private noncomputable def leaf161Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/16), kHi := (47/32), chiLo := (7/32), chiHi := (1/4) }

private noncomputable def leaf161Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108973/67108864) }, vSqrt := { lower := (65533/65536), upper := (2097154/2097105) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (88177293/67108864) }, upper := { exponent := 0, mantissa := (175/128) } }, logOuter := sk29LogOuterCertificate, logK := sk29LogKCertificate, logChi := chi28LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (4194259/4194210) } }, logDArg := sk29LogDArgCertificate }

private noncomputable def leaf161InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf161LocalValidity :
    LeafFacts leaf161Box leaf161Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf161Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (2097154/2097105) }) = true
      norm_num [leaf161Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf161CertificateValid :
    WideCertificateValid leaf161Box leaf161Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk29ValidityFacts chi28ValidityFacts
    leaf161LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf161CoverageChecked :
    coverageCheck (innerAD leaf161Box) leaf161InnerLog = true := by
  rfl'

private theorem leaf161InnerLogValid :
    leaf161InnerLog.Valid 8 (innerAD leaf161Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf161CoverageChecked

private noncomputable def leaf161InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629277/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf161InputLogOnePlusV_eq :
    leaf161InputLogOnePlusV = outerEnclosure 24
      (leaf161Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf161RoundedFacts : LeafRoundedFacts 8
    leaf161Certificate.logOnePlusV leaf161InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf161InputLogOnePlusV_eq }

private noncomputable def leaf161Inputs : Inputs :=
  inputsOfCaches globalInput sk29RoundedInputs
    chi28InputQChi innerPair21Input
    leaf161InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf161LowerChecked :
    lowerCheck 24 leaf161Box leaf161Inputs = true := by
  rfl'

private theorem leaf161CoversExact : CoversExact 8
    leaf161Box leaf161Certificate leaf161InnerLog leaf161Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk29RoundedFacts chi28RoundedFacts
    innerPair21RoundedFacts leaf161RoundedFacts (by rfl)

private theorem leaf161FlatSound : Sound leaf161Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf161CertificateValid
    leaf161InnerLogValid leaf161CoversExact leaf161LowerChecked

private noncomputable def leaf162Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/32), kHi := (3/2), chiLo := (7/32), chiHi := (1/4) }

private noncomputable def leaf162Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108975/67108864) }, vSqrt := { lower := (16383/16384), upper := (1048577/1048552) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (88636015/67108864) }, upper := { exponent := 0, mantissa := (11/8) } }, logOuter := sk30LogOuterCertificate, logK := sk30LogKCertificate, logChi := chi28LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (2097129/2097104) } }, logDArg := sk30LogDArgCertificate }

private noncomputable def leaf162InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf162LocalValidity :
    LeafFacts leaf162Box leaf162Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf162Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (1048577/1048552) }) = true
      norm_num [leaf162Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf162CertificateValid :
    WideCertificateValid leaf162Box leaf162Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk30ValidityFacts chi28ValidityFacts
    leaf162LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf162CoverageChecked :
    coverageCheck (innerAD leaf162Box) leaf162InnerLog = true := by
  rfl'

private theorem leaf162InnerLogValid :
    leaf162InnerLog.Valid 8 (innerAD leaf162Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf162CoverageChecked

private noncomputable def leaf162InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629281/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf162InputLogOnePlusV_eq :
    leaf162InputLogOnePlusV = outerEnclosure 24
      (leaf162Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf162RoundedFacts : LeafRoundedFacts 8
    leaf162Certificate.logOnePlusV leaf162InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf162InputLogOnePlusV_eq }

private noncomputable def leaf162Inputs : Inputs :=
  inputsOfCaches globalInput sk30RoundedInputs
    chi28InputQChi innerPair21Input
    leaf162InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf162LowerChecked :
    lowerCheck 24 leaf162Box leaf162Inputs = true := by
  rfl'

private theorem leaf162CoversExact : CoversExact 8
    leaf162Box leaf162Certificate leaf162InnerLog leaf162Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk30RoundedFacts chi28RoundedFacts
    innerPair21RoundedFacts leaf162RoundedFacts (by rfl)

private theorem leaf162FlatSound : Sound leaf162Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf162CertificateValid
    leaf162InnerLogValid leaf162CoversExact leaf162LowerChecked

private noncomputable def component3Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (9/8), chiLo := (1/16), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component3Node0_sound : Sound component3Node0Box :=
  sound_of_literal_split component3Node0Box leaf108Box leaf109Box
    .k (17/16) (by rfl) (by rfl)
    leaf108FlatSound leaf109FlatSound

private noncomputable def component3Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (9/8), chiLo := (3/32), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component3Node1_sound : Sound component3Node1Box :=
  sound_of_literal_split component3Node1Box leaf110Box leaf111Box
    .k (17/16) (by rfl) (by rfl)
    leaf110FlatSound leaf111FlatSound

private noncomputable def component3Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (9/8), chiLo := (1/16), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component3Node2_sound : Sound component3Node2Box :=
  sound_of_literal_split component3Node2Box component3Node0Box component3Node1Box
    .chi (3/32) (by rfl) (by rfl)
    component3Node0_sound component3Node1_sound

private noncomputable def component3Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (9/8), chiLo := (0), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component3Node3_sound : Sound component3Node3Box :=
  sound_of_literal_split component3Node3Box leaf107Box component3Node2Box
    .chi (1/16) (by rfl) (by rfl)
    leaf107FlatSound component3Node2_sound

private noncomputable def component3Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (5/4), chiLo := (1/16), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component3Node4_sound : Sound component3Node4Box :=
  sound_of_literal_split component3Node4Box leaf113Box leaf114Box
    .k (19/16) (by rfl) (by rfl)
    leaf113FlatSound leaf114FlatSound

private noncomputable def component3Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (5/4), chiLo := (3/32), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component3Node5_sound : Sound component3Node5Box :=
  sound_of_literal_split component3Node5Box leaf115Box leaf116Box
    .k (19/16) (by rfl) (by rfl)
    leaf115FlatSound leaf116FlatSound

private noncomputable def component3Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (5/4), chiLo := (1/16), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component3Node6_sound : Sound component3Node6Box :=
  sound_of_literal_split component3Node6Box component3Node4Box component3Node5Box
    .chi (3/32) (by rfl) (by rfl)
    component3Node4_sound component3Node5_sound

private noncomputable def component3Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (5/4), chiLo := (0), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component3Node7_sound : Sound component3Node7Box :=
  sound_of_literal_split component3Node7Box leaf112Box component3Node6Box
    .chi (1/16) (by rfl) (by rfl)
    leaf112FlatSound component3Node6_sound

private noncomputable def component3Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (5/4), chiLo := (0), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component3Node8_sound : Sound component3Node8Box :=
  sound_of_literal_split component3Node8Box component3Node3Box component3Node7Box
    .k (9/8) (by rfl) (by rfl)
    component3Node3_sound component3Node7_sound

private noncomputable def component3Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/16), kHi := (9/8), chiLo := (1/8), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component3Node9_sound : Sound component3Node9Box :=
  sound_of_literal_split component3Node9Box leaf118Box leaf119Box
    .chi (5/32) (by rfl) (by rfl)
    leaf118FlatSound leaf119FlatSound

private noncomputable def component3Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (9/8), chiLo := (1/8), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component3Node10_sound : Sound component3Node10Box :=
  sound_of_literal_split component3Node10Box leaf117Box component3Node9Box
    .k (17/16) (by rfl) (by rfl)
    leaf117FlatSound component3Node9_sound

private noncomputable def component3Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (17/16), chiLo := (3/16), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component3Node11_sound : Sound component3Node11Box :=
  sound_of_literal_split component3Node11Box leaf120Box leaf121Box
    .chi (7/32) (by rfl) (by rfl)
    leaf120FlatSound leaf121FlatSound

private noncomputable def component3Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/16), kHi := (9/8), chiLo := (3/16), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component3Node12_sound : Sound component3Node12Box :=
  sound_of_literal_split component3Node12Box leaf122Box leaf123Box
    .chi (7/32) (by rfl) (by rfl)
    leaf122FlatSound leaf123FlatSound

private noncomputable def component3Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (9/8), chiLo := (3/16), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component3Node13_sound : Sound component3Node13Box :=
  sound_of_literal_split component3Node13Box component3Node11Box component3Node12Box
    .k (17/16) (by rfl) (by rfl)
    component3Node11_sound component3Node12_sound

private noncomputable def component3Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (9/8), chiLo := (1/8), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component3Node14_sound : Sound component3Node14Box :=
  sound_of_literal_split component3Node14Box component3Node10Box component3Node13Box
    .chi (3/16) (by rfl) (by rfl)
    component3Node10_sound component3Node13_sound

private noncomputable def component3Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (5/4), chiLo := (1/8), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component3Node15_sound : Sound component3Node15Box :=
  sound_of_literal_split component3Node15Box leaf124Box leaf125Box
    .k (19/16) (by rfl) (by rfl)
    leaf124FlatSound leaf125FlatSound

private noncomputable def component3Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (5/4), chiLo := (5/32), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component3Node16_sound : Sound component3Node16Box :=
  sound_of_literal_split component3Node16Box leaf126Box leaf127Box
    .k (19/16) (by rfl) (by rfl)
    leaf126FlatSound leaf127FlatSound

private noncomputable def component3Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (5/4), chiLo := (1/8), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component3Node17_sound : Sound component3Node17Box :=
  sound_of_literal_split component3Node17Box component3Node15Box component3Node16Box
    .chi (5/32) (by rfl) (by rfl)
    component3Node15_sound component3Node16_sound

private noncomputable def component3Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (19/16), chiLo := (3/16), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component3Node18_sound : Sound component3Node18Box :=
  sound_of_literal_split component3Node18Box leaf128Box leaf129Box
    .chi (7/32) (by rfl) (by rfl)
    leaf128FlatSound leaf129FlatSound

private noncomputable def component3Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/16), kHi := (5/4), chiLo := (3/16), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component3Node19_sound : Sound component3Node19Box :=
  sound_of_literal_split component3Node19Box leaf130Box leaf131Box
    .chi (7/32) (by rfl) (by rfl)
    leaf130FlatSound leaf131FlatSound

private noncomputable def component3Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (5/4), chiLo := (3/16), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component3Node20_sound : Sound component3Node20Box :=
  sound_of_literal_split component3Node20Box component3Node18Box component3Node19Box
    .k (19/16) (by rfl) (by rfl)
    component3Node18_sound component3Node19_sound

private noncomputable def component3Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (5/4), chiLo := (1/8), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component3Node21_sound : Sound component3Node21Box :=
  sound_of_literal_split component3Node21Box component3Node17Box component3Node20Box
    .chi (3/16) (by rfl) (by rfl)
    component3Node17_sound component3Node20_sound

private noncomputable def component3Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (5/4), chiLo := (1/8), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component3Node22_sound : Sound component3Node22Box :=
  sound_of_literal_split component3Node22Box component3Node14Box component3Node21Box
    .k (9/8) (by rfl) (by rfl)
    component3Node14_sound component3Node21_sound

private noncomputable def component3Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (5/4), chiLo := (0), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component3Node23_sound : Sound component3Node23Box :=
  sound_of_literal_split component3Node23Box component3Node8Box component3Node22Box
    .chi (1/8) (by rfl) (by rfl)
    component3Node8_sound component3Node22_sound

private noncomputable def component3Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (3/2), chiLo := (1/32), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component3Node24_sound : Sound component3Node24Box :=
  sound_of_literal_split component3Node24Box leaf134Box leaf135Box
    .chi (3/64) (by rfl) (by rfl)
    leaf134FlatSound leaf135FlatSound

private noncomputable def component3Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (3/2), chiLo := (0), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component3Node25_sound : Sound component3Node25Box :=
  sound_of_literal_split component3Node25Box leaf133Box component3Node24Box
    .chi (1/32) (by rfl) (by rfl)
    leaf133FlatSound component3Node24_sound

private noncomputable def component3Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (3/2), chiLo := (0), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component3Node26_sound : Sound component3Node26Box :=
  sound_of_literal_split component3Node26Box leaf132Box component3Node25Box
    .k (11/8) (by rfl) (by rfl)
    leaf132FlatSound component3Node25_sound

private noncomputable def component3Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (11/8), chiLo := (1/16), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component3Node27_sound : Sound component3Node27Box :=
  sound_of_literal_split component3Node27Box leaf136Box leaf137Box
    .k (21/16) (by rfl) (by rfl)
    leaf136FlatSound leaf137FlatSound

private noncomputable def component3Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (11/8), chiLo := (3/32), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component3Node28_sound : Sound component3Node28Box :=
  sound_of_literal_split component3Node28Box leaf138Box leaf139Box
    .k (21/16) (by rfl) (by rfl)
    leaf138FlatSound leaf139FlatSound

private noncomputable def component3Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (11/8), chiLo := (1/16), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component3Node29_sound : Sound component3Node29Box :=
  sound_of_literal_split component3Node29Box component3Node27Box component3Node28Box
    .chi (3/32) (by rfl) (by rfl)
    component3Node27_sound component3Node28_sound

private noncomputable def component3Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (3/2), chiLo := (5/64), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component3Node30_sound : Sound component3Node30Box :=
  sound_of_literal_split component3Node30Box leaf141Box leaf142Box
    .k (23/16) (by rfl) (by rfl)
    leaf141FlatSound leaf142FlatSound

private noncomputable def component3Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (3/2), chiLo := (1/16), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component3Node31_sound : Sound component3Node31Box :=
  sound_of_literal_split component3Node31Box leaf140Box component3Node30Box
    .chi (5/64) (by rfl) (by rfl)
    leaf140FlatSound component3Node30_sound

private noncomputable def component3Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (3/2), chiLo := (3/32), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component3Node32_sound : Sound component3Node32Box :=
  sound_of_literal_split component3Node32Box leaf143Box leaf144Box
    .k (23/16) (by rfl) (by rfl)
    leaf143FlatSound leaf144FlatSound

private noncomputable def component3Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (3/2), chiLo := (1/16), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component3Node33_sound : Sound component3Node33Box :=
  sound_of_literal_split component3Node33Box component3Node31Box component3Node32Box
    .chi (3/32) (by rfl) (by rfl)
    component3Node31_sound component3Node32_sound

private noncomputable def component3Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (3/2), chiLo := (1/16), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component3Node34_sound : Sound component3Node34Box :=
  sound_of_literal_split component3Node34Box component3Node29Box component3Node33Box
    .k (11/8) (by rfl) (by rfl)
    component3Node29_sound component3Node33_sound

private noncomputable def component3Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (3/2), chiLo := (0), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component3Node35_sound : Sound component3Node35Box :=
  sound_of_literal_split component3Node35Box component3Node26Box component3Node34Box
    .chi (1/16) (by rfl) (by rfl)
    component3Node26_sound component3Node34_sound

private noncomputable def component3Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (11/8), chiLo := (1/8), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component3Node36_sound : Sound component3Node36Box :=
  sound_of_literal_split component3Node36Box leaf145Box leaf146Box
    .k (21/16) (by rfl) (by rfl)
    leaf145FlatSound leaf146FlatSound

private noncomputable def component3Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (11/8), chiLo := (5/32), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component3Node37_sound : Sound component3Node37Box :=
  sound_of_literal_split component3Node37Box leaf147Box leaf148Box
    .k (21/16) (by rfl) (by rfl)
    leaf147FlatSound leaf148FlatSound

private noncomputable def component3Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (11/8), chiLo := (1/8), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component3Node38_sound : Sound component3Node38Box :=
  sound_of_literal_split component3Node38Box component3Node36Box component3Node37Box
    .chi (5/32) (by rfl) (by rfl)
    component3Node36_sound component3Node37_sound

private noncomputable def component3Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (3/2), chiLo := (1/8), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component3Node39_sound : Sound component3Node39Box :=
  sound_of_literal_split component3Node39Box leaf149Box leaf150Box
    .k (23/16) (by rfl) (by rfl)
    leaf149FlatSound leaf150FlatSound

private noncomputable def component3Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (3/2), chiLo := (5/32), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component3Node40_sound : Sound component3Node40Box :=
  sound_of_literal_split component3Node40Box leaf151Box leaf152Box
    .k (23/16) (by rfl) (by rfl)
    leaf151FlatSound leaf152FlatSound

private noncomputable def component3Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (3/2), chiLo := (1/8), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component3Node41_sound : Sound component3Node41Box :=
  sound_of_literal_split component3Node41Box component3Node39Box component3Node40Box
    .chi (5/32) (by rfl) (by rfl)
    component3Node39_sound component3Node40_sound

private noncomputable def component3Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (3/2), chiLo := (1/8), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component3Node42_sound : Sound component3Node42Box :=
  sound_of_literal_split component3Node42Box component3Node38Box component3Node41Box
    .k (11/8) (by rfl) (by rfl)
    component3Node38_sound component3Node41_sound

private noncomputable def component3Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (21/16), chiLo := (3/16), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component3Node43_sound : Sound component3Node43Box :=
  sound_of_literal_split component3Node43Box leaf153Box leaf154Box
    .chi (7/32) (by rfl) (by rfl)
    leaf153FlatSound leaf154FlatSound

private noncomputable def component3Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/16), kHi := (11/8), chiLo := (3/16), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component3Node44_sound : Sound component3Node44Box :=
  sound_of_literal_split component3Node44Box leaf155Box leaf156Box
    .chi (7/32) (by rfl) (by rfl)
    leaf155FlatSound leaf156FlatSound

private noncomputable def component3Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (11/8), chiLo := (3/16), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component3Node45_sound : Sound component3Node45Box :=
  sound_of_literal_split component3Node45Box component3Node43Box component3Node44Box
    .k (21/16) (by rfl) (by rfl)
    component3Node43_sound component3Node44_sound

private noncomputable def component3Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (23/16), chiLo := (3/16), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component3Node46_sound : Sound component3Node46Box :=
  sound_of_literal_split component3Node46Box leaf157Box leaf158Box
    .chi (7/32) (by rfl) (by rfl)
    leaf157FlatSound leaf158FlatSound

private noncomputable def component3Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/16), kHi := (3/2), chiLo := (3/16), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component3Node47_sound : Sound component3Node47Box :=
  sound_of_literal_split component3Node47Box leaf159Box leaf160Box
    .chi (13/64) (by rfl) (by rfl)
    leaf159FlatSound leaf160FlatSound

private noncomputable def component3Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/16), kHi := (3/2), chiLo := (7/32), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component3Node48_sound : Sound component3Node48Box :=
  sound_of_literal_split component3Node48Box leaf161Box leaf162Box
    .k (47/32) (by rfl) (by rfl)
    leaf161FlatSound leaf162FlatSound

private noncomputable def component3Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/16), kHi := (3/2), chiLo := (3/16), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component3Node49_sound : Sound component3Node49Box :=
  sound_of_literal_split component3Node49Box component3Node47Box component3Node48Box
    .chi (7/32) (by rfl) (by rfl)
    component3Node47_sound component3Node48_sound

private noncomputable def component3Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (3/2), chiLo := (3/16), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component3Node50_sound : Sound component3Node50Box :=
  sound_of_literal_split component3Node50Box component3Node46Box component3Node49Box
    .k (23/16) (by rfl) (by rfl)
    component3Node46_sound component3Node49_sound

private noncomputable def component3Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (3/2), chiLo := (3/16), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component3Node51_sound : Sound component3Node51Box :=
  sound_of_literal_split component3Node51Box component3Node45Box component3Node50Box
    .k (11/8) (by rfl) (by rfl)
    component3Node45_sound component3Node50_sound

private noncomputable def component3Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (3/2), chiLo := (1/8), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component3Node52_sound : Sound component3Node52Box :=
  sound_of_literal_split component3Node52Box component3Node42Box component3Node51Box
    .chi (3/16) (by rfl) (by rfl)
    component3Node42_sound component3Node51_sound

private noncomputable def component3Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (3/2), chiLo := (0), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component3Node53_sound : Sound component3Node53Box :=
  sound_of_literal_split component3Node53Box component3Node35Box component3Node52Box
    .chi (1/8) (by rfl) (by rfl)
    component3Node35_sound component3Node52_sound

noncomputable def component3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (3/2), chiLo := (0), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
theorem component3_sound : Sound component3Box :=
  sound_of_literal_split component3Box component3Node23Box component3Node53Box
    .k (5/4) (by rfl) (by rfl)
    component3Node23_sound component3Node53_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
