import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch5
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

private noncomputable def leaf644Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (25/16), chiLo := (3/4), chiHi := (13/16) }

private noncomputable def leaf644Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (16777291/16777216) }, vSqrt := { lower := (16383/16384), upper := (5726459221/5726179328) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (35617591/33554432) }, upper := { exponent := 1, mantissa := (581/512) } }, logOuter := sk35LogOuterCertificate, logK := sk35LogKCertificate, logChi := chi76LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (11452638549/11452358656) } }, logDArg := sk35LogDArgCertificate }

private noncomputable def leaf644InnerLog : WideLogData :=
  innerPair245Data

set_option maxRecDepth 1000000 in
private theorem leaf644LocalValidity :
    LeafFacts leaf644Box leaf644Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf644Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (5726459221/5726179328) }) = true
      norm_num [leaf644Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf644CertificateValid :
    WideCertificateValid leaf644Box leaf644Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk35ValidityFacts chi76ValidityFacts
    leaf644LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf644CoverageChecked :
    coverageCheck (innerAD leaf644Box) leaf644InnerLog = true := by
  rfl'

private theorem leaf644InnerLogValid :
    leaf644InnerLog.Valid 8 (innerAD leaf644Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint76PositiveFacts.valid leaf644CoverageChecked

private noncomputable def leaf644InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629491/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf644InputLogOnePlusV_eq :
    leaf644InputLogOnePlusV = outerEnclosure 24
      (leaf644Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf644RoundedFacts : LeafRoundedFacts 8
    leaf644Certificate.logOnePlusV leaf644InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf644InputLogOnePlusV_eq }

private noncomputable def leaf644Inputs : Inputs :=
  inputsOfCaches globalInput sk35RoundedInputs
    chi76InputQChi innerPair245Input
    leaf644InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf644LowerChecked :
    lowerCheck 24 leaf644Box leaf644Inputs = true := by
  rfl'

private theorem leaf644CoversExact : CoversExact 8
    leaf644Box leaf644Certificate leaf644InnerLog leaf644Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk35RoundedFacts chi76RoundedFacts
    innerPair245RoundedFacts leaf644RoundedFacts (by rfl)

private theorem leaf644FlatSound : Sound leaf644Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf644CertificateValid
    leaf644InnerLogValid leaf644CoversExact leaf644LowerChecked

private noncomputable def leaf645Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/16), kHi := (13/8), chiLo := (3/4), chiHi := (13/16) }

private noncomputable def leaf645Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (16777293/16777216) }, vSqrt := { lower := (16383/16384), upper := (2454196809/2454069248) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (36403973/33554432) }, upper := { exponent := 1, mantissa := (297/256) } }, logOuter := sk36LogOuterCertificate, logK := sk36LogKCertificate, logChi := chi76LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (4908266057/4908138496) } }, logDArg := sk36LogDArgCertificate }

private noncomputable def leaf645InnerLog : WideLogData :=
  innerPair252Data

set_option maxRecDepth 1000000 in
private theorem leaf645LocalValidity :
    LeafFacts leaf645Box leaf645Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf645Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (2454196809/2454069248) }) = true
      norm_num [leaf645Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf645CertificateValid :
    WideCertificateValid leaf645Box leaf645Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk36ValidityFacts chi76ValidityFacts
    leaf645LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf645CoverageChecked :
    coverageCheck (innerAD leaf645Box) leaf645InnerLog = true := by
  rfl'

private theorem leaf645InnerLogValid :
    leaf645InnerLog.Valid 8 (innerAD leaf645Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint77PositiveFacts.valid leaf645CoverageChecked

private noncomputable def leaf645InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629517/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf645InputLogOnePlusV_eq :
    leaf645InputLogOnePlusV = outerEnclosure 24
      (leaf645Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf645RoundedFacts : LeafRoundedFacts 8
    leaf645Certificate.logOnePlusV leaf645InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf645InputLogOnePlusV_eq }

private noncomputable def leaf645Inputs : Inputs :=
  inputsOfCaches globalInput sk36RoundedInputs
    chi76InputQChi innerPair252Input
    leaf645InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf645LowerChecked :
    lowerCheck 24 leaf645Box leaf645Inputs = true := by
  rfl'

private theorem leaf645CoversExact : CoversExact 8
    leaf645Box leaf645Certificate leaf645InnerLog leaf645Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk36RoundedFacts chi76RoundedFacts
    innerPair252RoundedFacts leaf645RoundedFacts (by rfl)

private theorem leaf645FlatSound : Sound leaf645Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf645CertificateValid
    leaf645InnerLogValid leaf645CoversExact leaf645LowerChecked

private noncomputable def leaf646Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (25/16), chiLo := (13/16), chiHi := (7/8) }

private noncomputable def leaf646Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (16777293/16777216) }, vSqrt := { lower := (16383/16384), upper := (17179377663/17178435584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (37190357/33554432) }, upper := { exponent := 1, mantissa := (303/256) } }, logOuter := sk35LogOuterCertificate, logK := sk35LogKCertificate, logChi := chi77LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (34357813247/34356871168) } }, logDArg := sk35LogDArgCertificate }

private noncomputable def leaf646InnerLog : WideLogData :=
  innerPair258Data

set_option maxRecDepth 1000000 in
private theorem leaf646LocalValidity :
    LeafFacts leaf646Box leaf646Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf646Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (17179377663/17178435584) }) = true
      norm_num [leaf646Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf646CertificateValid :
    WideCertificateValid leaf646Box leaf646Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk35ValidityFacts chi77ValidityFacts
    leaf646LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf646CoverageChecked :
    coverageCheck (innerAD leaf646Box) leaf646InnerLog = true := by
  rfl'

private theorem leaf646InnerLogValid :
    leaf646InnerLog.Valid 8 (innerAD leaf646Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint77PositiveFacts.valid leaf646CoverageChecked

private noncomputable def leaf646InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629541/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf646InputLogOnePlusV_eq :
    leaf646InputLogOnePlusV = outerEnclosure 24
      (leaf646Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf646RoundedFacts : LeafRoundedFacts 8
    leaf646Certificate.logOnePlusV leaf646InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf646InputLogOnePlusV_eq }

private noncomputable def leaf646Inputs : Inputs :=
  inputsOfCaches globalInput sk35RoundedInputs
    chi77InputQChi innerPair258Input
    leaf646InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf646LowerChecked :
    lowerCheck 24 leaf646Box leaf646Inputs = true := by
  rfl'

private theorem leaf646CoversExact : CoversExact 8
    leaf646Box leaf646Certificate leaf646InnerLog leaf646Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk35RoundedFacts chi77RoundedFacts
    innerPair258RoundedFacts leaf646RoundedFacts (by rfl)

private theorem leaf646FlatSound : Sound leaf646Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf646CertificateValid
    leaf646InnerLogValid leaf646CoversExact leaf646LowerChecked

private noncomputable def leaf647Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/16), kHi := (13/8), chiLo := (13/16), chiHi := (7/8) }

private noncomputable def leaf647Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (16777295/16777216) }, vSqrt := { lower := (16383/16384), upper := (5726459221/5726126080) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (38042271/33554432) }, upper := { exponent := 1, mantissa := (155/128) } }, logOuter := sk36LogOuterCertificate, logK := sk36LogKCertificate, logChi := chi77LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (11452585301/11452252160) } }, logDArg := sk36LogDArgCertificate }

private noncomputable def leaf647InnerLog : WideLogData :=
  innerPair266Data

set_option maxRecDepth 1000000 in
private theorem leaf647LocalValidity :
    LeafFacts leaf647Box leaf647Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf647Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (5726459221/5726126080) }) = true
      norm_num [leaf647Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf647CertificateValid :
    WideCertificateValid leaf647Box leaf647Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk36ValidityFacts chi77ValidityFacts
    leaf647LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf647CoverageChecked :
    coverageCheck (innerAD leaf647Box) leaf647InnerLog = true := by
  rfl'

private theorem leaf647InnerLogValid :
    leaf647InnerLog.Valid 8 (innerAD leaf647Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint78PositiveFacts.valid leaf647CoverageChecked

private noncomputable def leaf647InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629569/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf647InputLogOnePlusV_eq :
    leaf647InputLogOnePlusV = outerEnclosure 24
      (leaf647Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf647RoundedFacts : LeafRoundedFacts 8
    leaf647Certificate.logOnePlusV leaf647InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf647InputLogOnePlusV_eq }

private noncomputable def leaf647Inputs : Inputs :=
  inputsOfCaches globalInput sk36RoundedInputs
    chi77InputQChi innerPair266Input
    leaf647InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf647LowerChecked :
    lowerCheck 24 leaf647Box leaf647Inputs = true := by
  rfl'

private theorem leaf647CoversExact : CoversExact 8
    leaf647Box leaf647Certificate leaf647InnerLog leaf647Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk36RoundedFacts chi77RoundedFacts
    innerPair266RoundedFacts leaf647RoundedFacts (by rfl)

private theorem leaf647FlatSound : Sound leaf647Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf647CertificateValid
    leaf647InnerLogValid leaf647CoversExact leaf647LowerChecked

private noncomputable def leaf648Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (27/16), chiLo := (3/4), chiHi := (13/16) }

private noncomputable def leaf648Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (16777295/16777216) }, vSqrt := { lower := (16383/16384), upper := (17179377663/17178431488) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (37190355/33554432) }, upper := { exponent := 1, mantissa := (607/512) } }, logOuter := sk33LogOuterCertificate, logK := sk33LogKCertificate, logChi := chi76LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (34357809151/34356862976) } }, logDArg := sk33LogDArgCertificate }

private noncomputable def leaf648InnerLog : WideLogData :=
  innerPair258Data

set_option maxRecDepth 1000000 in
private theorem leaf648LocalValidity :
    LeafFacts leaf648Box leaf648Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf648Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (17179377663/17178431488) }) = true
      norm_num [leaf648Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf648CertificateValid :
    WideCertificateValid leaf648Box leaf648Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk33ValidityFacts chi76ValidityFacts
    leaf648LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf648CoverageChecked :
    coverageCheck (innerAD leaf648Box) leaf648InnerLog = true := by
  rfl'

private theorem leaf648InnerLogValid :
    leaf648InnerLog.Valid 8 (innerAD leaf648Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint77PositiveFacts.valid leaf648CoverageChecked

private noncomputable def leaf648InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629543/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf648InputLogOnePlusV_eq :
    leaf648InputLogOnePlusV = outerEnclosure 24
      (leaf648Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf648RoundedFacts : LeafRoundedFacts 8
    leaf648Certificate.logOnePlusV leaf648InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf648InputLogOnePlusV_eq }

private noncomputable def leaf648Inputs : Inputs :=
  inputsOfCaches globalInput sk33RoundedInputs
    chi76InputQChi innerPair258Input
    leaf648InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf648LowerChecked :
    lowerCheck 24 leaf648Box leaf648Inputs = true := by
  rfl'

private theorem leaf648CoversExact : CoversExact 8
    leaf648Box leaf648Certificate leaf648InnerLog leaf648Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk33RoundedFacts chi76RoundedFacts
    innerPair258RoundedFacts leaf648RoundedFacts (by rfl)

private theorem leaf648FlatSound : Sound leaf648Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf648CertificateValid
    leaf648InnerLogValid leaf648CoversExact leaf648LowerChecked

private noncomputable def leaf649Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (3/4), chiHi := (13/16) }

private noncomputable def leaf649Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (16777297/16777216) }, vSqrt := { lower := (16383/16384), upper := (5726459221/5726126080) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (37976737/33554432) }, upper := { exponent := 1, mantissa := (155/128) } }, logOuter := sk34LogOuterCertificate, logK := sk34LogKCertificate, logChi := chi76LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (11452585301/11452252160) } }, logDArg := sk34LogDArgCertificate }

private noncomputable def leaf649InnerLog : WideLogData :=
  innerPair266Data

set_option maxRecDepth 1000000 in
private theorem leaf649LocalValidity :
    LeafFacts leaf649Box leaf649Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf649Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (5726459221/5726126080) }) = true
      norm_num [leaf649Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf649CertificateValid :
    WideCertificateValid leaf649Box leaf649Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk34ValidityFacts chi76ValidityFacts
    leaf649LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf649CoverageChecked :
    coverageCheck (innerAD leaf649Box) leaf649InnerLog = true := by
  rfl'

private theorem leaf649InnerLogValid :
    leaf649InnerLog.Valid 8 (innerAD leaf649Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint78PositiveFacts.valid leaf649CoverageChecked

private noncomputable def leaf649InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629569/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf649InputLogOnePlusV_eq :
    leaf649InputLogOnePlusV = outerEnclosure 24
      (leaf649Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf649RoundedFacts : LeafRoundedFacts 8
    leaf649Certificate.logOnePlusV leaf649InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf649InputLogOnePlusV_eq }

private noncomputable def leaf649Inputs : Inputs :=
  inputsOfCaches globalInput sk34RoundedInputs
    chi76InputQChi innerPair266Input
    leaf649InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf649LowerChecked :
    lowerCheck 24 leaf649Box leaf649Inputs = true := by
  rfl'

private theorem leaf649CoversExact : CoversExact 8
    leaf649Box leaf649Certificate leaf649InnerLog leaf649Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk34RoundedFacts chi76RoundedFacts
    innerPair266RoundedFacts leaf649RoundedFacts (by rfl)

private theorem leaf649FlatSound : Sound leaf649Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf649CertificateValid
    leaf649InnerLogValid leaf649CoversExact leaf649LowerChecked

private noncomputable def leaf650Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (27/16), chiLo := (13/16), chiHi := (7/8) }

private noncomputable def leaf650Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (16777297/16777216) }, vSqrt := { lower := (16383/16384), upper := (34358231037/34356641792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (38894185/33554432) }, upper := { exponent := 1, mantissa := (317/256) } }, logOuter := sk33LogOuterCertificate, logK := sk33LogKCertificate, logChi := chi77LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68714872829/68713283584) } }, logDArg := sk33LogDArgCertificate }

private noncomputable def leaf650InnerLog : WideLogData :=
  innerPair274Data

set_option maxRecDepth 1000000 in
private theorem leaf650LocalValidity :
    LeafFacts leaf650Box leaf650Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf650Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34358231037/34356641792) }) = true
      norm_num [leaf650Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf650CertificateValid :
    WideCertificateValid leaf650Box leaf650Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk33ValidityFacts chi77ValidityFacts
    leaf650LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf650CoverageChecked :
    coverageCheck (innerAD leaf650Box) leaf650InnerLog = true := by
  rfl'

private theorem leaf650InnerLogValid :
    leaf650InnerLog.Valid 8 (innerAD leaf650Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint79PositiveFacts.valid leaf650CoverageChecked

private noncomputable def leaf650InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629469/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf650InputLogOnePlusV_eq :
    leaf650InputLogOnePlusV = outerEnclosure 24
      (leaf650Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf650RoundedFacts : LeafRoundedFacts 8
    leaf650Certificate.logOnePlusV leaf650InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf650InputLogOnePlusV_eq }

private noncomputable def leaf650Inputs : Inputs :=
  inputsOfCaches globalInput sk33RoundedInputs
    chi77InputQChi innerPair274Input
    leaf650InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf650LowerChecked :
    lowerCheck 24 leaf650Box leaf650Inputs = true := by
  rfl'

private theorem leaf650CoversExact : CoversExact 8
    leaf650Box leaf650Certificate leaf650InnerLog leaf650Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk33RoundedFacts chi77RoundedFacts
    innerPair274RoundedFacts leaf650RoundedFacts (by rfl)

private theorem leaf650FlatSound : Sound leaf650Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf650CertificateValid
    leaf650InnerLogValid leaf650CoversExact leaf650LowerChecked

private noncomputable def leaf651Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (13/16), chiHi := (7/8) }

private noncomputable def leaf651Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (16777299/16777216) }, vSqrt := { lower := (16383/16384), upper := (34358231037/34356527104) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (39746099/33554432) }, upper := { exponent := 1, mantissa := (81/64) } }, logOuter := sk34LogOuterCertificate, logK := sk34LogKCertificate, logChi := chi77LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68714758141/68713054208) } }, logDArg := sk34LogDArgCertificate }

private noncomputable def leaf651InnerLog : WideLogData :=
  innerPair275Data

set_option maxRecDepth 1000000 in
private theorem leaf651LocalValidity :
    LeafFacts leaf651Box leaf651Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf651Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34358231037/34356527104) }) = true
      norm_num [leaf651Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf651CertificateValid :
    WideCertificateValid leaf651Box leaf651Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk34ValidityFacts chi77ValidityFacts
    leaf651LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf651CoverageChecked :
    coverageCheck (innerAD leaf651Box) leaf651InnerLog = true := by
  rfl'

private theorem leaf651InnerLogValid :
    leaf651InnerLog.Valid 8 (innerAD leaf651Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint90PositiveFacts.valid leaf651CoverageChecked

private noncomputable def leaf651InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629497/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf651InputLogOnePlusV_eq :
    leaf651InputLogOnePlusV = outerEnclosure 24
      (leaf651Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf651RoundedFacts : LeafRoundedFacts 8
    leaf651Certificate.logOnePlusV leaf651InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf651InputLogOnePlusV_eq }

private noncomputable def leaf651Inputs : Inputs :=
  inputsOfCaches globalInput sk34RoundedInputs
    chi77InputQChi innerPair275Input
    leaf651InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf651LowerChecked :
    lowerCheck 24 leaf651Box leaf651Inputs = true := by
  rfl'

private theorem leaf651CoversExact : CoversExact 8
    leaf651Box leaf651Certificate leaf651InnerLog leaf651Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk34RoundedFacts chi77RoundedFacts
    innerPair275RoundedFacts leaf651RoundedFacts (by rfl)

private theorem leaf651FlatSound : Sound leaf651Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf651CertificateValid
    leaf651InnerLogValid leaf651CoversExact leaf651LowerChecked

private noncomputable def leaf652Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (25/16), chiLo := (7/8), chiHi := (15/16) }

private noncomputable def leaf652Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (16777295/16777216) }, vSqrt := { lower := (16383/16384), upper := (17179377663/17178333184) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (38763123/33554432) }, upper := { exponent := 1, mantissa := (631/512) } }, logOuter := sk35LogOuterCertificate, logK := sk35LogKCertificate, logChi := chi78LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (34357710847/34356666368) } }, logDArg := sk35LogDArgCertificate }

private noncomputable def leaf652InnerLog : WideLogData :=
  innerPair267Data

set_option maxRecDepth 1000000 in
private theorem leaf652LocalValidity :
    LeafFacts leaf652Box leaf652Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf652Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (17179377663/17178333184) }) = true
      norm_num [leaf652Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf652CertificateValid :
    WideCertificateValid leaf652Box leaf652Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk35ValidityFacts chi78ValidityFacts
    leaf652LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf652CoverageChecked :
    coverageCheck (innerAD leaf652Box) leaf652InnerLog = true := by
  rfl'

private theorem leaf652InnerLogValid :
    leaf652InnerLog.Valid 8 (innerAD leaf652Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint79PositiveFacts.valid leaf652CoverageChecked

private noncomputable def leaf652InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629591/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf652InputLogOnePlusV_eq :
    leaf652InputLogOnePlusV = outerEnclosure 24
      (leaf652Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf652RoundedFacts : LeafRoundedFacts 8
    leaf652Certificate.logOnePlusV leaf652InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf652InputLogOnePlusV_eq }

private noncomputable def leaf652Inputs : Inputs :=
  inputsOfCaches globalInput sk35RoundedInputs
    chi78InputQChi innerPair267Input
    leaf652InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf652LowerChecked :
    lowerCheck 24 leaf652Box leaf652Inputs = true := by
  rfl'

private theorem leaf652CoversExact : CoversExact 8
    leaf652Box leaf652Certificate leaf652InnerLog leaf652Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk35RoundedFacts chi78RoundedFacts
    innerPair267RoundedFacts leaf652RoundedFacts (by rfl)

private theorem leaf652FlatSound : Sound leaf652Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf652CertificateValid
    leaf652InnerLogValid leaf652CoversExact leaf652LowerChecked

private noncomputable def leaf653Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/16), kHi := (13/8), chiLo := (7/8), chiHi := (15/16) }

private noncomputable def leaf653Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (16777297/16777216) }, vSqrt := { lower := (16383/16384), upper := (34358231037/34356543488) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (39680569/33554432) }, upper := { exponent := 1, mantissa := (323/256) } }, logOuter := sk36LogOuterCertificate, logK := sk36LogKCertificate, logChi := chi78LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68714774525/68713086976) } }, logDArg := sk36LogDArgCertificate }

private noncomputable def leaf653InnerLog : WideLogData :=
  innerPair275Data

set_option maxRecDepth 1000000 in
private theorem leaf653LocalValidity :
    LeafFacts leaf653Box leaf653Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf653Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34358231037/34356543488) }) = true
      norm_num [leaf653Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf653CertificateValid :
    WideCertificateValid leaf653Box leaf653Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk36ValidityFacts chi78ValidityFacts
    leaf653LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf653CoverageChecked :
    coverageCheck (innerAD leaf653Box) leaf653InnerLog = true := by
  rfl'

private theorem leaf653InnerLogValid :
    leaf653InnerLog.Valid 8 (innerAD leaf653Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint90PositiveFacts.valid leaf653CoverageChecked

private noncomputable def leaf653InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629493/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf653InputLogOnePlusV_eq :
    leaf653InputLogOnePlusV = outerEnclosure 24
      (leaf653Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf653RoundedFacts : LeafRoundedFacts 8
    leaf653Certificate.logOnePlusV leaf653InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf653InputLogOnePlusV_eq }

private noncomputable def leaf653Inputs : Inputs :=
  inputsOfCaches globalInput sk36RoundedInputs
    chi78InputQChi innerPair275Input
    leaf653InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf653LowerChecked :
    lowerCheck 24 leaf653Box leaf653Inputs = true := by
  rfl'

private theorem leaf653CoversExact : CoversExact 8
    leaf653Box leaf653Certificate leaf653InnerLog leaf653Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk36RoundedFacts chi78RoundedFacts
    innerPair275RoundedFacts leaf653RoundedFacts (by rfl)

private theorem leaf653FlatSound : Sound leaf653Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf653CertificateValid
    leaf653InnerLogValid leaf653CoversExact leaf653LowerChecked

private noncomputable def leaf654Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (25/16), chiLo := (15/16), chiHi := (1) }

private noncomputable def leaf654Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (16777297/16777216) }, vSqrt := { lower := (16383/16384), upper := (880980283/880934912) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (40335889/33554432) }, upper := { exponent := 1, mantissa := (41/32) } }, logOuter := sk35LogOuterCertificate, logK := sk35LogKCertificate, logChi := chi79LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (1761915195/1761869824) } }, logDArg := sk35LogDArgCertificate }

private noncomputable def leaf654InnerLog : WideLogData :=
  innerPair280Data

set_option maxRecDepth 1000000 in
private theorem leaf654LocalValidity :
    LeafFacts leaf654Box leaf654Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf654Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (880980283/880934912) }) = true
      norm_num [leaf654Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf654CertificateValid :
    WideCertificateValid leaf654Box leaf654Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk35ValidityFacts chi79ValidityFacts
    leaf654LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf654CoverageChecked :
    coverageCheck (innerAD leaf654Box) leaf654InnerLog = true := by
  rfl'

private theorem leaf654InnerLogValid :
    leaf654InnerLog.Valid 8 (innerAD leaf654Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint90PositiveFacts.valid leaf654CoverageChecked

private noncomputable def leaf654InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629513/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf654InputLogOnePlusV_eq :
    leaf654InputLogOnePlusV = outerEnclosure 24
      (leaf654Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf654RoundedFacts : LeafRoundedFacts 8
    leaf654Certificate.logOnePlusV leaf654InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf654InputLogOnePlusV_eq }

private noncomputable def leaf654Inputs : Inputs :=
  inputsOfCaches globalInput sk35RoundedInputs
    chi79InputQChi innerPair280Input
    leaf654InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf654LowerChecked :
    lowerCheck 24 leaf654Box leaf654Inputs = true := by
  rfl'

private theorem leaf654CoversExact : CoversExact 8
    leaf654Box leaf654Certificate leaf654InnerLog leaf654Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk35RoundedFacts chi79RoundedFacts
    innerPair280RoundedFacts leaf654RoundedFacts (by rfl)

private theorem leaf654FlatSound : Sound leaf654Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf654CertificateValid
    leaf654InnerLogValid leaf654CoversExact leaf654LowerChecked

private noncomputable def leaf655Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/16), kHi := (13/8), chiLo := (15/16), chiHi := (1) }

private noncomputable def leaf655Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (16777299/16777216) }, vSqrt := { lower := (16383/16384), upper := (34358231037/34356330496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (41318867/33554432) }, upper := { exponent := 1, mantissa := (21/16) } }, logOuter := sk36LogOuterCertificate, logK := sk36LogKCertificate, logChi := chi79LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68714561533/68712660992) } }, logDArg := sk36LogDArgCertificate }

private noncomputable def leaf655InnerLog : WideLogData :=
  innerPair287Data

set_option maxRecDepth 1000000 in
private theorem leaf655LocalValidity :
    LeafFacts leaf655Box leaf655Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf655Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34358231037/34356330496) }) = true
      norm_num [leaf655Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf655CertificateValid :
    WideCertificateValid leaf655Box leaf655Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk36ValidityFacts chi79ValidityFacts
    leaf655LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf655CoverageChecked :
    coverageCheck (innerAD leaf655Box) leaf655InnerLog = true := by
  rfl'

private theorem leaf655InnerLogValid :
    leaf655InnerLog.Valid 8 (innerAD leaf655Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint91PositiveFacts.valid leaf655CoverageChecked

private noncomputable def leaf655InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629545/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf655InputLogOnePlusV_eq :
    leaf655InputLogOnePlusV = outerEnclosure 24
      (leaf655Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf655RoundedFacts : LeafRoundedFacts 8
    leaf655Certificate.logOnePlusV leaf655InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf655InputLogOnePlusV_eq }

private noncomputable def leaf655Inputs : Inputs :=
  inputsOfCaches globalInput sk36RoundedInputs
    chi79InputQChi innerPair287Input
    leaf655InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf655LowerChecked :
    lowerCheck 24 leaf655Box leaf655Inputs = true := by
  rfl'

private theorem leaf655CoversExact : CoversExact 8
    leaf655Box leaf655Certificate leaf655InnerLog leaf655Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk36RoundedFacts chi79RoundedFacts
    innerPair287RoundedFacts leaf655RoundedFacts (by rfl)

private theorem leaf655FlatSound : Sound leaf655Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf655CertificateValid
    leaf655InnerLogValid leaf655CoversExact leaf655LowerChecked

private noncomputable def leaf656Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (27/16), chiLo := (7/8), chiHi := (15/16) }

private noncomputable def leaf656Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (16777299/16777216) }, vSqrt := { lower := (16383/16384), upper := (483918747/483893248) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (40598015/33554432) }, upper := { exponent := 1, mantissa := (661/512) } }, logOuter := sk33LogOuterCertificate, logK := sk33LogKCertificate, logChi := chi78LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (967811995/967786496) } }, logDArg := sk33LogDArgCertificate }

private noncomputable def leaf656InnerLog : WideLogData :=
  innerPair281Data

set_option maxRecDepth 1000000 in
private theorem leaf656LocalValidity :
    LeafFacts leaf656Box leaf656Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf656Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (483918747/483893248) }) = true
      norm_num [leaf656Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf656CertificateValid :
    WideCertificateValid leaf656Box leaf656Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk33ValidityFacts chi78ValidityFacts
    leaf656LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf656CoverageChecked :
    coverageCheck (innerAD leaf656Box) leaf656InnerLog = true := by
  rfl'

private theorem leaf656InnerLogValid :
    leaf656InnerLog.Valid 8 (innerAD leaf656Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint91PositiveFacts.valid leaf656CoverageChecked

private noncomputable def leaf656InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629523/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf656InputLogOnePlusV_eq :
    leaf656InputLogOnePlusV = outerEnclosure 24
      (leaf656Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf656RoundedFacts : LeafRoundedFacts 8
    leaf656Certificate.logOnePlusV leaf656InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf656InputLogOnePlusV_eq }

private noncomputable def leaf656Inputs : Inputs :=
  inputsOfCaches globalInput sk33RoundedInputs
    chi78InputQChi innerPair281Input
    leaf656InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf656LowerChecked :
    lowerCheck 24 leaf656Box leaf656Inputs = true := by
  rfl'

private theorem leaf656CoversExact : CoversExact 8
    leaf656Box leaf656Certificate leaf656InnerLog leaf656Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk33RoundedFacts chi78RoundedFacts
    innerPair281RoundedFacts leaf656RoundedFacts (by rfl)

private theorem leaf656FlatSound : Sound leaf656Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf656CertificateValid
    leaf656InnerLogValid leaf656CoversExact leaf656LowerChecked

private noncomputable def leaf657Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (7/8), chiHi := (15/16) }

private noncomputable def leaf657Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (16777301/16777216) }, vSqrt := { lower := (16383/16384), upper := (34358231037/34356297728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (41515461/33554432) }, upper := { exponent := 1, mantissa := (169/128) } }, logOuter := sk34LogOuterCertificate, logK := sk34LogKCertificate, logChi := chi78LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68714528765/68712595456) } }, logDArg := sk34LogDArgCertificate }

private noncomputable def leaf657InnerLog : WideLogData :=
  innerPair288Data

set_option maxRecDepth 1000000 in
private theorem leaf657LocalValidity :
    LeafFacts leaf657Box leaf657Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf657Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34358231037/34356297728) }) = true
      norm_num [leaf657Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf657CertificateValid :
    WideCertificateValid leaf657Box leaf657Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk34ValidityFacts chi78ValidityFacts
    leaf657LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf657CoverageChecked :
    coverageCheck (innerAD leaf657Box) leaf657InnerLog = true := by
  rfl'

private theorem leaf657InnerLogValid :
    leaf657InnerLog.Valid 8 (innerAD leaf657Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint92PositiveFacts.valid leaf657CoverageChecked

private noncomputable def leaf657InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629553/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf657InputLogOnePlusV_eq :
    leaf657InputLogOnePlusV = outerEnclosure 24
      (leaf657Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf657RoundedFacts : LeafRoundedFacts 8
    leaf657Certificate.logOnePlusV leaf657InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf657InputLogOnePlusV_eq }

private noncomputable def leaf657Inputs : Inputs :=
  inputsOfCaches globalInput sk34RoundedInputs
    chi78InputQChi innerPair288Input
    leaf657InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf657LowerChecked :
    lowerCheck 24 leaf657Box leaf657Inputs = true := by
  rfl'

private theorem leaf657CoversExact : CoversExact 8
    leaf657Box leaf657Certificate leaf657InnerLog leaf657Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk34RoundedFacts chi78RoundedFacts
    innerPair288RoundedFacts leaf657RoundedFacts (by rfl)

private theorem leaf657FlatSound : Sound leaf657Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf657CertificateValid
    leaf657InnerLogValid leaf657CoversExact leaf657LowerChecked

private noncomputable def leaf658Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (27/16), chiLo := (15/16), chiHi := (1) }

private noncomputable def leaf658Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (16777301/16777216) }, vSqrt := { lower := (16383/16384), upper := (34358231037/34356199424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (42301845/33554432) }, upper := { exponent := 1, mantissa := (43/32) } }, logOuter := sk33LogOuterCertificate, logK := sk33LogKCertificate, logChi := chi79LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68714430461/68712398848) } }, logDArg := sk33LogDArgCertificate }

private noncomputable def leaf658InnerLog : WideLogData :=
  innerPair295Data

set_option maxRecDepth 1000000 in
private theorem leaf658LocalValidity :
    LeafFacts leaf658Box leaf658Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf658Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34358231037/34356199424) }) = true
      norm_num [leaf658Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf658CertificateValid :
    WideCertificateValid leaf658Box leaf658Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk33ValidityFacts chi79ValidityFacts
    leaf658LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf658CoverageChecked :
    coverageCheck (innerAD leaf658Box) leaf658InnerLog = true := by
  rfl'

private theorem leaf658InnerLogValid :
    leaf658InnerLog.Valid 8 (innerAD leaf658Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint92PositiveFacts.valid leaf658CoverageChecked

private noncomputable def leaf658InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629577/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf658InputLogOnePlusV_eq :
    leaf658InputLogOnePlusV = outerEnclosure 24
      (leaf658Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf658RoundedFacts : LeafRoundedFacts 8
    leaf658Certificate.logOnePlusV leaf658InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf658InputLogOnePlusV_eq }

private noncomputable def leaf658Inputs : Inputs :=
  inputsOfCaches globalInput sk33RoundedInputs
    chi79InputQChi innerPair295Input
    leaf658InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf658LowerChecked :
    lowerCheck 24 leaf658Box leaf658Inputs = true := by
  rfl'

private theorem leaf658CoversExact : CoversExact 8
    leaf658Box leaf658Certificate leaf658InnerLog leaf658Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk33RoundedFacts chi79RoundedFacts
    innerPair295RoundedFacts leaf658RoundedFacts (by rfl)

private theorem leaf658FlatSound : Sound leaf658Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf658CertificateValid
    leaf658InnerLogValid leaf658CoversExact leaf658LowerChecked

private noncomputable def leaf659Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (15/16), chiHi := (1) }

private noncomputable def leaf659Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (16777303/16777216) }, vSqrt := { lower := (16383/16384), upper := (11452743679/11452022784) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (43284823/33554432) }, upper := { exponent := 1, mantissa := (11/8) } }, logOuter := sk34LogOuterCertificate, logK := sk34LogKCertificate, logChi := chi79LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (22904766463/22904045568) } }, logDArg := sk34LogDArgCertificate }

private noncomputable def leaf659InnerLog : WideLogData :=
  innerPair341Data

set_option maxRecDepth 1000000 in
private theorem leaf659LocalValidity :
    LeafFacts leaf659Box leaf659Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf659Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (11452743679/11452022784) }) = true
      norm_num [leaf659Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf659CertificateValid :
    WideCertificateValid leaf659Box leaf659Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk34ValidityFacts chi79ValidityFacts
    leaf659LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf659CoverageChecked :
    coverageCheck (innerAD leaf659Box) leaf659InnerLog = true := by
  rfl'

private theorem leaf659InnerLogValid :
    leaf659InnerLog.Valid 8 (innerAD leaf659Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint93PositiveFacts.valid leaf659CoverageChecked

private noncomputable def leaf659InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629609/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf659InputLogOnePlusV_eq :
    leaf659InputLogOnePlusV = outerEnclosure 24
      (leaf659Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf659RoundedFacts : LeafRoundedFacts 8
    leaf659Certificate.logOnePlusV leaf659InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf659InputLogOnePlusV_eq }

private noncomputable def leaf659Inputs : Inputs :=
  inputsOfCaches globalInput sk34RoundedInputs
    chi79InputQChi innerPair341Input
    leaf659InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf659LowerChecked :
    lowerCheck 24 leaf659Box leaf659Inputs = true := by
  rfl'

private theorem leaf659CoversExact : CoversExact 8
    leaf659Box leaf659Certificate leaf659InnerLog leaf659Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk34RoundedFacts chi79RoundedFacts
    innerPair341RoundedFacts leaf659RoundedFacts (by rfl)

private theorem leaf659FlatSound : Sound leaf659Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf659CertificateValid
    leaf659InnerLogValid leaf659CoversExact leaf659LowerChecked

private noncomputable def leaf660Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16), chiLo := (3/4), chiHi := (25/32) }

private noncomputable def leaf660Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (33554539/33554432) }, vSqrt := { lower := (16383/16384), upper := (818065603/818018304) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (77559063/67108864) }, upper := { exponent := 1, mantissa := (1237/1024) } }, logOuter := sk39LogOuterCertificate, logK := sk39LogKCertificate, logChi := chi88LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (1636083907/1636036608) } }, logDArg := sk39LogDArgCertificate }

private noncomputable def leaf660InnerLog : WideLogData :=
  innerPair266Data

set_option maxRecDepth 1000000 in
private theorem leaf660LocalValidity :
    LeafFacts leaf660Box leaf660Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf660Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (818065603/818018304) }) = true
      norm_num [leaf660Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf660CertificateValid :
    WideCertificateValid leaf660Box leaf660Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk39ValidityFacts chi88ValidityFacts
    leaf660LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf660CoverageChecked :
    coverageCheck (innerAD leaf660Box) leaf660InnerLog = true := by
  rfl'

private theorem leaf660InnerLogValid :
    leaf660InnerLog.Valid 8 (innerAD leaf660Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint78PositiveFacts.valid leaf660CoverageChecked

private noncomputable def leaf660InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814783/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf660InputLogOnePlusV_eq :
    leaf660InputLogOnePlusV = outerEnclosure 24
      (leaf660Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf660RoundedFacts : LeafRoundedFacts 8
    leaf660Certificate.logOnePlusV leaf660InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf660InputLogOnePlusV_eq }

private noncomputable def leaf660Inputs : Inputs :=
  inputsOfCaches globalInput sk39RoundedInputs
    chi88InputQChi innerPair266Input
    leaf660InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf660LowerChecked :
    lowerCheck 24 leaf660Box leaf660Inputs = true := by
  rfl'

private theorem leaf660CoversExact : CoversExact 8
    leaf660Box leaf660Certificate leaf660InnerLog leaf660Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk39RoundedFacts chi88RoundedFacts
    innerPair266RoundedFacts leaf660RoundedFacts (by rfl)

private theorem leaf660FlatSound : Sound leaf660Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf660CertificateValid
    leaf660InnerLogValid leaf660CoversExact leaf660LowerChecked

private noncomputable def leaf661Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8), chiLo := (3/4), chiHi := (25/32) }

private noncomputable def leaf661Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (33554541/33554432) }, vSqrt := { lower := (16383/16384), upper := (17179377663/17178333184) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (79131829/67108864) }, upper := { exponent := 1, mantissa := (631/512) } }, logOuter := sk40LogOuterCertificate, logK := sk40LogKCertificate, logChi := chi88LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (34357710847/34356666368) } }, logDArg := sk40LogDArgCertificate }

private noncomputable def leaf661InnerLog : WideLogData :=
  innerPair274Data

set_option maxRecDepth 1000000 in
private theorem leaf661LocalValidity :
    LeafFacts leaf661Box leaf661Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf661Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (17179377663/17178333184) }) = true
      norm_num [leaf661Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf661CertificateValid :
    WideCertificateValid leaf661Box leaf661Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk40ValidityFacts chi88ValidityFacts
    leaf661LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf661CoverageChecked :
    coverageCheck (innerAD leaf661Box) leaf661InnerLog = true := by
  rfl'

private theorem leaf661InnerLogValid :
    leaf661InnerLog.Valid 8 (innerAD leaf661Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint79PositiveFacts.valid leaf661CoverageChecked

private noncomputable def leaf661InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629591/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf661InputLogOnePlusV_eq :
    leaf661InputLogOnePlusV = outerEnclosure 24
      (leaf661Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf661RoundedFacts : LeafRoundedFacts 8
    leaf661Certificate.logOnePlusV leaf661InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf661InputLogOnePlusV_eq }

private noncomputable def leaf661Inputs : Inputs :=
  inputsOfCaches globalInput sk40RoundedInputs
    chi88InputQChi innerPair274Input
    leaf661InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf661LowerChecked :
    lowerCheck 24 leaf661Box leaf661Inputs = true := by
  rfl'

private theorem leaf661CoversExact : CoversExact 8
    leaf661Box leaf661Certificate leaf661InnerLog leaf661Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk40RoundedFacts chi88RoundedFacts
    innerPair274RoundedFacts leaf661RoundedFacts (by rfl)

private theorem leaf661FlatSound : Sound leaf661Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf661CertificateValid
    leaf661InnerLogValid leaf661CoversExact leaf661LowerChecked

private noncomputable def leaf662Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16), chiLo := (25/32), chiHi := (13/16) }

private noncomputable def leaf662Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (33554541/33554432) }, vSqrt := { lower := (16383/16384), upper := (34358231037/34356649984) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (79393957/67108864) }, upper := { exponent := 1, mantissa := (633/512) } }, logOuter := sk39LogOuterCertificate, logK := sk39LogKCertificate, logChi := chi89LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68714881021/68713299968) } }, logDArg := sk39LogDArgCertificate }

private noncomputable def leaf662InnerLog : WideLogData :=
  innerPair274Data

set_option maxRecDepth 1000000 in
private theorem leaf662LocalValidity :
    LeafFacts leaf662Box leaf662Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf662Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34358231037/34356649984) }) = true
      norm_num [leaf662Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf662CertificateValid :
    WideCertificateValid leaf662Box leaf662Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk39ValidityFacts chi89ValidityFacts
    leaf662LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf662CoverageChecked :
    coverageCheck (innerAD leaf662Box) leaf662InnerLog = true := by
  rfl'

private theorem leaf662InnerLogValid :
    leaf662InnerLog.Valid 8 (innerAD leaf662Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint79PositiveFacts.valid leaf662CoverageChecked

private noncomputable def leaf662InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629467/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf662InputLogOnePlusV_eq :
    leaf662InputLogOnePlusV = outerEnclosure 24
      (leaf662Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf662RoundedFacts : LeafRoundedFacts 8
    leaf662Certificate.logOnePlusV leaf662InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf662InputLogOnePlusV_eq }

private noncomputable def leaf662Inputs : Inputs :=
  inputsOfCaches globalInput sk39RoundedInputs
    chi89InputQChi innerPair274Input
    leaf662InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf662LowerChecked :
    lowerCheck 24 leaf662Box leaf662Inputs = true := by
  rfl'

private theorem leaf662CoversExact : CoversExact 8
    leaf662Box leaf662Certificate leaf662InnerLog leaf662Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk39RoundedFacts chi89RoundedFacts
    innerPair274RoundedFacts leaf662RoundedFacts (by rfl)

private theorem leaf662FlatSound : Sound leaf662Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf662CertificateValid
    leaf662InnerLogValid leaf662CoversExact leaf662LowerChecked

private noncomputable def leaf663Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8), chiLo := (25/32), chiHi := (13/16) }

private noncomputable def leaf663Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554543/33554432) }, vSqrt := { lower := (16383/16384), upper := (34358231037/34356543488) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (81032255/67108864) }, upper := { exponent := 1, mantissa := (323/256) } }, logOuter := sk40LogOuterCertificate, logK := sk40LogKCertificate, logChi := chi89LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68714774525/68713086976) } }, logDArg := sk40LogDArgCertificate }

private noncomputable def leaf663InnerLog : WideLogData :=
  innerPair280Data

set_option maxRecDepth 1000000 in
private theorem leaf663LocalValidity :
    LeafFacts leaf663Box leaf663Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf663Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34358231037/34356543488) }) = true
      norm_num [leaf663Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf663CertificateValid :
    WideCertificateValid leaf663Box leaf663Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk40ValidityFacts chi89ValidityFacts
    leaf663LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf663CoverageChecked :
    coverageCheck (innerAD leaf663Box) leaf663InnerLog = true := by
  rfl'

private theorem leaf663InnerLogValid :
    leaf663InnerLog.Valid 8 (innerAD leaf663Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint90PositiveFacts.valid leaf663CoverageChecked

private noncomputable def leaf663InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629493/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf663InputLogOnePlusV_eq :
    leaf663InputLogOnePlusV = outerEnclosure 24
      (leaf663Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf663RoundedFacts : LeafRoundedFacts 8
    leaf663Certificate.logOnePlusV leaf663InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf663InputLogOnePlusV_eq }

private noncomputable def leaf663Inputs : Inputs :=
  inputsOfCaches globalInput sk40RoundedInputs
    chi89InputQChi innerPair280Input
    leaf663InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf663LowerChecked :
    lowerCheck 24 leaf663Box leaf663Inputs = true := by
  rfl'

private theorem leaf663CoversExact : CoversExact 8
    leaf663Box leaf663Certificate leaf663InnerLog leaf663Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk40RoundedFacts chi89RoundedFacts
    innerPair280RoundedFacts leaf663RoundedFacts (by rfl)

private theorem leaf663FlatSound : Sound leaf663Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf663CertificateValid
    leaf663InnerLogValid leaf663CoversExact leaf663LowerChecked

private noncomputable def leaf664Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16), chiLo := (13/16), chiHi := (7/8) }

private noncomputable def leaf664Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (16777301/16777216) }, vSqrt := { lower := (16383/16384), upper := (11452743679/11452137472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (40598013/33554432) }, upper := { exponent := 1, mantissa := (331/256) } }, logOuter := sk39LogOuterCertificate, logK := sk39LogKCertificate, logChi := chi77LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (22904881151/22904274944) } }, logDArg := sk39LogDArgCertificate }

private noncomputable def leaf664InnerLog : WideLogData :=
  innerPair281Data

set_option maxRecDepth 1000000 in
private theorem leaf664LocalValidity :
    LeafFacts leaf664Box leaf664Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf664Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (11452743679/11452137472) }) = true
      norm_num [leaf664Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf664CertificateValid :
    WideCertificateValid leaf664Box leaf664Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk39ValidityFacts chi77ValidityFacts
    leaf664LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf664CoverageChecked :
    coverageCheck (innerAD leaf664Box) leaf664InnerLog = true := by
  rfl'

private theorem leaf664InnerLogValid :
    leaf664InnerLog.Valid 8 (innerAD leaf664Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint91PositiveFacts.valid leaf664CoverageChecked

private noncomputable def leaf664InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629525/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf664InputLogOnePlusV_eq :
    leaf664InputLogOnePlusV = outerEnclosure 24
      (leaf664Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf664RoundedFacts : LeafRoundedFacts 8
    leaf664Certificate.logOnePlusV leaf664InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf664InputLogOnePlusV_eq }

private noncomputable def leaf664Inputs : Inputs :=
  inputsOfCaches globalInput sk39RoundedInputs
    chi77InputQChi innerPair281Input
    leaf664InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf664LowerChecked :
    lowerCheck 24 leaf664Box leaf664Inputs = true := by
  rfl'

private theorem leaf664CoversExact : CoversExact 8
    leaf664Box leaf664Certificate leaf664InnerLog leaf664Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk39RoundedFacts chi77RoundedFacts
    innerPair281RoundedFacts leaf664RoundedFacts (by rfl)

private theorem leaf664FlatSound : Sound leaf664Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf664CertificateValid
    leaf664InnerLogValid leaf664CoversExact leaf664LowerChecked

private noncomputable def leaf665Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8), chiLo := (13/16), chiHi := (7/8) }

private noncomputable def leaf665Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (16777303/16777216) }, vSqrt := { lower := (16383/16384), upper := (34358231037/34356297728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (41449927/33554432) }, upper := { exponent := 1, mantissa := (169/128) } }, logOuter := sk40LogOuterCertificate, logK := sk40LogKCertificate, logChi := chi77LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68714528765/68712595456) } }, logDArg := sk40LogDArgCertificate }

private noncomputable def leaf665InnerLog : WideLogData :=
  innerPair361Data

set_option maxRecDepth 1000000 in
private theorem leaf665LocalValidity :
    LeafFacts leaf665Box leaf665Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf665Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34358231037/34356297728) }) = true
      norm_num [leaf665Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf665CertificateValid :
    WideCertificateValid leaf665Box leaf665Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk40ValidityFacts chi77ValidityFacts
    leaf665LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf665CoverageChecked :
    coverageCheck (innerAD leaf665Box) leaf665InnerLog = true := by
  rfl'

private theorem leaf665InnerLogValid :
    leaf665InnerLog.Valid 8 (innerAD leaf665Box) :=
  wideLogDataValid_of_cachedCheck endpoint94PositiveFacts
    endpoint95PositiveFacts.valid leaf665CoverageChecked

private noncomputable def leaf665InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629553/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf665InputLogOnePlusV_eq :
    leaf665InputLogOnePlusV = outerEnclosure 24
      (leaf665Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf665RoundedFacts : LeafRoundedFacts 8
    leaf665Certificate.logOnePlusV leaf665InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf665InputLogOnePlusV_eq }

private noncomputable def leaf665Inputs : Inputs :=
  inputsOfCaches globalInput sk40RoundedInputs
    chi77InputQChi innerPair361Input
    leaf665InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf665LowerChecked :
    lowerCheck 24 leaf665Box leaf665Inputs = true := by
  rfl'

private theorem leaf665CoversExact : CoversExact 8
    leaf665Box leaf665Certificate leaf665InnerLog leaf665Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk40RoundedFacts chi77RoundedFacts
    innerPair361RoundedFacts leaf665RoundedFacts (by rfl)

private theorem leaf665FlatSound : Sound leaf665Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf665CertificateValid
    leaf665InnerLogValid leaf665CoversExact leaf665LowerChecked

private noncomputable def leaf666Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (3/4), chiHi := (25/32) }

private noncomputable def leaf666Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554543/33554432) }, vSqrt := { lower := (16383/16384), upper := (34358231037/34356563968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (80704595/67108864) }, upper := { exponent := 1, mantissa := (1287/1024) } }, logOuter := sk41LogOuterCertificate, logK := sk41LogKCertificate, logChi := chi88LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68714795005/68713127936) } }, logDArg := sk41LogDArgCertificate }

private noncomputable def leaf666InnerLog : WideLogData :=
  innerPair280Data

set_option maxRecDepth 1000000 in
private theorem leaf666LocalValidity :
    LeafFacts leaf666Box leaf666Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf666Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34358231037/34356563968) }) = true
      norm_num [leaf666Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf666CertificateValid :
    WideCertificateValid leaf666Box leaf666Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk41ValidityFacts chi88ValidityFacts
    leaf666LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf666CoverageChecked :
    coverageCheck (innerAD leaf666Box) leaf666InnerLog = true := by
  rfl'

private theorem leaf666InnerLogValid :
    leaf666InnerLog.Valid 8 (innerAD leaf666Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint90PositiveFacts.valid leaf666CoverageChecked

private noncomputable def leaf666InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (726843/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf666InputLogOnePlusV_eq :
    leaf666InputLogOnePlusV = outerEnclosure 24
      (leaf666Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf666RoundedFacts : LeafRoundedFacts 8
    leaf666Certificate.logOnePlusV leaf666InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf666InputLogOnePlusV_eq }

private noncomputable def leaf666Inputs : Inputs :=
  inputsOfCaches globalInput sk41RoundedInputs
    chi88InputQChi innerPair280Input
    leaf666InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf666LowerChecked :
    lowerCheck 24 leaf666Box leaf666Inputs = true := by
  rfl'

private theorem leaf666CoversExact : CoversExact 8
    leaf666Box leaf666Certificate leaf666InnerLog leaf666Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk41RoundedFacts chi88RoundedFacts
    innerPair280RoundedFacts leaf666RoundedFacts (by rfl)

private theorem leaf666FlatSound : Sound leaf666Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf666CertificateValid
    leaf666InnerLogValid leaf666CoversExact leaf666LowerChecked

private noncomputable def leaf667Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (3/4), chiHi := (25/32) }

private noncomputable def leaf667Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554545/33554432) }, vSqrt := { lower := (65531/65536), upper := (880980283/880934912) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (82277361/67108864) }, upper := { exponent := 1, mantissa := (41/32) } }, logOuter := sk42LogOuterCertificate, logK := sk42LogKCertificate, logChi := chi88LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (1761915195/1761869824) } }, logDArg := sk42LogDArgCertificate }

private noncomputable def leaf667InnerLog : WideLogData :=
  innerPair286Data

set_option maxRecDepth 1000000 in
private theorem leaf667LocalValidity :
    LeafFacts leaf667Box leaf667Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf667Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (880980283/880934912) }) = true
      norm_num [leaf667Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf667CertificateValid :
    WideCertificateValid leaf667Box leaf667Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk42ValidityFacts chi88ValidityFacts
    leaf667LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf667CoverageChecked :
    coverageCheck (innerAD leaf667Box) leaf667InnerLog = true := by
  rfl'

private theorem leaf667InnerLogValid :
    leaf667InnerLog.Valid 8 (innerAD leaf667Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint90PositiveFacts.valid leaf667CoverageChecked

private noncomputable def leaf667InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629513/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf667InputLogOnePlusV_eq :
    leaf667InputLogOnePlusV = outerEnclosure 24
      (leaf667Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf667RoundedFacts : LeafRoundedFacts 8
    leaf667Certificate.logOnePlusV leaf667InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf667InputLogOnePlusV_eq }

private noncomputable def leaf667Inputs : Inputs :=
  inputsOfCaches globalInput sk42RoundedInputs
    chi88InputQChi innerPair286Input
    leaf667InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf667LowerChecked :
    lowerCheck 24 leaf667Box leaf667Inputs = true := by
  rfl'

private theorem leaf667CoversExact : CoversExact 8
    leaf667Box leaf667Certificate leaf667InnerLog leaf667Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk42RoundedFacts chi88RoundedFacts
    innerPair286RoundedFacts leaf667RoundedFacts (by rfl)

private theorem leaf667FlatSound : Sound leaf667Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf667CertificateValid
    leaf667InnerLogValid leaf667CoversExact leaf667LowerChecked

private noncomputable def leaf668Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (25/32), chiHi := (13/16) }

private noncomputable def leaf668Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554545/33554432) }, vSqrt := { lower := (16383/16384), upper := (11452743679/11452145664) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (82670553/67108864) }, upper := { exponent := 1, mantissa := (659/512) } }, logOuter := sk41LogOuterCertificate, logK := sk41LogKCertificate, logChi := chi89LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (22904889343/22904291328) } }, logDArg := sk41LogDArgCertificate }

private noncomputable def leaf668InnerLog : WideLogData :=
  innerPair287Data

set_option maxRecDepth 1000000 in
private theorem leaf668LocalValidity :
    LeafFacts leaf668Box leaf668Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf668Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (11452743679/11452145664) }) = true
      norm_num [leaf668Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf668CertificateValid :
    WideCertificateValid leaf668Box leaf668Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk41ValidityFacts chi89ValidityFacts
    leaf668LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf668CoverageChecked :
    coverageCheck (innerAD leaf668Box) leaf668InnerLog = true := by
  rfl'

private theorem leaf668InnerLogValid :
    leaf668InnerLog.Valid 8 (innerAD leaf668Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint91PositiveFacts.valid leaf668CoverageChecked

private noncomputable def leaf668InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629519/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf668InputLogOnePlusV_eq :
    leaf668InputLogOnePlusV = outerEnclosure 24
      (leaf668Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf668RoundedFacts : LeafRoundedFacts 8
    leaf668Certificate.logOnePlusV leaf668InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf668InputLogOnePlusV_eq }

private noncomputable def leaf668Inputs : Inputs :=
  inputsOfCaches globalInput sk41RoundedInputs
    chi89InputQChi innerPair287Input
    leaf668InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf668LowerChecked :
    lowerCheck 24 leaf668Box leaf668Inputs = true := by
  rfl'

private theorem leaf668CoversExact : CoversExact 8
    leaf668Box leaf668Certificate leaf668InnerLog leaf668Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk41RoundedFacts chi89RoundedFacts
    innerPair287RoundedFacts leaf668RoundedFacts (by rfl)

private theorem leaf668FlatSound : Sound leaf668Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf668CertificateValid
    leaf668InnerLogValid leaf668CoversExact leaf668LowerChecked

private noncomputable def leaf669Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (25/32), chiHi := (13/16) }

private noncomputable def leaf669Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554547/33554432) }, vSqrt := { lower := (65531/65536), upper := (34358231037/34356330496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (84308851/67108864) }, upper := { exponent := 1, mantissa := (21/16) } }, logOuter := sk42LogOuterCertificate, logK := sk42LogKCertificate, logChi := chi89LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68714561533/68712660992) } }, logDArg := sk42LogDArgCertificate }

private noncomputable def leaf669InnerLog : WideLogData :=
  innerPair294Data

set_option maxRecDepth 1000000 in
private theorem leaf669LocalValidity :
    LeafFacts leaf669Box leaf669Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf669Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358231037/34356330496) }) = true
      norm_num [leaf669Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf669CertificateValid :
    WideCertificateValid leaf669Box leaf669Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk42ValidityFacts chi89ValidityFacts
    leaf669LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf669CoverageChecked :
    coverageCheck (innerAD leaf669Box) leaf669InnerLog = true := by
  rfl'

private theorem leaf669InnerLogValid :
    leaf669InnerLog.Valid 8 (innerAD leaf669Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint91PositiveFacts.valid leaf669CoverageChecked

private noncomputable def leaf669InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629545/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf669InputLogOnePlusV_eq :
    leaf669InputLogOnePlusV = outerEnclosure 24
      (leaf669Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf669RoundedFacts : LeafRoundedFacts 8
    leaf669Certificate.logOnePlusV leaf669InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf669InputLogOnePlusV_eq }

private noncomputable def leaf669Inputs : Inputs :=
  inputsOfCaches globalInput sk42RoundedInputs
    chi89InputQChi innerPair294Input
    leaf669InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf669LowerChecked :
    lowerCheck 24 leaf669Box leaf669Inputs = true := by
  rfl'

private theorem leaf669CoversExact : CoversExact 8
    leaf669Box leaf669Certificate leaf669InnerLog leaf669Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk42RoundedFacts chi89RoundedFacts
    innerPair294RoundedFacts leaf669RoundedFacts (by rfl)

private theorem leaf669FlatSound : Sound leaf669Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf669CertificateValid
    leaf669InnerLogValid leaf669CoversExact leaf669LowerChecked

private noncomputable def leaf670Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (13/16), chiHi := (27/32) }

private noncomputable def leaf670Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554547/33554432) }, vSqrt := { lower := (16383/16384), upper := (34358231037/34356310016) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (84636511/67108864) }, upper := { exponent := 1, mantissa := (1349/1024) } }, logOuter := sk41LogOuterCertificate, logK := sk41LogKCertificate, logChi := chi90LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68714541053/68712620032) } }, logDArg := sk41LogDArgCertificate }

private noncomputable def leaf670InnerLog : WideLogData :=
  innerPair295Data

set_option maxRecDepth 1000000 in
private theorem leaf670LocalValidity :
    LeafFacts leaf670Box leaf670Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf670Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34358231037/34356310016) }) = true
      norm_num [leaf670Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf670CertificateValid :
    WideCertificateValid leaf670Box leaf670Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk41ValidityFacts chi90ValidityFacts
    leaf670LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf670CoverageChecked :
    coverageCheck (innerAD leaf670Box) leaf670InnerLog = true := by
  rfl'

private theorem leaf670InnerLogValid :
    leaf670InnerLog.Valid 8 (innerAD leaf670Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint92PositiveFacts.valid leaf670CoverageChecked

private noncomputable def leaf670InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814775/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf670InputLogOnePlusV_eq :
    leaf670InputLogOnePlusV = outerEnclosure 24
      (leaf670Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf670RoundedFacts : LeafRoundedFacts 8
    leaf670Certificate.logOnePlusV leaf670InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf670InputLogOnePlusV_eq }

private noncomputable def leaf670Inputs : Inputs :=
  inputsOfCaches globalInput sk41RoundedInputs
    chi90InputQChi innerPair295Input
    leaf670InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf670LowerChecked :
    lowerCheck 24 leaf670Box leaf670Inputs = true := by
  rfl'

private theorem leaf670CoversExact : CoversExact 8
    leaf670Box leaf670Certificate leaf670InnerLog leaf670Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk41RoundedFacts chi90RoundedFacts
    innerPair295RoundedFacts leaf670RoundedFacts (by rfl)

private theorem leaf670FlatSound : Sound leaf670Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf670CertificateValid
    leaf670InnerLogValid leaf670CoversExact leaf670LowerChecked

private noncomputable def leaf671Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (13/16), chiHi := (27/32) }

private noncomputable def leaf671Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554549/33554432) }, vSqrt := { lower := (65531/65536), upper := (34358231037/34356199424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (86340341/67108864) }, upper := { exponent := 1, mantissa := (43/32) } }, logOuter := sk42LogOuterCertificate, logK := sk42LogKCertificate, logChi := chi90LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68714430461/68712398848) } }, logDArg := sk42LogDArgCertificate }

private noncomputable def leaf671InnerLog : WideLogData :=
  innerPair340Data

set_option maxRecDepth 1000000 in
private theorem leaf671LocalValidity :
    LeafFacts leaf671Box leaf671Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf671Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358231037/34356199424) }) = true
      norm_num [leaf671Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf671CertificateValid :
    WideCertificateValid leaf671Box leaf671Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk42ValidityFacts chi90ValidityFacts
    leaf671LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf671CoverageChecked :
    coverageCheck (innerAD leaf671Box) leaf671InnerLog = true := by
  rfl'

private theorem leaf671InnerLogValid :
    leaf671InnerLog.Valid 8 (innerAD leaf671Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint92PositiveFacts.valid leaf671CoverageChecked

private noncomputable def leaf671InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629577/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf671InputLogOnePlusV_eq :
    leaf671InputLogOnePlusV = outerEnclosure 24
      (leaf671Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf671RoundedFacts : LeafRoundedFacts 8
    leaf671Certificate.logOnePlusV leaf671InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf671InputLogOnePlusV_eq }

private noncomputable def leaf671Inputs : Inputs :=
  inputsOfCaches globalInput sk42RoundedInputs
    chi90InputQChi innerPair340Input
    leaf671InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf671LowerChecked :
    lowerCheck 24 leaf671Box leaf671Inputs = true := by
  rfl'

private theorem leaf671CoversExact : CoversExact 8
    leaf671Box leaf671Certificate leaf671InnerLog leaf671Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk42RoundedFacts chi90RoundedFacts
    innerPair340RoundedFacts leaf671RoundedFacts (by rfl)

private theorem leaf671FlatSound : Sound leaf671Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf671CertificateValid
    leaf671InnerLogValid leaf671CoversExact leaf671LowerChecked

private noncomputable def leaf672Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (27/32), chiHi := (7/8) }

private noncomputable def leaf672Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554549/33554432) }, vSqrt := { lower := (16383/16384), upper := (34358231037/34356183040) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (86602469/67108864) }, upper := { exponent := 1, mantissa := (345/256) } }, logOuter := sk41LogOuterCertificate, logK := sk41LogKCertificate, logChi := chi91LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68714414077/68712366080) } }, logDArg := sk41LogDArgCertificate }

private noncomputable def leaf672InnerLog : WideLogData :=
  innerPair341Data

set_option maxRecDepth 1000000 in
private theorem leaf672LocalValidity :
    LeafFacts leaf672Box leaf672Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf672Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34358231037/34356183040) }) = true
      norm_num [leaf672Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf672CertificateValid :
    WideCertificateValid leaf672Box leaf672Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk41ValidityFacts chi91ValidityFacts
    leaf672LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf672CoverageChecked :
    coverageCheck (innerAD leaf672Box) leaf672InnerLog = true := by
  rfl'

private theorem leaf672InnerLogValid :
    leaf672InnerLog.Valid 8 (innerAD leaf672Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint93PositiveFacts.valid leaf672CoverageChecked

private noncomputable def leaf672InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629581/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf672InputLogOnePlusV_eq :
    leaf672InputLogOnePlusV = outerEnclosure 24
      (leaf672Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf672RoundedFacts : LeafRoundedFacts 8
    leaf672Certificate.logOnePlusV leaf672InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf672InputLogOnePlusV_eq }

private noncomputable def leaf672Inputs : Inputs :=
  inputsOfCaches globalInput sk41RoundedInputs
    chi91InputQChi innerPair341Input
    leaf672InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf672LowerChecked :
    lowerCheck 24 leaf672Box leaf672Inputs = true := by
  rfl'

private theorem leaf672CoversExact : CoversExact 8
    leaf672Box leaf672Certificate leaf672InnerLog leaf672Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk41RoundedFacts chi91RoundedFacts
    innerPair341RoundedFacts leaf672RoundedFacts (by rfl)

private theorem leaf672FlatSound : Sound leaf672Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf672CertificateValid
    leaf672InnerLogValid leaf672CoversExact leaf672LowerChecked

private noncomputable def leaf673Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (27/32), chiHi := (7/8) }

private noncomputable def leaf673Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554551/33554432) }, vSqrt := { lower := (65531/65536), upper := (11452743679/11452022784) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (88371831/67108864) }, upper := { exponent := 1, mantissa := (11/8) } }, logOuter := sk42LogOuterCertificate, logK := sk42LogKCertificate, logChi := chi91LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (22904766463/22904045568) } }, logDArg := sk42LogDArgCertificate }

private noncomputable def leaf673InnerLog : WideLogData :=
  innerPair346Data

set_option maxRecDepth 1000000 in
private theorem leaf673LocalValidity :
    LeafFacts leaf673Box leaf673Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf673Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (11452743679/11452022784) }) = true
      norm_num [leaf673Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf673CertificateValid :
    WideCertificateValid leaf673Box leaf673Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk42ValidityFacts chi91ValidityFacts
    leaf673LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf673CoverageChecked :
    coverageCheck (innerAD leaf673Box) leaf673InnerLog = true := by
  rfl'

private theorem leaf673InnerLogValid :
    leaf673InnerLog.Valid 8 (innerAD leaf673Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint93PositiveFacts.valid leaf673CoverageChecked

private noncomputable def leaf673InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629609/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf673InputLogOnePlusV_eq :
    leaf673InputLogOnePlusV = outerEnclosure 24
      (leaf673Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf673RoundedFacts : LeafRoundedFacts 8
    leaf673Certificate.logOnePlusV leaf673InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf673InputLogOnePlusV_eq }

private noncomputable def leaf673Inputs : Inputs :=
  inputsOfCaches globalInput sk42RoundedInputs
    chi91InputQChi innerPair346Input
    leaf673InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf673LowerChecked :
    lowerCheck 24 leaf673Box leaf673Inputs = true := by
  rfl'

private theorem leaf673CoversExact : CoversExact 8
    leaf673Box leaf673Certificate leaf673InnerLog leaf673Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk42RoundedFacts chi91RoundedFacts
    innerPair346RoundedFacts leaf673RoundedFacts (by rfl)

private theorem leaf673FlatSound : Sound leaf673Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf673CertificateValid
    leaf673InnerLogValid leaf673CoversExact leaf673LowerChecked

private noncomputable def leaf674Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16), chiLo := (7/8), chiHi := (15/16) }

private noncomputable def leaf674Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (16777303/16777216) }, vSqrt := { lower := (16383/16384), upper := (34358231037/34356174848) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (42432907/33554432) }, upper := { exponent := 1, mantissa := (691/512) } }, logOuter := sk39LogOuterCertificate, logK := sk39LogKCertificate, logChi := chi78LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68714405885/68712349696) } }, logDArg := sk39LogDArgCertificate }

private noncomputable def leaf674InnerLog : WideLogData :=
  innerPair296Data

set_option maxRecDepth 1000000 in
private theorem leaf674LocalValidity :
    LeafFacts leaf674Box leaf674Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf674Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34358231037/34356174848) }) = true
      norm_num [leaf674Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf674CertificateValid :
    WideCertificateValid leaf674Box leaf674Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk39ValidityFacts chi78ValidityFacts
    leaf674LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf674CoverageChecked :
    coverageCheck (innerAD leaf674Box) leaf674InnerLog = true := by
  rfl'

private theorem leaf674InnerLogValid :
    leaf674InnerLog.Valid 8 (innerAD leaf674Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint93PositiveFacts.valid leaf674CoverageChecked

private noncomputable def leaf674InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629583/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf674InputLogOnePlusV_eq :
    leaf674InputLogOnePlusV = outerEnclosure 24
      (leaf674Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf674RoundedFacts : LeafRoundedFacts 8
    leaf674Certificate.logOnePlusV leaf674InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf674InputLogOnePlusV_eq }

private noncomputable def leaf674Inputs : Inputs :=
  inputsOfCaches globalInput sk39RoundedInputs
    chi78InputQChi innerPair296Input
    leaf674InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf674LowerChecked :
    lowerCheck 24 leaf674Box leaf674Inputs = true := by
  rfl'

private theorem leaf674CoversExact : CoversExact 8
    leaf674Box leaf674Certificate leaf674InnerLog leaf674Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk39RoundedFacts chi78RoundedFacts
    innerPair296RoundedFacts leaf674RoundedFacts (by rfl)

private theorem leaf674FlatSound : Sound leaf674Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf674CertificateValid
    leaf674InnerLogValid leaf674CoversExact leaf674LowerChecked

private noncomputable def leaf675Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8), chiLo := (7/8), chiHi := (15/16) }

private noncomputable def leaf675Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (16777305/16777216) }, vSqrt := { lower := (16383/16384), upper := (34358231037/34356051968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (43350353/33554432) }, upper := { exponent := 1, mantissa := (353/256) } }, logOuter := sk40LogOuterCertificate, logK := sk40LogKCertificate, logChi := chi78LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68714283005/68712103936) } }, logDArg := sk40LogDArgCertificate }

private noncomputable def leaf675InnerLog : WideLogData :=
  innerPair343Data

set_option maxRecDepth 1000000 in
private theorem leaf675LocalValidity :
    LeafFacts leaf675Box leaf675Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf675Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34358231037/34356051968) }) = true
      norm_num [leaf675Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf675CertificateValid :
    WideCertificateValid leaf675Box leaf675Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk40ValidityFacts chi78ValidityFacts
    leaf675LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf675CoverageChecked :
    coverageCheck (innerAD leaf675Box) leaf675InnerLog = true := by
  rfl'

private theorem leaf675InnerLogValid :
    leaf675InnerLog.Valid 8 (innerAD leaf675Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint96PositiveFacts.valid leaf675CoverageChecked

private noncomputable def leaf675InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629613/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf675InputLogOnePlusV_eq :
    leaf675InputLogOnePlusV = outerEnclosure 24
      (leaf675Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf675RoundedFacts : LeafRoundedFacts 8
    leaf675Certificate.logOnePlusV leaf675InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf675InputLogOnePlusV_eq }

private noncomputable def leaf675Inputs : Inputs :=
  inputsOfCaches globalInput sk40RoundedInputs
    chi78InputQChi innerPair343Input
    leaf675InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf675LowerChecked :
    lowerCheck 24 leaf675Box leaf675Inputs = true := by
  rfl'

private theorem leaf675CoversExact : CoversExact 8
    leaf675Box leaf675Certificate leaf675InnerLog leaf675Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk40RoundedFacts chi78RoundedFacts
    innerPair343RoundedFacts leaf675RoundedFacts (by rfl)

private theorem leaf675FlatSound : Sound leaf675Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf675CertificateValid
    leaf675InnerLogValid leaf675CoversExact leaf675LowerChecked

private noncomputable def leaf676Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16), chiLo := (15/16), chiHi := (1) }

private noncomputable def leaf676Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (16777305/16777216) }, vSqrt := { lower := (16383/16384), upper := (34358231037/34355937280) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (44267801/33554432) }, upper := { exponent := 1, mantissa := (45/32) } }, logOuter := sk39LogOuterCertificate, logK := sk39LogKCertificate, logChi := chi79LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68714168317/68711874560) } }, logDArg := sk39LogDArgCertificate }

private noncomputable def leaf676InnerLog : WideLogData :=
  innerPair347Data

set_option maxRecDepth 1000000 in
private theorem leaf676LocalValidity :
    LeafFacts leaf676Box leaf676Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf676Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34358231037/34355937280) }) = true
      norm_num [leaf676Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf676CertificateValid :
    WideCertificateValid leaf676Box leaf676Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk39ValidityFacts chi79ValidityFacts
    leaf676LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf676CoverageChecked :
    coverageCheck (innerAD leaf676Box) leaf676InnerLog = true := by
  rfl'

private theorem leaf676InnerLogValid :
    leaf676InnerLog.Valid 8 (innerAD leaf676Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint96PositiveFacts.valid leaf676CoverageChecked

private noncomputable def leaf676InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629641/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf676InputLogOnePlusV_eq :
    leaf676InputLogOnePlusV = outerEnclosure 24
      (leaf676Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf676RoundedFacts : LeafRoundedFacts 8
    leaf676Certificate.logOnePlusV leaf676InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf676InputLogOnePlusV_eq }

private noncomputable def leaf676Inputs : Inputs :=
  inputsOfCaches globalInput sk39RoundedInputs
    chi79InputQChi innerPair347Input
    leaf676InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf676LowerChecked :
    lowerCheck 24 leaf676Box leaf676Inputs = true := by
  rfl'

private theorem leaf676CoversExact : CoversExact 8
    leaf676Box leaf676Certificate leaf676InnerLog leaf676Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk39RoundedFacts chi79RoundedFacts
    innerPair347RoundedFacts leaf676RoundedFacts (by rfl)

private theorem leaf676FlatSound : Sound leaf676Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf676CertificateValid
    leaf676InnerLogValid leaf676CoversExact leaf676LowerChecked

private noncomputable def leaf677Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8), chiLo := (15/16), chiHi := (1) }

private noncomputable def leaf677Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (16777307/16777216) }, vSqrt := { lower := (16383/16384), upper := (34358231037/34355806208) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (45250779/33554432) }, upper := { exponent := 1, mantissa := (23/16) } }, logOuter := sk40LogOuterCertificate, logK := sk40LogKCertificate, logChi := chi79LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68714037245/68711612416) } }, logDArg := sk40LogDArgCertificate }

private noncomputable def leaf677InnerLog : WideLogData :=
  innerPair354Data

set_option maxRecDepth 1000000 in
private theorem leaf677LocalValidity :
    LeafFacts leaf677Box leaf677Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf677Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34358231037/34355806208) }) = true
      norm_num [leaf677Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf677CertificateValid :
    WideCertificateValid leaf677Box leaf677Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk40ValidityFacts chi79ValidityFacts
    leaf677LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf677CoverageChecked :
    coverageCheck (innerAD leaf677Box) leaf677InnerLog = true := by
  rfl'

private theorem leaf677InnerLogValid :
    leaf677InnerLog.Valid 8 (innerAD leaf677Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint97PositiveFacts.valid leaf677CoverageChecked

private noncomputable def leaf677InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629673/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf677InputLogOnePlusV_eq :
    leaf677InputLogOnePlusV = outerEnclosure 24
      (leaf677Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf677RoundedFacts : LeafRoundedFacts 8
    leaf677Certificate.logOnePlusV leaf677InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf677InputLogOnePlusV_eq }

private noncomputable def leaf677Inputs : Inputs :=
  inputsOfCaches globalInput sk40RoundedInputs
    chi79InputQChi innerPair354Input
    leaf677InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf677LowerChecked :
    lowerCheck 24 leaf677Box leaf677Inputs = true := by
  rfl'

private theorem leaf677CoversExact : CoversExact 8
    leaf677Box leaf677Certificate leaf677InnerLog leaf677Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk40RoundedFacts chi79RoundedFacts
    innerPair354RoundedFacts leaf677RoundedFacts (by rfl)

private theorem leaf677FlatSound : Sound leaf677Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf677CertificateValid
    leaf677InnerLogValid leaf677CoversExact leaf677LowerChecked

private noncomputable def leaf678Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (7/8), chiHi := (29/32) }

private noncomputable def leaf678Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554551/33554432) }, vSqrt := { lower := (16383/16384), upper := (11452743679/11452018688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (88568427/67108864) }, upper := { exponent := 1, mantissa := (1411/1024) } }, logOuter := sk41LogOuterCertificate, logK := sk41LogKCertificate, logChi := chi92LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (22904762367/22904037376) } }, logDArg := sk41LogDArgCertificate }

private noncomputable def leaf678InnerLog : WideLogData :=
  innerPair347Data

set_option maxRecDepth 1000000 in
private theorem leaf678LocalValidity :
    LeafFacts leaf678Box leaf678Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf678Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (11452743679/11452018688) }) = true
      norm_num [leaf678Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf678CertificateValid :
    WideCertificateValid leaf678Box leaf678Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk41ValidityFacts chi92ValidityFacts
    leaf678LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf678CoverageChecked :
    coverageCheck (innerAD leaf678Box) leaf678InnerLog = true := by
  rfl'

private theorem leaf678InnerLogValid :
    leaf678InnerLog.Valid 8 (innerAD leaf678Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint96PositiveFacts.valid leaf678CoverageChecked

private noncomputable def leaf678InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (2907403/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf678InputLogOnePlusV_eq :
    leaf678InputLogOnePlusV = outerEnclosure 24
      (leaf678Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf678RoundedFacts : LeafRoundedFacts 8
    leaf678Certificate.logOnePlusV leaf678InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf678InputLogOnePlusV_eq }

private noncomputable def leaf678Inputs : Inputs :=
  inputsOfCaches globalInput sk41RoundedInputs
    chi92InputQChi innerPair347Input
    leaf678InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf678LowerChecked :
    lowerCheck 24 leaf678Box leaf678Inputs = true := by
  rfl'

private theorem leaf678CoversExact : CoversExact 8
    leaf678Box leaf678Certificate leaf678InnerLog leaf678Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk41RoundedFacts chi92RoundedFacts
    innerPair347RoundedFacts leaf678RoundedFacts (by rfl)

private theorem leaf678FlatSound : Sound leaf678Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf678CertificateValid
    leaf678InnerLogValid leaf678CoversExact leaf678LowerChecked

private noncomputable def leaf679Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (7/8), chiHi := (29/32) }

private noncomputable def leaf679Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554553/33554432) }, vSqrt := { lower := (65531/65536), upper := (34358231037/34355937280) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (90403321/67108864) }, upper := { exponent := 1, mantissa := (45/32) } }, logOuter := sk42LogOuterCertificate, logK := sk42LogKCertificate, logChi := chi92LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68714168317/68711874560) } }, logDArg := sk42LogDArgCertificate }

private noncomputable def leaf679InnerLog : WideLogData :=
  innerPair353Data

set_option maxRecDepth 1000000 in
private theorem leaf679LocalValidity :
    LeafFacts leaf679Box leaf679Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf679Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358231037/34355937280) }) = true
      norm_num [leaf679Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf679CertificateValid :
    WideCertificateValid leaf679Box leaf679Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk42ValidityFacts chi92ValidityFacts
    leaf679LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf679CoverageChecked :
    coverageCheck (innerAD leaf679Box) leaf679InnerLog = true := by
  rfl'

private theorem leaf679InnerLogValid :
    leaf679InnerLog.Valid 8 (innerAD leaf679Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint96PositiveFacts.valid leaf679CoverageChecked

private noncomputable def leaf679InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629641/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf679InputLogOnePlusV_eq :
    leaf679InputLogOnePlusV = outerEnclosure 24
      (leaf679Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf679RoundedFacts : LeafRoundedFacts 8
    leaf679Certificate.logOnePlusV leaf679InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf679InputLogOnePlusV_eq }

private noncomputable def leaf679Inputs : Inputs :=
  inputsOfCaches globalInput sk42RoundedInputs
    chi92InputQChi innerPair353Input
    leaf679InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf679LowerChecked :
    lowerCheck 24 leaf679Box leaf679Inputs = true := by
  rfl'

private theorem leaf679CoversExact : CoversExact 8
    leaf679Box leaf679Certificate leaf679InnerLog leaf679Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk42RoundedFacts chi92RoundedFacts
    innerPair353RoundedFacts leaf679RoundedFacts (by rfl)

private theorem leaf679FlatSound : Sound leaf679Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf679CertificateValid
    leaf679InnerLogValid leaf679CoversExact leaf679LowerChecked

private noncomputable def leaf680Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (29/32), chiHi := (15/16) }

private noncomputable def leaf680Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554553/33554432) }, vSqrt := { lower := (16383/16384), upper := (2642940849/2642763776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (90534385/67108864) }, upper := { exponent := 1, mantissa := (721/512) } }, logOuter := sk41LogOuterCertificate, logK := sk41LogKCertificate, logChi := chi93LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (5285704625/5285527552) } }, logDArg := sk41LogDArgCertificate }

private noncomputable def leaf680InnerLog : WideLogData :=
  innerPair354Data

set_option maxRecDepth 1000000 in
private theorem leaf680LocalValidity :
    LeafFacts leaf680Box leaf680Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf680Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (2642940849/2642763776) }) = true
      norm_num [leaf680Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf680CertificateValid :
    WideCertificateValid leaf680Box leaf680Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk41ValidityFacts chi93ValidityFacts
    leaf680LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf680CoverageChecked :
    coverageCheck (innerAD leaf680Box) leaf680InnerLog = true := by
  rfl'

private theorem leaf680InnerLogValid :
    leaf680InnerLog.Valid 8 (innerAD leaf680Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint97PositiveFacts.valid leaf680CoverageChecked

private noncomputable def leaf680InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629643/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf680InputLogOnePlusV_eq :
    leaf680InputLogOnePlusV = outerEnclosure 24
      (leaf680Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf680RoundedFacts : LeafRoundedFacts 8
    leaf680Certificate.logOnePlusV leaf680InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf680InputLogOnePlusV_eq }

private noncomputable def leaf680Inputs : Inputs :=
  inputsOfCaches globalInput sk41RoundedInputs
    chi93InputQChi innerPair354Input
    leaf680InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf680LowerChecked :
    lowerCheck 24 leaf680Box leaf680Inputs = true := by
  rfl'

private theorem leaf680CoversExact : CoversExact 8
    leaf680Box leaf680Certificate leaf680InnerLog leaf680Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk41RoundedFacts chi93RoundedFacts
    innerPair354RoundedFacts leaf680RoundedFacts (by rfl)

private theorem leaf680FlatSound : Sound leaf680Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf680CertificateValid
    leaf680InnerLogValid leaf680CoversExact leaf680LowerChecked

private noncomputable def leaf681Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (29/32), chiHi := (15/16) }

private noncomputable def leaf681Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554555/33554432) }, vSqrt := { lower := (65531/65536), upper := (34358231037/34355806208) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (92434811/67108864) }, upper := { exponent := 1, mantissa := (23/16) } }, logOuter := sk42LogOuterCertificate, logK := sk42LogKCertificate, logChi := chi93LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68714037245/68711612416) } }, logDArg := sk42LogDArgCertificate }

private noncomputable def leaf681InnerLog : WideLogData :=
  innerPair357Data

set_option maxRecDepth 1000000 in
private theorem leaf681LocalValidity :
    LeafFacts leaf681Box leaf681Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf681Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358231037/34355806208) }) = true
      norm_num [leaf681Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf681CertificateValid :
    WideCertificateValid leaf681Box leaf681Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk42ValidityFacts chi93ValidityFacts
    leaf681LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf681CoverageChecked :
    coverageCheck (innerAD leaf681Box) leaf681InnerLog = true := by
  rfl'

private theorem leaf681InnerLogValid :
    leaf681InnerLog.Valid 8 (innerAD leaf681Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint97PositiveFacts.valid leaf681CoverageChecked

private noncomputable def leaf681InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629673/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf681InputLogOnePlusV_eq :
    leaf681InputLogOnePlusV = outerEnclosure 24
      (leaf681Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf681RoundedFacts : LeafRoundedFacts 8
    leaf681Certificate.logOnePlusV leaf681InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf681InputLogOnePlusV_eq }

private noncomputable def leaf681Inputs : Inputs :=
  inputsOfCaches globalInput sk42RoundedInputs
    chi93InputQChi innerPair357Input
    leaf681InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf681LowerChecked :
    lowerCheck 24 leaf681Box leaf681Inputs = true := by
  rfl'

private theorem leaf681CoversExact : CoversExact 8
    leaf681Box leaf681Certificate leaf681InnerLog leaf681Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk42RoundedFacts chi93RoundedFacts
    innerPair357RoundedFacts leaf681RoundedFacts (by rfl)

private theorem leaf681FlatSound : Sound leaf681Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf681CertificateValid
    leaf681InnerLogValid leaf681CoversExact leaf681LowerChecked

private noncomputable def leaf682Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (15/16), chiHi := (31/32) }

private noncomputable def leaf682Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554555/33554432) }, vSqrt := { lower := (16383/16384), upper := (34358231037/34355802112) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (92500343/67108864) }, upper := { exponent := 1, mantissa := (1473/1024) } }, logOuter := sk41LogOuterCertificate, logK := sk41LogKCertificate, logChi := chi94LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68714033149/68711604224) } }, logDArg := sk41LogDArgCertificate }

private noncomputable def leaf682InnerLog : WideLogData :=
  innerPair358Data

set_option maxRecDepth 1000000 in
private theorem leaf682LocalValidity :
    LeafFacts leaf682Box leaf682Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf682Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34358231037/34355802112) }) = true
      norm_num [leaf682Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf682CertificateValid :
    WideCertificateValid leaf682Box leaf682Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk41ValidityFacts chi94ValidityFacts
    leaf682LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf682CoverageChecked :
    coverageCheck (innerAD leaf682Box) leaf682InnerLog = true := by
  rfl'

private theorem leaf682InnerLogValid :
    leaf682InnerLog.Valid 8 (innerAD leaf682Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint98PositiveFacts.valid leaf682CoverageChecked

private noncomputable def leaf682InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814837/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf682InputLogOnePlusV_eq :
    leaf682InputLogOnePlusV = outerEnclosure 24
      (leaf682Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf682RoundedFacts : LeafRoundedFacts 8
    leaf682Certificate.logOnePlusV leaf682InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf682InputLogOnePlusV_eq }

private noncomputable def leaf682Inputs : Inputs :=
  inputsOfCaches globalInput sk41RoundedInputs
    chi94InputQChi innerPair358Input
    leaf682InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf682LowerChecked :
    lowerCheck 24 leaf682Box leaf682Inputs = true := by
  rfl'

private theorem leaf682CoversExact : CoversExact 8
    leaf682Box leaf682Certificate leaf682InnerLog leaf682Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk41RoundedFacts chi94RoundedFacts
    innerPair358RoundedFacts leaf682RoundedFacts (by rfl)

private theorem leaf682FlatSound : Sound leaf682Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf682CertificateValid
    leaf682InnerLogValid leaf682CoversExact leaf682LowerChecked

private noncomputable def leaf683Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (15/16), chiHi := (31/32) }

private noncomputable def leaf683Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554557/33554432) }, vSqrt := { lower := (65531/65536), upper := (11452743679/11451891712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (94466301/67108864) }, upper := { exponent := 1, mantissa := (47/32) } }, logOuter := sk42LogOuterCertificate, logK := sk42LogKCertificate, logChi := chi94LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (22904635391/22903783424) } }, logDArg := sk42LogDArgCertificate }

private noncomputable def leaf683InnerLog : WideLogData :=
  innerPair368Data

set_option maxRecDepth 1000000 in
private theorem leaf683LocalValidity :
    LeafFacts leaf683Box leaf683Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf683Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (11452743679/11451891712) }) = true
      norm_num [leaf683Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf683CertificateValid :
    WideCertificateValid leaf683Box leaf683Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk42ValidityFacts chi94ValidityFacts
    leaf683LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf683CoverageChecked :
    coverageCheck (innerAD leaf683Box) leaf683InnerLog = true := by
  rfl'

private theorem leaf683InnerLogValid :
    leaf683InnerLog.Valid 8 (innerAD leaf683Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint98PositiveFacts.valid leaf683CoverageChecked

private noncomputable def leaf683InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629705/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf683InputLogOnePlusV_eq :
    leaf683InputLogOnePlusV = outerEnclosure 24
      (leaf683Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf683RoundedFacts : LeafRoundedFacts 8
    leaf683Certificate.logOnePlusV leaf683InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf683InputLogOnePlusV_eq }

private noncomputable def leaf683Inputs : Inputs :=
  inputsOfCaches globalInput sk42RoundedInputs
    chi94InputQChi innerPair368Input
    leaf683InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf683LowerChecked :
    lowerCheck 24 leaf683Box leaf683Inputs = true := by
  rfl'

private theorem leaf683CoversExact : CoversExact 8
    leaf683Box leaf683Certificate leaf683InnerLog leaf683Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk42RoundedFacts chi94RoundedFacts
    innerPair368RoundedFacts leaf683RoundedFacts (by rfl)

private theorem leaf683FlatSound : Sound leaf683Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf683CertificateValid
    leaf683InnerLogValid leaf683CoversExact leaf683LowerChecked

private noncomputable def leaf684Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (31/32), chiHi := (1) }

private noncomputable def leaf684Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554557/33554432) }, vSqrt := { lower := (16383/16384), upper := (11452743679/11451891712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (94466301/67108864) }, upper := { exponent := 1, mantissa := (47/32) } }, logOuter := sk41LogOuterCertificate, logK := sk41LogKCertificate, logChi := chi95LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (22904635391/22903783424) } }, logDArg := sk41LogDArgCertificate }

private noncomputable def leaf684InnerLog : WideLogData :=
  innerPair368Data

set_option maxRecDepth 1000000 in
private theorem leaf684LocalValidity :
    LeafFacts leaf684Box leaf684Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf684Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (11452743679/11451891712) }) = true
      norm_num [leaf684Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf684CertificateValid :
    WideCertificateValid leaf684Box leaf684Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk41ValidityFacts chi95ValidityFacts
    leaf684LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf684CoverageChecked :
    coverageCheck (innerAD leaf684Box) leaf684InnerLog = true := by
  rfl'

private theorem leaf684InnerLogValid :
    leaf684InnerLog.Valid 8 (innerAD leaf684Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint98PositiveFacts.valid leaf684CoverageChecked

private noncomputable def leaf684InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629705/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf684InputLogOnePlusV_eq :
    leaf684InputLogOnePlusV = outerEnclosure 24
      (leaf684Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf684RoundedFacts : LeafRoundedFacts 8
    leaf684Certificate.logOnePlusV leaf684InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf684InputLogOnePlusV_eq }

private noncomputable def leaf684Inputs : Inputs :=
  inputsOfCaches globalInput sk41RoundedInputs
    chi95InputQChi innerPair368Input
    leaf684InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf684LowerChecked :
    lowerCheck 24 leaf684Box leaf684Inputs = true := by
  rfl'

private theorem leaf684CoversExact : CoversExact 8
    leaf684Box leaf684Certificate leaf684InnerLog leaf684Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk41RoundedFacts chi95RoundedFacts
    innerPair368RoundedFacts leaf684RoundedFacts (by rfl)

private theorem leaf684FlatSound : Sound leaf684Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf684CertificateValid
    leaf684InnerLogValid leaf684CoversExact leaf684LowerChecked

private noncomputable def leaf685Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (31/32), chiHi := (1) }

private noncomputable def leaf685Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554559/33554432) }, vSqrt := { lower := (65531/65536), upper := (8589426687/8588886016) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (96497791/67108864) }, upper := { exponent := 1, mantissa := (3/2) } }, logOuter := sk42LogOuterCertificate, logK := sk42LogKCertificate, logChi := chi95LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (17178312703/17177772032) } }, logDArg := sk42LogDArgCertificate }

private noncomputable def leaf685InnerLog : WideLogData :=
  innerPair372Data

set_option maxRecDepth 1000000 in
private theorem leaf685LocalValidity :
    LeafFacts leaf685Box leaf685Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf685Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (8589426687/8588886016) }) = true
      norm_num [leaf685Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf685CertificateValid :
    WideCertificateValid leaf685Box leaf685Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk42ValidityFacts chi95ValidityFacts
    leaf685LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf685CoverageChecked :
    coverageCheck (innerAD leaf685Box) leaf685InnerLog = true := by
  rfl'

private theorem leaf685InnerLogValid :
    leaf685InnerLog.Valid 8 (innerAD leaf685Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint99PositiveFacts.valid leaf685CoverageChecked

private noncomputable def leaf685InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629609/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf685InputLogOnePlusV_eq :
    leaf685InputLogOnePlusV = outerEnclosure 24
      (leaf685Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf685RoundedFacts : LeafRoundedFacts 8
    leaf685Certificate.logOnePlusV leaf685InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf685InputLogOnePlusV_eq }

private noncomputable def leaf685Inputs : Inputs :=
  inputsOfCaches globalInput sk42RoundedInputs
    chi95InputQChi innerPair372Input
    leaf685InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf685LowerChecked :
    lowerCheck 24 leaf685Box leaf685Inputs = true := by
  rfl'

private theorem leaf685CoversExact : CoversExact 8
    leaf685Box leaf685Certificate leaf685InnerLog leaf685Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk42RoundedFacts chi95RoundedFacts
    innerPair372RoundedFacts leaf685RoundedFacts (by rfl)

private theorem leaf685FlatSound : Sound leaf685Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf685CertificateValid
    leaf685InnerLogValid leaf685CoversExact leaf685LowerChecked

private noncomputable def component16Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (13/8), chiLo := (3/4), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component16Node0_sound : Sound component16Node0Box :=
  sound_of_literal_split component16Node0Box leaf644Box leaf645Box
    .k (25/16) (by rfl) (by rfl)
    leaf644FlatSound leaf645FlatSound

private noncomputable def component16Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (13/8), chiLo := (13/16), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component16Node1_sound : Sound component16Node1Box :=
  sound_of_literal_split component16Node1Box leaf646Box leaf647Box
    .k (25/16) (by rfl) (by rfl)
    leaf646FlatSound leaf647FlatSound

private noncomputable def component16Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (13/8), chiLo := (3/4), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component16Node2_sound : Sound component16Node2Box :=
  sound_of_literal_split component16Node2Box component16Node0Box component16Node1Box
    .chi (13/16) (by rfl) (by rfl)
    component16Node0_sound component16Node1_sound

private noncomputable def component16Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (7/4), chiLo := (3/4), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component16Node3_sound : Sound component16Node3Box :=
  sound_of_literal_split component16Node3Box leaf648Box leaf649Box
    .k (27/16) (by rfl) (by rfl)
    leaf648FlatSound leaf649FlatSound

private noncomputable def component16Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (7/4), chiLo := (13/16), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component16Node4_sound : Sound component16Node4Box :=
  sound_of_literal_split component16Node4Box leaf650Box leaf651Box
    .k (27/16) (by rfl) (by rfl)
    leaf650FlatSound leaf651FlatSound

private noncomputable def component16Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (7/4), chiLo := (3/4), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component16Node5_sound : Sound component16Node5Box :=
  sound_of_literal_split component16Node5Box component16Node3Box component16Node4Box
    .chi (13/16) (by rfl) (by rfl)
    component16Node3_sound component16Node4_sound

private noncomputable def component16Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (7/4), chiLo := (3/4), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component16Node6_sound : Sound component16Node6Box :=
  sound_of_literal_split component16Node6Box component16Node2Box component16Node5Box
    .k (13/8) (by rfl) (by rfl)
    component16Node2_sound component16Node5_sound

private noncomputable def component16Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (13/8), chiLo := (7/8), chiHi := (15/16) }

set_option maxRecDepth 1000000 in
private theorem component16Node7_sound : Sound component16Node7Box :=
  sound_of_literal_split component16Node7Box leaf652Box leaf653Box
    .k (25/16) (by rfl) (by rfl)
    leaf652FlatSound leaf653FlatSound

private noncomputable def component16Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (13/8), chiLo := (15/16), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component16Node8_sound : Sound component16Node8Box :=
  sound_of_literal_split component16Node8Box leaf654Box leaf655Box
    .k (25/16) (by rfl) (by rfl)
    leaf654FlatSound leaf655FlatSound

private noncomputable def component16Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (13/8), chiLo := (7/8), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component16Node9_sound : Sound component16Node9Box :=
  sound_of_literal_split component16Node9Box component16Node7Box component16Node8Box
    .chi (15/16) (by rfl) (by rfl)
    component16Node7_sound component16Node8_sound

private noncomputable def component16Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (7/4), chiLo := (7/8), chiHi := (15/16) }

set_option maxRecDepth 1000000 in
private theorem component16Node10_sound : Sound component16Node10Box :=
  sound_of_literal_split component16Node10Box leaf656Box leaf657Box
    .k (27/16) (by rfl) (by rfl)
    leaf656FlatSound leaf657FlatSound

private noncomputable def component16Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (7/4), chiLo := (15/16), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component16Node11_sound : Sound component16Node11Box :=
  sound_of_literal_split component16Node11Box leaf658Box leaf659Box
    .k (27/16) (by rfl) (by rfl)
    leaf658FlatSound leaf659FlatSound

private noncomputable def component16Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (7/4), chiLo := (7/8), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component16Node12_sound : Sound component16Node12Box :=
  sound_of_literal_split component16Node12Box component16Node10Box component16Node11Box
    .chi (15/16) (by rfl) (by rfl)
    component16Node10_sound component16Node11_sound

private noncomputable def component16Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (7/4), chiLo := (7/8), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component16Node13_sound : Sound component16Node13Box :=
  sound_of_literal_split component16Node13Box component16Node9Box component16Node12Box
    .k (13/8) (by rfl) (by rfl)
    component16Node9_sound component16Node12_sound

private noncomputable def component16Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (7/4), chiLo := (3/4), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component16Node14_sound : Sound component16Node14Box :=
  sound_of_literal_split component16Node14Box component16Node6Box component16Node13Box
    .chi (7/8) (by rfl) (by rfl)
    component16Node6_sound component16Node13_sound

private noncomputable def component16Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (15/8), chiLo := (3/4), chiHi := (25/32) }

set_option maxRecDepth 1000000 in
private theorem component16Node15_sound : Sound component16Node15Box :=
  sound_of_literal_split component16Node15Box leaf660Box leaf661Box
    .k (29/16) (by rfl) (by rfl)
    leaf660FlatSound leaf661FlatSound

private noncomputable def component16Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (15/8), chiLo := (25/32), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component16Node16_sound : Sound component16Node16Box :=
  sound_of_literal_split component16Node16Box leaf662Box leaf663Box
    .k (29/16) (by rfl) (by rfl)
    leaf662FlatSound leaf663FlatSound

private noncomputable def component16Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (15/8), chiLo := (3/4), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component16Node17_sound : Sound component16Node17Box :=
  sound_of_literal_split component16Node17Box component16Node15Box component16Node16Box
    .chi (25/32) (by rfl) (by rfl)
    component16Node15_sound component16Node16_sound

private noncomputable def component16Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (15/8), chiLo := (13/16), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component16Node18_sound : Sound component16Node18Box :=
  sound_of_literal_split component16Node18Box leaf664Box leaf665Box
    .k (29/16) (by rfl) (by rfl)
    leaf664FlatSound leaf665FlatSound

private noncomputable def component16Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (15/8), chiLo := (3/4), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component16Node19_sound : Sound component16Node19Box :=
  sound_of_literal_split component16Node19Box component16Node17Box component16Node18Box
    .chi (13/16) (by rfl) (by rfl)
    component16Node17_sound component16Node18_sound

private noncomputable def component16Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (3/4), chiHi := (25/32) }

set_option maxRecDepth 1000000 in
private theorem component16Node20_sound : Sound component16Node20Box :=
  sound_of_literal_split component16Node20Box leaf666Box leaf667Box
    .k (31/16) (by rfl) (by rfl)
    leaf666FlatSound leaf667FlatSound

private noncomputable def component16Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (25/32), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component16Node21_sound : Sound component16Node21Box :=
  sound_of_literal_split component16Node21Box leaf668Box leaf669Box
    .k (31/16) (by rfl) (by rfl)
    leaf668FlatSound leaf669FlatSound

private noncomputable def component16Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (3/4), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component16Node22_sound : Sound component16Node22Box :=
  sound_of_literal_split component16Node22Box component16Node20Box component16Node21Box
    .chi (25/32) (by rfl) (by rfl)
    component16Node20_sound component16Node21_sound

private noncomputable def component16Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (13/16), chiHi := (27/32) }

set_option maxRecDepth 1000000 in
private theorem component16Node23_sound : Sound component16Node23Box :=
  sound_of_literal_split component16Node23Box leaf670Box leaf671Box
    .k (31/16) (by rfl) (by rfl)
    leaf670FlatSound leaf671FlatSound

private noncomputable def component16Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (27/32), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component16Node24_sound : Sound component16Node24Box :=
  sound_of_literal_split component16Node24Box leaf672Box leaf673Box
    .k (31/16) (by rfl) (by rfl)
    leaf672FlatSound leaf673FlatSound

private noncomputable def component16Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (13/16), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component16Node25_sound : Sound component16Node25Box :=
  sound_of_literal_split component16Node25Box component16Node23Box component16Node24Box
    .chi (27/32) (by rfl) (by rfl)
    component16Node23_sound component16Node24_sound

private noncomputable def component16Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (3/4), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component16Node26_sound : Sound component16Node26Box :=
  sound_of_literal_split component16Node26Box component16Node22Box component16Node25Box
    .chi (13/16) (by rfl) (by rfl)
    component16Node22_sound component16Node25_sound

private noncomputable def component16Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (2), chiLo := (3/4), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component16Node27_sound : Sound component16Node27Box :=
  sound_of_literal_split component16Node27Box component16Node19Box component16Node26Box
    .k (15/8) (by rfl) (by rfl)
    component16Node19_sound component16Node26_sound

private noncomputable def component16Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (15/8), chiLo := (7/8), chiHi := (15/16) }

set_option maxRecDepth 1000000 in
private theorem component16Node28_sound : Sound component16Node28Box :=
  sound_of_literal_split component16Node28Box leaf674Box leaf675Box
    .k (29/16) (by rfl) (by rfl)
    leaf674FlatSound leaf675FlatSound

private noncomputable def component16Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (15/8), chiLo := (15/16), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component16Node29_sound : Sound component16Node29Box :=
  sound_of_literal_split component16Node29Box leaf676Box leaf677Box
    .k (29/16) (by rfl) (by rfl)
    leaf676FlatSound leaf677FlatSound

private noncomputable def component16Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (15/8), chiLo := (7/8), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component16Node30_sound : Sound component16Node30Box :=
  sound_of_literal_split component16Node30Box component16Node28Box component16Node29Box
    .chi (15/16) (by rfl) (by rfl)
    component16Node28_sound component16Node29_sound

private noncomputable def component16Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (7/8), chiHi := (29/32) }

set_option maxRecDepth 1000000 in
private theorem component16Node31_sound : Sound component16Node31Box :=
  sound_of_literal_split component16Node31Box leaf678Box leaf679Box
    .k (31/16) (by rfl) (by rfl)
    leaf678FlatSound leaf679FlatSound

private noncomputable def component16Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (29/32), chiHi := (15/16) }

set_option maxRecDepth 1000000 in
private theorem component16Node32_sound : Sound component16Node32Box :=
  sound_of_literal_split component16Node32Box leaf680Box leaf681Box
    .k (31/16) (by rfl) (by rfl)
    leaf680FlatSound leaf681FlatSound

private noncomputable def component16Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (7/8), chiHi := (15/16) }

set_option maxRecDepth 1000000 in
private theorem component16Node33_sound : Sound component16Node33Box :=
  sound_of_literal_split component16Node33Box component16Node31Box component16Node32Box
    .chi (29/32) (by rfl) (by rfl)
    component16Node31_sound component16Node32_sound

private noncomputable def component16Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (15/16), chiHi := (31/32) }

set_option maxRecDepth 1000000 in
private theorem component16Node34_sound : Sound component16Node34Box :=
  sound_of_literal_split component16Node34Box leaf682Box leaf683Box
    .k (31/16) (by rfl) (by rfl)
    leaf682FlatSound leaf683FlatSound

private noncomputable def component16Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (31/32), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component16Node35_sound : Sound component16Node35Box :=
  sound_of_literal_split component16Node35Box leaf684Box leaf685Box
    .k (31/16) (by rfl) (by rfl)
    leaf684FlatSound leaf685FlatSound

private noncomputable def component16Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (15/16), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component16Node36_sound : Sound component16Node36Box :=
  sound_of_literal_split component16Node36Box component16Node34Box component16Node35Box
    .chi (31/32) (by rfl) (by rfl)
    component16Node34_sound component16Node35_sound

private noncomputable def component16Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (7/8), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component16Node37_sound : Sound component16Node37Box :=
  sound_of_literal_split component16Node37Box component16Node33Box component16Node36Box
    .chi (15/16) (by rfl) (by rfl)
    component16Node33_sound component16Node36_sound

private noncomputable def component16Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (2), chiLo := (7/8), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component16Node38_sound : Sound component16Node38Box :=
  sound_of_literal_split component16Node38Box component16Node30Box component16Node37Box
    .k (15/8) (by rfl) (by rfl)
    component16Node30_sound component16Node37_sound

private noncomputable def component16Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (2), chiLo := (3/4), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component16Node39_sound : Sound component16Node39Box :=
  sound_of_literal_split component16Node39Box component16Node27Box component16Node38Box
    .chi (7/8) (by rfl) (by rfl)
    component16Node27_sound component16Node38_sound

noncomputable def component16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (2), chiLo := (3/4), chiHi := (1) }

set_option maxRecDepth 1000000 in
theorem component16_sound : Sound component16Box :=
  sound_of_literal_split component16Box component16Node14Box component16Node39Box
    .k (7/4) (by rfl) (by rfl)
    component16Node14_sound component16Node39_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
