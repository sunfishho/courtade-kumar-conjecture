import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch6
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch7
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

private noncomputable def leaf3963Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (1/4), chiHi := (33/128) }

private noncomputable def leaf3963Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435699/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716469248) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (452940559/268435456) }, upper := { exponent := 0, mantissa := (7033/4096) } }, logOuter := sk107LogOuterCertificate, logK := sk107LogKCertificate, logChi := chi241LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434962943/137432938496) } }, logDArg := sk107LogDArgCertificate }

private noncomputable def leaf3963InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf3963LocalValidity :
    LeafFacts leaf3963Box leaf3963Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3963Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716469248) }) = true
      norm_num [leaf3963Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3963CertificateValid :
    WideCertificateValid leaf3963Box leaf3963Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk107ValidityFacts chi241ValidityFacts
    leaf3963LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3963CoverageChecked :
    coverageCheck (innerAD leaf3963Box) leaf3963InnerLog = true := by
  rfl'

private theorem leaf3963InnerLogValid :
    leaf3963InnerLog.Valid 8 (innerAD leaf3963Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf3963CoverageChecked

private noncomputable def leaf3963InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (726833/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf3963InputLogOnePlusV_eq :
    leaf3963InputLogOnePlusV = outerEnclosure 24
      (leaf3963Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3963RoundedFacts : LeafRoundedFacts 8
    leaf3963Certificate.logOnePlusV leaf3963InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3963InputLogOnePlusV_eq }

private noncomputable def leaf3963Inputs : Inputs :=
  inputsOfCaches globalInput sk107RoundedInputs
    chi241InputQChi innerPair57Input
    leaf3963InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3963LowerChecked :
    lowerCheck 24 leaf3963Box leaf3963Inputs = true := by
  rfl'

private theorem leaf3963CoversExact : CoversExact 8
    leaf3963Box leaf3963Certificate leaf3963InnerLog leaf3963Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk107RoundedFacts chi241RoundedFacts
    innerPair57RoundedFacts leaf3963RoundedFacts (by rfl)

private theorem leaf3963FlatSound : Sound leaf3963Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3963CertificateValid
    leaf3963InnerLogValid leaf3963CoversExact leaf3963LowerChecked

private noncomputable def leaf3964Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (33/128), chiHi := (17/64) }

private noncomputable def leaf3964Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435701/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716378112) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (458707373/268435456) }, upper := { exponent := 0, mantissa := (3561/2048) } }, logOuter := sk107LogOuterCertificate, logK := sk107LogKCertificate, logChi := chi242LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434871807/137432756224) } }, logDArg := sk107LogDArgCertificate }

private noncomputable def leaf3964InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3964LocalValidity :
    LeafFacts leaf3964Box leaf3964Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3964Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716378112) }) = true
      norm_num [leaf3964Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3964CertificateValid :
    WideCertificateValid leaf3964Box leaf3964Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk107ValidityFacts chi242ValidityFacts
    leaf3964LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3964CoverageChecked :
    coverageCheck (innerAD leaf3964Box) leaf3964InnerLog = true := by
  rfl'

private theorem leaf3964InnerLogValid :
    leaf3964InnerLog.Valid 8 (innerAD leaf3964Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3964CoverageChecked

private noncomputable def leaf3964InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629339/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3964InputLogOnePlusV_eq :
    leaf3964InputLogOnePlusV = outerEnclosure 24
      (leaf3964Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3964RoundedFacts : LeafRoundedFacts 8
    leaf3964Certificate.logOnePlusV leaf3964InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3964InputLogOnePlusV_eq }

private noncomputable def leaf3964Inputs : Inputs :=
  inputsOfCaches globalInput sk107RoundedInputs
    chi242InputQChi innerPair64Input
    leaf3964InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3964LowerChecked :
    lowerCheck 24 leaf3964Box leaf3964Inputs = true := by
  rfl'

private theorem leaf3964CoversExact : CoversExact 8
    leaf3964Box leaf3964Certificate leaf3964InnerLog leaf3964Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk107RoundedFacts chi242RoundedFacts
    innerPair64RoundedFacts leaf3964RoundedFacts (by rfl)

private theorem leaf3964FlatSound : Sound leaf3964Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3964CertificateValid
    leaf3964InnerLogValid leaf3964CoversExact leaf3964LowerChecked

private noncomputable def leaf3965Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (1/4), chiHi := (33/128) }

private noncomputable def leaf3965Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435701/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716435456) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (455037581/268435456) }, upper := { exponent := 0, mantissa := (3533/2048) } }, logOuter := sk108LogOuterCertificate, logK := sk108LogKCertificate, logChi := chi241LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434929151/137432870912) } }, logDArg := sk108LogDArgCertificate }

private noncomputable def leaf3965InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3965LocalValidity :
    LeafFacts leaf3965Box leaf3965Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3965Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716435456) }) = true
      norm_num [leaf3965Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3965CertificateValid :
    WideCertificateValid leaf3965Box leaf3965Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk108ValidityFacts chi241ValidityFacts
    leaf3965LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3965CoverageChecked :
    coverageCheck (innerAD leaf3965Box) leaf3965InnerLog = true := by
  rfl'

private theorem leaf3965InnerLogValid :
    leaf3965InnerLog.Valid 8 (innerAD leaf3965Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3965CoverageChecked

private noncomputable def leaf3965InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907333/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3965InputLogOnePlusV_eq :
    leaf3965InputLogOnePlusV = outerEnclosure 24
      (leaf3965Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3965RoundedFacts : LeafRoundedFacts 8
    leaf3965Certificate.logOnePlusV leaf3965InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3965InputLogOnePlusV_eq }

private noncomputable def leaf3965Inputs : Inputs :=
  inputsOfCaches globalInput sk108RoundedInputs
    chi241InputQChi innerPair64Input
    leaf3965InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3965LowerChecked :
    lowerCheck 24 leaf3965Box leaf3965Inputs = true := by
  rfl'

private theorem leaf3965CoversExact : CoversExact 8
    leaf3965Box leaf3965Certificate leaf3965InnerLog leaf3965Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk108RoundedFacts chi241RoundedFacts
    innerPair64RoundedFacts leaf3965RoundedFacts (by rfl)

private theorem leaf3965FlatSound : Sound leaf3965Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3965CertificateValid
    leaf3965InnerLogValid leaf3965CoversExact leaf3965LowerChecked

private noncomputable def leaf3966Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (33/128), chiHi := (17/64) }

private noncomputable def leaf3966Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435703/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716343296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (460869927/268435456) }, upper := { exponent := 0, mantissa := (1789/1024) } }, logOuter := sk108LogOuterCertificate, logK := sk108LogKCertificate, logChi := chi242LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434836991/137432686592) } }, logDArg := sk108LogDArgCertificate }

private noncomputable def leaf3966InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3966LocalValidity :
    LeafFacts leaf3966Box leaf3966Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3966Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716343296) }) = true
      norm_num [leaf3966Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3966CertificateValid :
    WideCertificateValid leaf3966Box leaf3966Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk108ValidityFacts chi242ValidityFacts
    leaf3966LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3966CoverageChecked :
    coverageCheck (innerAD leaf3966Box) leaf3966InnerLog = true := by
  rfl'

private theorem leaf3966InnerLogValid :
    leaf3966InnerLog.Valid 8 (innerAD leaf3966Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3966CoverageChecked

private noncomputable def leaf3966InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629343/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3966InputLogOnePlusV_eq :
    leaf3966InputLogOnePlusV = outerEnclosure 24
      (leaf3966Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3966RoundedFacts : LeafRoundedFacts 8
    leaf3966Certificate.logOnePlusV leaf3966InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3966InputLogOnePlusV_eq }

private noncomputable def leaf3966Inputs : Inputs :=
  inputsOfCaches globalInput sk108RoundedInputs
    chi242InputQChi innerPair64Input
    leaf3966InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3966LowerChecked :
    lowerCheck 24 leaf3966Box leaf3966Inputs = true := by
  rfl'

private theorem leaf3966CoversExact : CoversExact 8
    leaf3966Box leaf3966Certificate leaf3966InnerLog leaf3966Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk108RoundedFacts chi242RoundedFacts
    innerPair64RoundedFacts leaf3966RoundedFacts (by rfl)

private theorem leaf3966FlatSound : Sound leaf3966Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3966CertificateValid
    leaf3966InnerLogValid leaf3966CoversExact leaf3966LowerChecked

private noncomputable def leaf3967Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (17/64), chiHi := (35/128) }

private noncomputable def leaf3967Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435703/268435456) }, vSqrt := { lower := (32765/32768), upper := (1347421445/1347378176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (464474187/268435456) }, upper := { exponent := 0, mantissa := (7211/4096) } }, logOuter := sk107LogOuterCertificate, logK := sk107LogKCertificate, logChi := chi243LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (2694799621/2694756352) } }, logDArg := sk107LogDArgCertificate }

private noncomputable def leaf3967InnerLog : WideLogData :=
  innerPair204Data

set_option maxRecDepth 1000000 in
private theorem leaf3967LocalValidity :
    LeafFacts leaf3967Box leaf3967Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3967Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (1347421445/1347378176) }) = true
      norm_num [leaf3967Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3967CertificateValid :
    WideCertificateValid leaf3967Box leaf3967Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk107ValidityFacts chi243ValidityFacts
    leaf3967LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3967CoverageChecked :
    coverageCheck (innerAD leaf3967Box) leaf3967InnerLog = true := by
  rfl'

private theorem leaf3967InnerLogValid :
    leaf3967InnerLog.Valid 8 (innerAD leaf3967Box) :=
  wideLogDataValid_of_cachedCheck endpoint62PositiveFacts
    endpoint63PositiveFacts.valid leaf3967CoverageChecked

private noncomputable def leaf3967InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814675/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3967InputLogOnePlusV_eq :
    leaf3967InputLogOnePlusV = outerEnclosure 24
      (leaf3967Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3967RoundedFacts : LeafRoundedFacts 8
    leaf3967Certificate.logOnePlusV leaf3967InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3967InputLogOnePlusV_eq }

private noncomputable def leaf3967Inputs : Inputs :=
  inputsOfCaches globalInput sk107RoundedInputs
    chi243InputQChi innerPair204Input
    leaf3967InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3967LowerChecked :
    lowerCheck 24 leaf3967Box leaf3967Inputs = true := by
  rfl'

private theorem leaf3967CoversExact : CoversExact 8
    leaf3967Box leaf3967Certificate leaf3967InnerLog leaf3967Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk107RoundedFacts chi243RoundedFacts
    innerPair204RoundedFacts leaf3967RoundedFacts (by rfl)

private theorem leaf3967FlatSound : Sound leaf3967Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3967CertificateValid
    leaf3967InnerLogValid leaf3967CoversExact leaf3967LowerChecked

private noncomputable def leaf3968Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (35/128), chiHi := (9/32) }

private noncomputable def leaf3968Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435705/268435456) }, vSqrt := { lower := (32765/32768), upper := (13743698739/13743239168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (470241001/268435456) }, upper := { exponent := 0, mantissa := (1825/1024) } }, logOuter := sk107LogOuterCertificate, logK := sk107LogKCertificate, logChi := chi244LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (27486937907/27486478336) } }, logDArg := sk107LogDArgCertificate }

private noncomputable def leaf3968InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3968LocalValidity :
    LeafFacts leaf3968Box leaf3968Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3968Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (13743698739/13743239168) }) = true
      norm_num [leaf3968Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3968CertificateValid :
    WideCertificateValid leaf3968Box leaf3968Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk107ValidityFacts chi244ValidityFacts
    leaf3968LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3968CoverageChecked :
    coverageCheck (innerAD leaf3968Box) leaf3968InnerLog = true := by
  rfl'

private theorem leaf3968InnerLogValid :
    leaf3968InnerLog.Valid 8 (innerAD leaf3968Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3968CoverageChecked

private noncomputable def leaf3968InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629361/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3968InputLogOnePlusV_eq :
    leaf3968InputLogOnePlusV = outerEnclosure 24
      (leaf3968Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3968RoundedFacts : LeafRoundedFacts 8
    leaf3968Certificate.logOnePlusV leaf3968InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3968InputLogOnePlusV_eq }

private noncomputable def leaf3968Inputs : Inputs :=
  inputsOfCaches globalInput sk107RoundedInputs
    chi244InputQChi innerPair71Input
    leaf3968InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3968LowerChecked :
    lowerCheck 24 leaf3968Box leaf3968Inputs = true := by
  rfl'

private theorem leaf3968CoversExact : CoversExact 8
    leaf3968Box leaf3968Certificate leaf3968InnerLog leaf3968Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk107RoundedFacts chi244RoundedFacts
    innerPair71RoundedFacts leaf3968RoundedFacts (by rfl)

private theorem leaf3968FlatSound : Sound leaf3968Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3968CertificateValid
    leaf3968InnerLogValid leaf3968CoversExact leaf3968LowerChecked

private noncomputable def leaf3969Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (17/64), chiHi := (35/128) }

private noncomputable def leaf3969Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435705/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716251136) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (466702273/268435456) }, upper := { exponent := 0, mantissa := (3623/2048) } }, logOuter := sk108LogOuterCertificate, logK := sk108LogKCertificate, logChi := chi243LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434744831/137432502272) } }, logDArg := sk108LogDArgCertificate }

private noncomputable def leaf3969InnerLog : WideLogData :=
  innerPair431Data

set_option maxRecDepth 1000000 in
private theorem leaf3969LocalValidity :
    LeafFacts leaf3969Box leaf3969Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3969Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716251136) }) = true
      norm_num [leaf3969Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3969CertificateValid :
    WideCertificateValid leaf3969Box leaf3969Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk108ValidityFacts chi243ValidityFacts
    leaf3969LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3969CoverageChecked :
    coverageCheck (innerAD leaf3969Box) leaf3969InnerLog = true := by
  rfl'

private theorem leaf3969InnerLogValid :
    leaf3969InnerLog.Valid 8 (innerAD leaf3969Box) :=
  wideLogDataValid_of_cachedCheck endpoint139PositiveFacts
    endpoint68PositiveFacts.valid leaf3969CoverageChecked

private noncomputable def leaf3969InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629355/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3969InputLogOnePlusV_eq :
    leaf3969InputLogOnePlusV = outerEnclosure 24
      (leaf3969Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3969RoundedFacts : LeafRoundedFacts 8
    leaf3969Certificate.logOnePlusV leaf3969InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3969InputLogOnePlusV_eq }

private noncomputable def leaf3969Inputs : Inputs :=
  inputsOfCaches globalInput sk108RoundedInputs
    chi243InputQChi innerPair431Input
    leaf3969InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3969LowerChecked :
    lowerCheck 24 leaf3969Box leaf3969Inputs = true := by
  rfl'

private theorem leaf3969CoversExact : CoversExact 8
    leaf3969Box leaf3969Certificate leaf3969InnerLog leaf3969Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk108RoundedFacts chi243RoundedFacts
    innerPair431RoundedFacts leaf3969RoundedFacts (by rfl)

private theorem leaf3969FlatSound : Sound leaf3969Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3969CertificateValid
    leaf3969InnerLogValid leaf3969CoversExact leaf3969LowerChecked

private noncomputable def leaf3970Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (35/128), chiHi := (9/32) }

private noncomputable def leaf3970Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435707/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716158976) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (472534619/268435456) }, upper := { exponent := 0, mantissa := (917/512) } }, logOuter := sk108LogOuterCertificate, logK := sk108LogKCertificate, logChi := chi244LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434652671/137432317952) } }, logDArg := sk108LogDArgCertificate }

private noncomputable def leaf3970InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3970LocalValidity :
    LeafFacts leaf3970Box leaf3970Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3970Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716158976) }) = true
      norm_num [leaf3970Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3970CertificateValid :
    WideCertificateValid leaf3970Box leaf3970Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk108ValidityFacts chi244ValidityFacts
    leaf3970LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3970CoverageChecked :
    coverageCheck (innerAD leaf3970Box) leaf3970InnerLog = true := by
  rfl'

private theorem leaf3970InnerLogValid :
    leaf3970InnerLog.Valid 8 (innerAD leaf3970Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3970CoverageChecked

private noncomputable def leaf3970InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814683/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3970InputLogOnePlusV_eq :
    leaf3970InputLogOnePlusV = outerEnclosure 24
      (leaf3970Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3970RoundedFacts : LeafRoundedFacts 8
    leaf3970Certificate.logOnePlusV leaf3970InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3970InputLogOnePlusV_eq }

private noncomputable def leaf3970Inputs : Inputs :=
  inputsOfCaches globalInput sk108RoundedInputs
    chi244InputQChi innerPair71Input
    leaf3970InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3970LowerChecked :
    lowerCheck 24 leaf3970Box leaf3970Inputs = true := by
  rfl'

private theorem leaf3970CoversExact : CoversExact 8
    leaf3970Box leaf3970Certificate leaf3970InnerLog leaf3970Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk108RoundedFacts chi244RoundedFacts
    innerPair71RoundedFacts leaf3970RoundedFacts (by rfl)

private theorem leaf3970FlatSound : Sound leaf3970Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3970CertificateValid
    leaf3970InnerLogValid leaf3970CoversExact leaf3970LowerChecked

private noncomputable def leaf3971Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32), chiLo := (1/4), chiHi := (33/128) }

private noncomputable def leaf3971Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435703/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716401664) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (457134603/268435456) }, upper := { exponent := 0, mantissa := (7099/4096) } }, logOuter := sk109LogOuterCertificate, logK := sk109LogKCertificate, logChi := chi241LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434895359/137432803328) } }, logDArg := sk109LogDArgCertificate }

private noncomputable def leaf3971InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3971LocalValidity :
    LeafFacts leaf3971Box leaf3971Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3971Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716401664) }) = true
      norm_num [leaf3971Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3971CertificateValid :
    WideCertificateValid leaf3971Box leaf3971Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk109ValidityFacts chi241ValidityFacts
    leaf3971LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3971CoverageChecked :
    coverageCheck (innerAD leaf3971Box) leaf3971InnerLog = true := by
  rfl'

private theorem leaf3971InnerLogValid :
    leaf3971InnerLog.Valid 8 (innerAD leaf3971Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3971CoverageChecked

private noncomputable def leaf3971InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453667/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3971InputLogOnePlusV_eq :
    leaf3971InputLogOnePlusV = outerEnclosure 24
      (leaf3971Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3971RoundedFacts : LeafRoundedFacts 8
    leaf3971Certificate.logOnePlusV leaf3971InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3971InputLogOnePlusV_eq }

private noncomputable def leaf3971Inputs : Inputs :=
  inputsOfCaches globalInput sk109RoundedInputs
    chi241InputQChi innerPair64Input
    leaf3971InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3971LowerChecked :
    lowerCheck 24 leaf3971Box leaf3971Inputs = true := by
  rfl'

private theorem leaf3971CoversExact : CoversExact 8
    leaf3971Box leaf3971Certificate leaf3971InnerLog leaf3971Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk109RoundedFacts chi241RoundedFacts
    innerPair64RoundedFacts leaf3971RoundedFacts (by rfl)

private theorem leaf3971FlatSound : Sound leaf3971Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3971CertificateValid
    leaf3971InnerLogValid leaf3971CoversExact leaf3971LowerChecked

private noncomputable def leaf3972Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32), chiLo := (33/128), chiHi := (17/64) }

private noncomputable def leaf3972Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435705/268435456) }, vSqrt := { lower := (32765/32768), upper := (4581232913/4581087232) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (463032481/268435456) }, upper := { exponent := 0, mantissa := (3595/2048) } }, logOuter := sk109LogOuterCertificate, logK := sk109LogKCertificate, logChi := chi242LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (9162320145/9162174464) } }, logDArg := sk109LogDArgCertificate }

private noncomputable def leaf3972InnerLog : WideLogData :=
  innerPair204Data

set_option maxRecDepth 1000000 in
private theorem leaf3972LocalValidity :
    LeafFacts leaf3972Box leaf3972Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3972Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4581232913/4581087232) }) = true
      norm_num [leaf3972Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3972CertificateValid :
    WideCertificateValid leaf3972Box leaf3972Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk109ValidityFacts chi242ValidityFacts
    leaf3972LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3972CoverageChecked :
    coverageCheck (innerAD leaf3972Box) leaf3972InnerLog = true := by
  rfl'

private theorem leaf3972InnerLogValid :
    leaf3972InnerLog.Valid 8 (innerAD leaf3972Box) :=
  wideLogDataValid_of_cachedCheck endpoint62PositiveFacts
    endpoint63PositiveFacts.valid leaf3972CoverageChecked

private noncomputable def leaf3972InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907337/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3972InputLogOnePlusV_eq :
    leaf3972InputLogOnePlusV = outerEnclosure 24
      (leaf3972Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3972RoundedFacts : LeafRoundedFacts 8
    leaf3972Certificate.logOnePlusV leaf3972InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3972InputLogOnePlusV_eq }

private noncomputable def leaf3972Inputs : Inputs :=
  inputsOfCaches globalInput sk109RoundedInputs
    chi242InputQChi innerPair204Input
    leaf3972InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3972LowerChecked :
    lowerCheck 24 leaf3972Box leaf3972Inputs = true := by
  rfl'

private theorem leaf3972CoversExact : CoversExact 8
    leaf3972Box leaf3972Certificate leaf3972InnerLog leaf3972Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk109RoundedFacts chi242RoundedFacts
    innerPair204RoundedFacts leaf3972RoundedFacts (by rfl)

private theorem leaf3972FlatSound : Sound leaf3972Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3972CertificateValid
    leaf3972InnerLogValid leaf3972CoversExact leaf3972LowerChecked

private noncomputable def leaf3973Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8), chiLo := (1/4), chiHi := (33/128) }

private noncomputable def leaf3973Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435705/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716367872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (459231625/268435456) }, upper := { exponent := 0, mantissa := (1783/1024) } }, logOuter := sk110LogOuterCertificate, logK := sk110LogKCertificate, logChi := chi241LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434861567/137432735744) } }, logDArg := sk110LogDArgCertificate }

private noncomputable def leaf3973InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3973LocalValidity :
    LeafFacts leaf3973Box leaf3973Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3973Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716367872) }) = true
      norm_num [leaf3973Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3973CertificateValid :
    WideCertificateValid leaf3973Box leaf3973Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk110ValidityFacts chi241ValidityFacts
    leaf3973LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3973CoverageChecked :
    coverageCheck (innerAD leaf3973Box) leaf3973InnerLog = true := by
  rfl'

private theorem leaf3973InnerLogValid :
    leaf3973InnerLog.Valid 8 (innerAD leaf3973Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3973CoverageChecked

private noncomputable def leaf3973InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907335/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3973InputLogOnePlusV_eq :
    leaf3973InputLogOnePlusV = outerEnclosure 24
      (leaf3973Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3973RoundedFacts : LeafRoundedFacts 8
    leaf3973Certificate.logOnePlusV leaf3973InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3973InputLogOnePlusV_eq }

private noncomputable def leaf3973Inputs : Inputs :=
  inputsOfCaches globalInput sk110RoundedInputs
    chi241InputQChi innerPair64Input
    leaf3973InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3973LowerChecked :
    lowerCheck 24 leaf3973Box leaf3973Inputs = true := by
  rfl'

private theorem leaf3973CoversExact : CoversExact 8
    leaf3973Box leaf3973Certificate leaf3973InnerLog leaf3973Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk110RoundedFacts chi241RoundedFacts
    innerPair64RoundedFacts leaf3973RoundedFacts (by rfl)

private theorem leaf3973FlatSound : Sound leaf3973Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3973CertificateValid
    leaf3973InnerLogValid leaf3973CoversExact leaf3973LowerChecked

private noncomputable def leaf3974Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8), chiLo := (33/128), chiHi := (17/64) }

private noncomputable def leaf3974Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435707/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716273664) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (465195035/268435456) }, upper := { exponent := 0, mantissa := (903/512) } }, logOuter := sk110LogOuterCertificate, logK := sk110LogKCertificate, logChi := chi242LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434767359/137432547328) } }, logDArg := sk110LogDArgCertificate }

private noncomputable def leaf3974InnerLog : WideLogData :=
  innerPair204Data

set_option maxRecDepth 1000000 in
private theorem leaf3974LocalValidity :
    LeafFacts leaf3974Box leaf3974Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3974Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716273664) }) = true
      norm_num [leaf3974Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3974CertificateValid :
    WideCertificateValid leaf3974Box leaf3974Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk110ValidityFacts chi242ValidityFacts
    leaf3974LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3974CoverageChecked :
    coverageCheck (innerAD leaf3974Box) leaf3974InnerLog = true := by
  rfl'

private theorem leaf3974InnerLogValid :
    leaf3974InnerLog.Valid 8 (innerAD leaf3974Box) :=
  wideLogDataValid_of_cachedCheck endpoint62PositiveFacts
    endpoint63PositiveFacts.valid leaf3974CoverageChecked

private noncomputable def leaf3974InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453669/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3974InputLogOnePlusV_eq :
    leaf3974InputLogOnePlusV = outerEnclosure 24
      (leaf3974Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3974RoundedFacts : LeafRoundedFacts 8
    leaf3974Certificate.logOnePlusV leaf3974InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3974InputLogOnePlusV_eq }

private noncomputable def leaf3974Inputs : Inputs :=
  inputsOfCaches globalInput sk110RoundedInputs
    chi242InputQChi innerPair204Input
    leaf3974InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3974LowerChecked :
    lowerCheck 24 leaf3974Box leaf3974Inputs = true := by
  rfl'

private theorem leaf3974CoversExact : CoversExact 8
    leaf3974Box leaf3974Certificate leaf3974InnerLog leaf3974Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk110RoundedFacts chi242RoundedFacts
    innerPair204RoundedFacts leaf3974RoundedFacts (by rfl)

private theorem leaf3974FlatSound : Sound leaf3974Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3974CertificateValid
    leaf3974InnerLogValid leaf3974CoversExact leaf3974LowerChecked

private noncomputable def leaf3975Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32), chiLo := (17/64), chiHi := (35/128) }

private noncomputable def leaf3975Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435707/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716215296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (468930359/268435456) }, upper := { exponent := 0, mantissa := (7281/4096) } }, logOuter := sk109LogOuterCertificate, logK := sk109LogKCertificate, logChi := chi243LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434708991/137432430592) } }, logDArg := sk109LogDArgCertificate }

private noncomputable def leaf3975InnerLog : WideLogData :=
  innerPair431Data

set_option maxRecDepth 1000000 in
private theorem leaf3975LocalValidity :
    LeafFacts leaf3975Box leaf3975Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3975Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716215296) }) = true
      norm_num [leaf3975Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3975CertificateValid :
    WideCertificateValid leaf3975Box leaf3975Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk109ValidityFacts chi243ValidityFacts
    leaf3975LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3975CoverageChecked :
    coverageCheck (innerAD leaf3975Box) leaf3975InnerLog = true := by
  rfl'

private theorem leaf3975InnerLogValid :
    leaf3975InnerLog.Valid 8 (innerAD leaf3975Box) :=
  wideLogDataValid_of_cachedCheck endpoint139PositiveFacts
    endpoint68PositiveFacts.valid leaf3975CoverageChecked

private noncomputable def leaf3975InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629359/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3975InputLogOnePlusV_eq :
    leaf3975InputLogOnePlusV = outerEnclosure 24
      (leaf3975Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3975RoundedFacts : LeafRoundedFacts 8
    leaf3975Certificate.logOnePlusV leaf3975InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3975InputLogOnePlusV_eq }

private noncomputable def leaf3975Inputs : Inputs :=
  inputsOfCaches globalInput sk109RoundedInputs
    chi243InputQChi innerPair431Input
    leaf3975InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3975LowerChecked :
    lowerCheck 24 leaf3975Box leaf3975Inputs = true := by
  rfl'

private theorem leaf3975CoversExact : CoversExact 8
    leaf3975Box leaf3975Certificate leaf3975InnerLog leaf3975Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk109RoundedFacts chi243RoundedFacts
    innerPair431RoundedFacts leaf3975RoundedFacts (by rfl)

private theorem leaf3975FlatSound : Sound leaf3975Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3975CertificateValid
    leaf3975InnerLogValid leaf3975CoversExact leaf3975LowerChecked

private noncomputable def leaf3976Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32), chiLo := (35/128), chiHi := (9/32) }

private noncomputable def leaf3976Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435709/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716122112) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (474828237/268435456) }, upper := { exponent := 0, mantissa := (1843/1024) } }, logOuter := sk109LogOuterCertificate, logK := sk109LogKCertificate, logChi := chi244LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434615807/137432244224) } }, logDArg := sk109LogDArgCertificate }

private noncomputable def leaf3976InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3976LocalValidity :
    LeafFacts leaf3976Box leaf3976Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3976Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716122112) }) = true
      norm_num [leaf3976Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3976CertificateValid :
    WideCertificateValid leaf3976Box leaf3976Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk109ValidityFacts chi244ValidityFacts
    leaf3976LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3976CoverageChecked :
    coverageCheck (innerAD leaf3976Box) leaf3976InnerLog = true := by
  rfl'

private theorem leaf3976InnerLogValid :
    leaf3976InnerLog.Valid 8 (innerAD leaf3976Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3976CoverageChecked

private noncomputable def leaf3976InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814685/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3976InputLogOnePlusV_eq :
    leaf3976InputLogOnePlusV = outerEnclosure 24
      (leaf3976Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3976RoundedFacts : LeafRoundedFacts 8
    leaf3976Certificate.logOnePlusV leaf3976InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3976InputLogOnePlusV_eq }

private noncomputable def leaf3976Inputs : Inputs :=
  inputsOfCaches globalInput sk109RoundedInputs
    chi244InputQChi innerPair71Input
    leaf3976InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3976LowerChecked :
    lowerCheck 24 leaf3976Box leaf3976Inputs = true := by
  rfl'

private theorem leaf3976CoversExact : CoversExact 8
    leaf3976Box leaf3976Certificate leaf3976InnerLog leaf3976Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk109RoundedFacts chi244RoundedFacts
    innerPair71RoundedFacts leaf3976RoundedFacts (by rfl)

private theorem leaf3976FlatSound : Sound leaf3976Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3976CertificateValid
    leaf3976InnerLogValid leaf3976CoversExact leaf3976LowerChecked

private noncomputable def leaf3977Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8), chiLo := (17/64), chiHi := (35/128) }

private noncomputable def leaf3977Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435709/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905393152) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (471158445/268435456) }, upper := { exponent := 0, mantissa := (1829/1024) } }, logOuter := sk110LogOuterCertificate, logK := sk110LogKCertificate, logChi := chi243LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811557717/45810786304) } }, logDArg := sk110LogDArgCertificate }

private noncomputable def leaf3977InnerLog : WideLogData :=
  innerPair77Data

set_option maxRecDepth 1000000 in
private theorem leaf3977LocalValidity :
    LeafFacts leaf3977Box leaf3977Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3977Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905393152) }) = true
      norm_num [leaf3977Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3977CertificateValid :
    WideCertificateValid leaf3977Box leaf3977Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk110ValidityFacts chi243ValidityFacts
    leaf3977LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3977CoverageChecked :
    coverageCheck (innerAD leaf3977Box) leaf3977InnerLog = true := by
  rfl'

private theorem leaf3977InnerLogValid :
    leaf3977InnerLog.Valid 8 (innerAD leaf3977Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint67PositiveFacts.valid leaf3977CoverageChecked

private noncomputable def leaf3977InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629363/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3977InputLogOnePlusV_eq :
    leaf3977InputLogOnePlusV = outerEnclosure 24
      (leaf3977Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3977RoundedFacts : LeafRoundedFacts 8
    leaf3977Certificate.logOnePlusV leaf3977InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3977InputLogOnePlusV_eq }

private noncomputable def leaf3977Inputs : Inputs :=
  inputsOfCaches globalInput sk110RoundedInputs
    chi243InputQChi innerPair77Input
    leaf3977InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3977LowerChecked :
    lowerCheck 24 leaf3977Box leaf3977Inputs = true := by
  rfl'

private theorem leaf3977CoversExact : CoversExact 8
    leaf3977Box leaf3977Certificate leaf3977InnerLog leaf3977Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk110RoundedFacts chi243RoundedFacts
    innerPair77RoundedFacts leaf3977RoundedFacts (by rfl)

private theorem leaf3977FlatSound : Sound leaf3977Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3977CertificateValid
    leaf3977InnerLogValid leaf3977CoversExact leaf3977LowerChecked

private noncomputable def leaf3978Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8), chiLo := (35/128), chiHi := (9/32) }

private noncomputable def leaf3978Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435711/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716085248) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (477121855/268435456) }, upper := { exponent := 0, mantissa := (463/256) } }, logOuter := sk110LogOuterCertificate, logK := sk110LogKCertificate, logChi := chi244LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434578943/137432170496) } }, logDArg := sk110LogDArgCertificate }

private noncomputable def leaf3978InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3978LocalValidity :
    LeafFacts leaf3978Box leaf3978Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3978Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716085248) }) = true
      norm_num [leaf3978Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3978CertificateValid :
    WideCertificateValid leaf3978Box leaf3978Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk110ValidityFacts chi244ValidityFacts
    leaf3978LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3978CoverageChecked :
    coverageCheck (innerAD leaf3978Box) leaf3978InnerLog = true := by
  rfl'

private theorem leaf3978InnerLogValid :
    leaf3978InnerLog.Valid 8 (innerAD leaf3978Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3978CoverageChecked

private noncomputable def leaf3978InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629375/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3978InputLogOnePlusV_eq :
    leaf3978InputLogOnePlusV = outerEnclosure 24
      (leaf3978Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3978RoundedFacts : LeafRoundedFacts 8
    leaf3978Certificate.logOnePlusV leaf3978InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3978InputLogOnePlusV_eq }

private noncomputable def leaf3978Inputs : Inputs :=
  inputsOfCaches globalInput sk110RoundedInputs
    chi244InputQChi innerPair71Input
    leaf3978InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3978LowerChecked :
    lowerCheck 24 leaf3978Box leaf3978Inputs = true := by
  rfl'

private theorem leaf3978CoversExact : CoversExact 8
    leaf3978Box leaf3978Certificate leaf3978InnerLog leaf3978Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk110RoundedFacts chi244RoundedFacts
    innerPair71RoundedFacts leaf3978RoundedFacts (by rfl)

private theorem leaf3978FlatSound : Sound leaf3978Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3978CertificateValid
    leaf3978InnerLogValid leaf3978CoversExact leaf3978LowerChecked

private noncomputable def leaf3979Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (9/32), chiHi := (37/128) }

private noncomputable def leaf3979Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435707/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716104704) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (476007815/268435456) }, upper := { exponent := 0, mantissa := (7389/4096) } }, logOuter := sk107LogOuterCertificate, logK := sk107LogKCertificate, logChi := chi245LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434598399/137432209408) } }, logDArg := sk107LogDArgCertificate }

private noncomputable def leaf3979InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3979LocalValidity :
    LeafFacts leaf3979Box leaf3979Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3979Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716104704) }) = true
      norm_num [leaf3979Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3979CertificateValid :
    WideCertificateValid leaf3979Box leaf3979Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk107ValidityFacts chi245ValidityFacts
    leaf3979LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3979CoverageChecked :
    coverageCheck (innerAD leaf3979Box) leaf3979InnerLog = true := by
  rfl'

private theorem leaf3979InnerLogValid :
    leaf3979InnerLog.Valid 8 (innerAD leaf3979Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3979CoverageChecked

private noncomputable def leaf3979InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907343/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3979InputLogOnePlusV_eq :
    leaf3979InputLogOnePlusV = outerEnclosure 24
      (leaf3979Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3979RoundedFacts : LeafRoundedFacts 8
    leaf3979Certificate.logOnePlusV leaf3979InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3979InputLogOnePlusV_eq }

private noncomputable def leaf3979Inputs : Inputs :=
  inputsOfCaches globalInput sk107RoundedInputs
    chi245InputQChi innerPair71Input
    leaf3979InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3979LowerChecked :
    lowerCheck 24 leaf3979Box leaf3979Inputs = true := by
  rfl'

private theorem leaf3979CoversExact : CoversExact 8
    leaf3979Box leaf3979Certificate leaf3979InnerLog leaf3979Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk107RoundedFacts chi245RoundedFacts
    innerPair71RoundedFacts leaf3979RoundedFacts (by rfl)

private theorem leaf3979FlatSound : Sound leaf3979Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3979CertificateValid
    leaf3979InnerLogValid leaf3979CoversExact leaf3979LowerChecked

private noncomputable def leaf3980Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (37/128), chiHi := (19/64) }

private noncomputable def leaf3980Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435709/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905337856) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (481774629/268435456) }, upper := { exponent := 0, mantissa := (3739/2048) } }, logOuter := sk107LogOuterCertificate, logK := sk107LogKCertificate, logChi := chi246LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811502421/45810675712) } }, logDArg := sk107LogDArgCertificate }

private noncomputable def leaf3980InnerLog : WideLogData :=
  innerPair226Data

set_option maxRecDepth 1000000 in
private theorem leaf3980LocalValidity :
    LeafFacts leaf3980Box leaf3980Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3980Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905337856) }) = true
      norm_num [leaf3980Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3980CertificateValid :
    WideCertificateValid leaf3980Box leaf3980Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk107ValidityFacts chi246ValidityFacts
    leaf3980LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3980CoverageChecked :
    coverageCheck (innerAD leaf3980Box) leaf3980InnerLog = true := by
  rfl'

private theorem leaf3980InnerLogValid :
    leaf3980InnerLog.Valid 8 (innerAD leaf3980Box) :=
  wideLogDataValid_of_cachedCheck endpoint68PositiveFacts
    endpoint64PositiveFacts.valid leaf3980CoverageChecked

private noncomputable def leaf3980InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453673/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3980InputLogOnePlusV_eq :
    leaf3980InputLogOnePlusV = outerEnclosure 24
      (leaf3980Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3980RoundedFacts : LeafRoundedFacts 8
    leaf3980Certificate.logOnePlusV leaf3980InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3980InputLogOnePlusV_eq }

private noncomputable def leaf3980Inputs : Inputs :=
  inputsOfCaches globalInput sk107RoundedInputs
    chi246InputQChi innerPair226Input
    leaf3980InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3980LowerChecked :
    lowerCheck 24 leaf3980Box leaf3980Inputs = true := by
  rfl'

private theorem leaf3980CoversExact : CoversExact 8
    leaf3980Box leaf3980Certificate leaf3980InnerLog leaf3980Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk107RoundedFacts chi246RoundedFacts
    innerPair226RoundedFacts leaf3980RoundedFacts (by rfl)

private theorem leaf3980FlatSound : Sound leaf3980Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3980CertificateValid
    leaf3980InnerLogValid leaf3980CoversExact leaf3980LowerChecked

private noncomputable def leaf3981Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (9/32), chiHi := (37/128) }

private noncomputable def leaf3981Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435709/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716066816) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (478366965/268435456) }, upper := { exponent := 0, mantissa := (3713/2048) } }, logOuter := sk108LogOuterCertificate, logK := sk108LogKCertificate, logChi := chi245LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434560511/137432133632) } }, logDArg := sk108LogDArgCertificate }

private noncomputable def leaf3981InnerLog : WideLogData :=
  innerPair226Data

set_option maxRecDepth 1000000 in
private theorem leaf3981LocalValidity :
    LeafFacts leaf3981Box leaf3981Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3981Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716066816) }) = true
      norm_num [leaf3981Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3981CertificateValid :
    WideCertificateValid leaf3981Box leaf3981Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk108ValidityFacts chi245ValidityFacts
    leaf3981LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3981CoverageChecked :
    coverageCheck (innerAD leaf3981Box) leaf3981InnerLog = true := by
  rfl'

private theorem leaf3981InnerLogValid :
    leaf3981InnerLog.Valid 8 (innerAD leaf3981Box) :=
  wideLogDataValid_of_cachedCheck endpoint68PositiveFacts
    endpoint64PositiveFacts.valid leaf3981CoverageChecked

private noncomputable def leaf3981InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629377/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3981InputLogOnePlusV_eq :
    leaf3981InputLogOnePlusV = outerEnclosure 24
      (leaf3981Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3981RoundedFacts : LeafRoundedFacts 8
    leaf3981Certificate.logOnePlusV leaf3981InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3981InputLogOnePlusV_eq }

private noncomputable def leaf3981Inputs : Inputs :=
  inputsOfCaches globalInput sk108RoundedInputs
    chi245InputQChi innerPair226Input
    leaf3981InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3981LowerChecked :
    lowerCheck 24 leaf3981Box leaf3981Inputs = true := by
  rfl'

private theorem leaf3981CoversExact : CoversExact 8
    leaf3981Box leaf3981Certificate leaf3981InnerLog leaf3981Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk108RoundedFacts chi245RoundedFacts
    innerPair226RoundedFacts leaf3981RoundedFacts (by rfl)

private theorem leaf3981FlatSound : Sound leaf3981Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3981CertificateValid
    leaf3981InnerLogValid leaf3981CoversExact leaf3981LowerChecked

private noncomputable def leaf3982Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (37/128), chiHi := (19/64) }

private noncomputable def leaf3982Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435711/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715974656) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (484199311/268435456) }, upper := { exponent := 0, mantissa := (1879/1024) } }, logOuter := sk108LogOuterCertificate, logK := sk108LogKCertificate, logChi := chi246LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434468351/137431949312) } }, logDArg := sk108LogDArgCertificate }

private noncomputable def leaf3982InnerLog : WideLogData :=
  innerPair220Data

set_option maxRecDepth 1000000 in
private theorem leaf3982LocalValidity :
    LeafFacts leaf3982Box leaf3982Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3982Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715974656) }) = true
      norm_num [leaf3982Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3982CertificateValid :
    WideCertificateValid leaf3982Box leaf3982Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk108ValidityFacts chi246ValidityFacts
    leaf3982LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3982CoverageChecked :
    coverageCheck (innerAD leaf3982Box) leaf3982InnerLog = true := by
  rfl'

private theorem leaf3982InnerLogValid :
    leaf3982InnerLog.Valid 8 (innerAD leaf3982Box) :=
  wideLogDataValid_of_cachedCheck endpoint67PositiveFacts
    endpoint61PositiveFacts.valid leaf3982CoverageChecked

private noncomputable def leaf3982InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907347/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3982InputLogOnePlusV_eq :
    leaf3982InputLogOnePlusV = outerEnclosure 24
      (leaf3982Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3982RoundedFacts : LeafRoundedFacts 8
    leaf3982Certificate.logOnePlusV leaf3982InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3982InputLogOnePlusV_eq }

private noncomputable def leaf3982Inputs : Inputs :=
  inputsOfCaches globalInput sk108RoundedInputs
    chi246InputQChi innerPair220Input
    leaf3982InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3982LowerChecked :
    lowerCheck 24 leaf3982Box leaf3982Inputs = true := by
  rfl'

private theorem leaf3982CoversExact : CoversExact 8
    leaf3982Box leaf3982Certificate leaf3982InnerLog leaf3982Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk108RoundedFacts chi246RoundedFacts
    innerPair220RoundedFacts leaf3982RoundedFacts (by rfl)

private theorem leaf3982FlatSound : Sound leaf3982Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3982CertificateValid
    leaf3982InnerLogValid leaf3982CoversExact leaf3982LowerChecked

private noncomputable def leaf3983Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (19/64), chiHi := (39/128) }

private noncomputable def leaf3983Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435711/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715922432) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (487541443/268435456) }, upper := { exponent := 0, mantissa := (7567/4096) } }, logOuter := sk107LogOuterCertificate, logK := sk107LogKCertificate, logChi := chi247LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434416127/137431844864) } }, logDArg := sk107LogDArgCertificate }

private noncomputable def leaf3983InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3983LocalValidity :
    LeafFacts leaf3983Box leaf3983Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3983Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715922432) }) = true
      norm_num [leaf3983Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3983CertificateValid :
    WideCertificateValid leaf3983Box leaf3983Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk107ValidityFacts chi247ValidityFacts
    leaf3983LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3983CoverageChecked :
    coverageCheck (innerAD leaf3983Box) leaf3983InnerLog = true := by
  rfl'

private theorem leaf3983InnerLogValid :
    leaf3983InnerLog.Valid 8 (innerAD leaf3983Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3983CoverageChecked

private noncomputable def leaf3983InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629395/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3983InputLogOnePlusV_eq :
    leaf3983InputLogOnePlusV = outerEnclosure 24
      (leaf3983Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3983RoundedFacts : LeafRoundedFacts 8
    leaf3983Certificate.logOnePlusV leaf3983InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3983InputLogOnePlusV_eq }

private noncomputable def leaf3983Inputs : Inputs :=
  inputsOfCaches globalInput sk107RoundedInputs
    chi247InputQChi innerPair91Input
    leaf3983InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3983LowerChecked :
    lowerCheck 24 leaf3983Box leaf3983Inputs = true := by
  rfl'

private theorem leaf3983CoversExact : CoversExact 8
    leaf3983Box leaf3983Certificate leaf3983InnerLog leaf3983Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk107RoundedFacts chi247RoundedFacts
    innerPair91RoundedFacts leaf3983RoundedFacts (by rfl)

private theorem leaf3983FlatSound : Sound leaf3983Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3983CertificateValid
    leaf3983InnerLogValid leaf3983CoversExact leaf3983LowerChecked

private noncomputable def leaf3984Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (39/128), chiHi := (5/16) }

private noncomputable def leaf3984Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435713/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715831296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (493308257/268435456) }, upper := { exponent := 0, mantissa := (957/512) } }, logOuter := sk107LogOuterCertificate, logK := sk107LogKCertificate, logChi := chi248LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434324991/137431662592) } }, logDArg := sk107LogDArgCertificate }

private noncomputable def leaf3984InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3984LocalValidity :
    LeafFacts leaf3984Box leaf3984Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3984Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715831296) }) = true
      norm_num [leaf3984Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3984CertificateValid :
    WideCertificateValid leaf3984Box leaf3984Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk107ValidityFacts chi248ValidityFacts
    leaf3984LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3984CoverageChecked :
    coverageCheck (innerAD leaf3984Box) leaf3984InnerLog = true := by
  rfl'

private theorem leaf3984InnerLogValid :
    leaf3984InnerLog.Valid 8 (innerAD leaf3984Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3984CoverageChecked

private noncomputable def leaf3984InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814703/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3984InputLogOnePlusV_eq :
    leaf3984InputLogOnePlusV = outerEnclosure 24
      (leaf3984Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3984RoundedFacts : LeafRoundedFacts 8
    leaf3984Certificate.logOnePlusV leaf3984InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3984InputLogOnePlusV_eq }

private noncomputable def leaf3984Inputs : Inputs :=
  inputsOfCaches globalInput sk107RoundedInputs
    chi248InputQChi innerPair91Input
    leaf3984InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3984LowerChecked :
    lowerCheck 24 leaf3984Box leaf3984Inputs = true := by
  rfl'

private theorem leaf3984CoversExact : CoversExact 8
    leaf3984Box leaf3984Certificate leaf3984InnerLog leaf3984Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk107RoundedFacts chi248RoundedFacts
    innerPair91RoundedFacts leaf3984RoundedFacts (by rfl)

private theorem leaf3984FlatSound : Sound leaf3984Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3984CertificateValid
    leaf3984InnerLogValid leaf3984CoversExact leaf3984LowerChecked

private noncomputable def leaf3985Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (19/64), chiHi := (39/128) }

private noncomputable def leaf3985Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435713/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715882496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (490031657/268435456) }, upper := { exponent := 0, mantissa := (3803/2048) } }, logOuter := sk108LogOuterCertificate, logK := sk108LogKCertificate, logChi := chi247LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434376191/137431764992) } }, logDArg := sk108LogDArgCertificate }

private noncomputable def leaf3985InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3985LocalValidity :
    LeafFacts leaf3985Box leaf3985Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3985Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715882496) }) = true
      norm_num [leaf3985Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3985CertificateValid :
    WideCertificateValid leaf3985Box leaf3985Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk108ValidityFacts chi247ValidityFacts
    leaf3985LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3985CoverageChecked :
    coverageCheck (innerAD leaf3985Box) leaf3985InnerLog = true := by
  rfl'

private theorem leaf3985InnerLogValid :
    leaf3985InnerLog.Valid 8 (innerAD leaf3985Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3985CoverageChecked

private noncomputable def leaf3985InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453675/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3985InputLogOnePlusV_eq :
    leaf3985InputLogOnePlusV = outerEnclosure 24
      (leaf3985Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3985RoundedFacts : LeafRoundedFacts 8
    leaf3985Certificate.logOnePlusV leaf3985InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3985InputLogOnePlusV_eq }

private noncomputable def leaf3985Inputs : Inputs :=
  inputsOfCaches globalInput sk108RoundedInputs
    chi247InputQChi innerPair91Input
    leaf3985InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3985LowerChecked :
    lowerCheck 24 leaf3985Box leaf3985Inputs = true := by
  rfl'

private theorem leaf3985CoversExact : CoversExact 8
    leaf3985Box leaf3985Certificate leaf3985InnerLog leaf3985Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk108RoundedFacts chi247RoundedFacts
    innerPair91RoundedFacts leaf3985RoundedFacts (by rfl)

private theorem leaf3985FlatSound : Sound leaf3985Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3985CertificateValid
    leaf3985InnerLogValid leaf3985CoversExact leaf3985LowerChecked

private noncomputable def leaf3986Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (39/128), chiHi := (5/16) }

private noncomputable def leaf3986Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435715/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715790336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (495864003/268435456) }, upper := { exponent := 0, mantissa := (481/256) } }, logOuter := sk108LogOuterCertificate, logK := sk108LogKCertificate, logChi := chi248LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434284031/137431580672) } }, logDArg := sk108LogDArgCertificate }

private noncomputable def leaf3986InnerLog : WideLogData :=
  innerPair199Data

set_option maxRecDepth 1000000 in
private theorem leaf3986LocalValidity :
    LeafFacts leaf3986Box leaf3986Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3986Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715790336) }) = true
      norm_num [leaf3986Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3986CertificateValid :
    WideCertificateValid leaf3986Box leaf3986Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk108ValidityFacts chi248ValidityFacts
    leaf3986LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3986CoverageChecked :
    coverageCheck (innerAD leaf3986Box) leaf3986InnerLog = true := by
  rfl'

private theorem leaf3986InnerLogValid :
    leaf3986InnerLog.Valid 8 (innerAD leaf3986Box) :=
  wideLogDataValid_of_cachedCheck endpoint61PositiveFacts
    endpoint69PositiveFacts.valid leaf3986CoverageChecked

private noncomputable def leaf3986InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629411/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3986InputLogOnePlusV_eq :
    leaf3986InputLogOnePlusV = outerEnclosure 24
      (leaf3986Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3986RoundedFacts : LeafRoundedFacts 8
    leaf3986Certificate.logOnePlusV leaf3986InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3986InputLogOnePlusV_eq }

private noncomputable def leaf3986Inputs : Inputs :=
  inputsOfCaches globalInput sk108RoundedInputs
    chi248InputQChi innerPair199Input
    leaf3986InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3986LowerChecked :
    lowerCheck 24 leaf3986Box leaf3986Inputs = true := by
  rfl'

private theorem leaf3986CoversExact : CoversExact 8
    leaf3986Box leaf3986Certificate leaf3986InnerLog leaf3986Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk108RoundedFacts chi248RoundedFacts
    innerPair199RoundedFacts leaf3986RoundedFacts (by rfl)

private theorem leaf3986FlatSound : Sound leaf3986Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3986CertificateValid
    leaf3986InnerLogValid leaf3986CoversExact leaf3986LowerChecked

private noncomputable def leaf3987Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32), chiLo := (9/32), chiHi := (37/128) }

private noncomputable def leaf3987Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435711/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905342976) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (480726115/268435456) }, upper := { exponent := 0, mantissa := (7463/4096) } }, logOuter := sk109LogOuterCertificate, logK := sk109LogKCertificate, logChi := chi245LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811507541/45810685952) } }, logDArg := sk109LogDArgCertificate }

private noncomputable def leaf3987InnerLog : WideLogData :=
  innerPair226Data

set_option maxRecDepth 1000000 in
private theorem leaf3987LocalValidity :
    LeafFacts leaf3987Box leaf3987Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3987Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905342976) }) = true
      norm_num [leaf3987Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3987CertificateValid :
    WideCertificateValid leaf3987Box leaf3987Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk109ValidityFacts chi245ValidityFacts
    leaf3987LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3987CoverageChecked :
    coverageCheck (innerAD leaf3987Box) leaf3987InnerLog = true := by
  rfl'

private theorem leaf3987InnerLogValid :
    leaf3987InnerLog.Valid 8 (innerAD leaf3987Box) :=
  wideLogDataValid_of_cachedCheck endpoint68PositiveFacts
    endpoint64PositiveFacts.valid leaf3987CoverageChecked

private noncomputable def leaf3987InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814691/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3987InputLogOnePlusV_eq :
    leaf3987InputLogOnePlusV = outerEnclosure 24
      (leaf3987Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3987RoundedFacts : LeafRoundedFacts 8
    leaf3987Certificate.logOnePlusV leaf3987InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3987InputLogOnePlusV_eq }

private noncomputable def leaf3987Inputs : Inputs :=
  inputsOfCaches globalInput sk109RoundedInputs
    chi245InputQChi innerPair226Input
    leaf3987InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3987LowerChecked :
    lowerCheck 24 leaf3987Box leaf3987Inputs = true := by
  rfl'

private theorem leaf3987CoversExact : CoversExact 8
    leaf3987Box leaf3987Certificate leaf3987InnerLog leaf3987Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk109RoundedFacts chi245RoundedFacts
    innerPair226RoundedFacts leaf3987RoundedFacts (by rfl)

private theorem leaf3987FlatSound : Sound leaf3987Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3987CertificateValid
    leaf3987InnerLogValid leaf3987CoversExact leaf3987LowerChecked

private noncomputable def leaf3988Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32), chiLo := (37/128), chiHi := (19/64) }

private noncomputable def leaf3988Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435713/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715935744) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (486623993/268435456) }, upper := { exponent := 0, mantissa := (3777/2048) } }, logOuter := sk109LogOuterCertificate, logK := sk109LogKCertificate, logChi := chi246LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434429439/137431871488) } }, logDArg := sk109LogDArgCertificate }

private noncomputable def leaf3988InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3988LocalValidity :
    LeafFacts leaf3988Box leaf3988Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3988Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715935744) }) = true
      norm_num [leaf3988Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3988CertificateValid :
    WideCertificateValid leaf3988Box leaf3988Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk109ValidityFacts chi246ValidityFacts
    leaf3988LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3988CoverageChecked :
    coverageCheck (innerAD leaf3988Box) leaf3988InnerLog = true := by
  rfl'

private theorem leaf3988InnerLogValid :
    leaf3988InnerLog.Valid 8 (innerAD leaf3988Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3988CoverageChecked

private noncomputable def leaf3988InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629393/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3988InputLogOnePlusV_eq :
    leaf3988InputLogOnePlusV = outerEnclosure 24
      (leaf3988Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3988RoundedFacts : LeafRoundedFacts 8
    leaf3988Certificate.logOnePlusV leaf3988InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3988InputLogOnePlusV_eq }

private noncomputable def leaf3988Inputs : Inputs :=
  inputsOfCaches globalInput sk109RoundedInputs
    chi246InputQChi innerPair91Input
    leaf3988InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3988LowerChecked :
    lowerCheck 24 leaf3988Box leaf3988Inputs = true := by
  rfl'

private theorem leaf3988CoversExact : CoversExact 8
    leaf3988Box leaf3988Certificate leaf3988InnerLog leaf3988Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk109RoundedFacts chi246RoundedFacts
    innerPair91RoundedFacts leaf3988RoundedFacts (by rfl)

private theorem leaf3988FlatSound : Sound leaf3988Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3988CertificateValid
    leaf3988InnerLogValid leaf3988CoversExact leaf3988LowerChecked

private noncomputable def leaf3989Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8), chiLo := (9/32), chiHi := (37/128) }

private noncomputable def leaf3989Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435713/268435456) }, vSqrt := { lower := (32765/32768), upper := (808452867/808423424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (483085265/268435456) }, upper := { exponent := 0, mantissa := (1875/1024) } }, logOuter := sk110LogOuterCertificate, logK := sk110LogKCertificate, logChi := chi245LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (1616876291/1616846848) } }, logDArg := sk110LogDArgCertificate }

private noncomputable def leaf3989InnerLog : WideLogData :=
  innerPair220Data

set_option maxRecDepth 1000000 in
private theorem leaf3989LocalValidity :
    LeafFacts leaf3989Box leaf3989Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3989Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (808452867/808423424) }) = true
      norm_num [leaf3989Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3989CertificateValid :
    WideCertificateValid leaf3989Box leaf3989Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk110ValidityFacts chi245ValidityFacts
    leaf3989LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3989CoverageChecked :
    coverageCheck (innerAD leaf3989Box) leaf3989InnerLog = true := by
  rfl'

private theorem leaf3989InnerLogValid :
    leaf3989InnerLog.Valid 8 (innerAD leaf3989Box) :=
  wideLogDataValid_of_cachedCheck endpoint67PositiveFacts
    endpoint61PositiveFacts.valid leaf3989CoverageChecked

private noncomputable def leaf3989InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814693/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3989InputLogOnePlusV_eq :
    leaf3989InputLogOnePlusV = outerEnclosure 24
      (leaf3989Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3989RoundedFacts : LeafRoundedFacts 8
    leaf3989Certificate.logOnePlusV leaf3989InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3989InputLogOnePlusV_eq }

private noncomputable def leaf3989Inputs : Inputs :=
  inputsOfCaches globalInput sk110RoundedInputs
    chi245InputQChi innerPair220Input
    leaf3989InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3989LowerChecked :
    lowerCheck 24 leaf3989Box leaf3989Inputs = true := by
  rfl'

private theorem leaf3989CoversExact : CoversExact 8
    leaf3989Box leaf3989Certificate leaf3989InnerLog leaf3989Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk110RoundedFacts chi245RoundedFacts
    innerPair220RoundedFacts leaf3989RoundedFacts (by rfl)

private theorem leaf3989FlatSound : Sound leaf3989Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3989CertificateValid
    leaf3989InnerLogValid leaf3989CoversExact leaf3989LowerChecked

private noncomputable def leaf3990Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8), chiLo := (37/128), chiHi := (19/64) }

private noncomputable def leaf3990Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435715/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905298944) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (489048675/268435456) }, upper := { exponent := 0, mantissa := (949/512) } }, logOuter := sk110LogOuterCertificate, logK := sk110LogKCertificate, logChi := chi246LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811463509/45810597888) } }, logDArg := sk110LogDArgCertificate }

private noncomputable def leaf3990InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3990LocalValidity :
    LeafFacts leaf3990Box leaf3990Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3990Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905298944) }) = true
      norm_num [leaf3990Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3990CertificateValid :
    WideCertificateValid leaf3990Box leaf3990Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk110ValidityFacts chi246ValidityFacts
    leaf3990LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3990CoverageChecked :
    coverageCheck (innerAD leaf3990Box) leaf3990InnerLog = true := by
  rfl'

private theorem leaf3990InnerLogValid :
    leaf3990InnerLog.Valid 8 (innerAD leaf3990Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3990CoverageChecked

private noncomputable def leaf3990InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814699/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3990InputLogOnePlusV_eq :
    leaf3990InputLogOnePlusV = outerEnclosure 24
      (leaf3990Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3990RoundedFacts : LeafRoundedFacts 8
    leaf3990Certificate.logOnePlusV leaf3990InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3990InputLogOnePlusV_eq }

private noncomputable def leaf3990Inputs : Inputs :=
  inputsOfCaches globalInput sk110RoundedInputs
    chi246InputQChi innerPair91Input
    leaf3990InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3990LowerChecked :
    lowerCheck 24 leaf3990Box leaf3990Inputs = true := by
  rfl'

private theorem leaf3990CoversExact : CoversExact 8
    leaf3990Box leaf3990Certificate leaf3990InnerLog leaf3990Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk110RoundedFacts chi246RoundedFacts
    innerPair91RoundedFacts leaf3990RoundedFacts (by rfl)

private theorem leaf3990FlatSound : Sound leaf3990Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3990CertificateValid
    leaf3990InnerLogValid leaf3990CoversExact leaf3990LowerChecked

private noncomputable def leaf3991Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32), chiLo := (19/64), chiHi := (39/128) }

private noncomputable def leaf3991Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435715/268435456) }, vSqrt := { lower := (32765/32768), upper := (13743698739/13743168512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (492521871/268435456) }, upper := { exponent := 0, mantissa := (7645/4096) } }, logOuter := sk109LogOuterCertificate, logK := sk109LogKCertificate, logChi := chi247LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (27486867251/27486337024) } }, logDArg := sk109LogDArgCertificate }

private noncomputable def leaf3991InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3991LocalValidity :
    LeafFacts leaf3991Box leaf3991Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3991Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (13743698739/13743168512) }) = true
      norm_num [leaf3991Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3991CertificateValid :
    WideCertificateValid leaf3991Box leaf3991Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk109ValidityFacts chi247ValidityFacts
    leaf3991LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3991CoverageChecked :
    coverageCheck (innerAD leaf3991Box) leaf3991InnerLog = true := by
  rfl'

private theorem leaf3991InnerLogValid :
    leaf3991InnerLog.Valid 8 (innerAD leaf3991Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3991CoverageChecked

private noncomputable def leaf3991InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907351/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3991InputLogOnePlusV_eq :
    leaf3991InputLogOnePlusV = outerEnclosure 24
      (leaf3991Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3991RoundedFacts : LeafRoundedFacts 8
    leaf3991Certificate.logOnePlusV leaf3991InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3991InputLogOnePlusV_eq }

private noncomputable def leaf3991Inputs : Inputs :=
  inputsOfCaches globalInput sk109RoundedInputs
    chi247InputQChi innerPair91Input
    leaf3991InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3991LowerChecked :
    lowerCheck 24 leaf3991Box leaf3991Inputs = true := by
  rfl'

private theorem leaf3991CoversExact : CoversExact 8
    leaf3991Box leaf3991Certificate leaf3991InnerLog leaf3991Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk109RoundedFacts chi247RoundedFacts
    innerPair91RoundedFacts leaf3991RoundedFacts (by rfl)

private theorem leaf3991FlatSound : Sound leaf3991Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3991CertificateValid
    leaf3991InnerLogValid leaf3991CoversExact leaf3991LowerChecked

private noncomputable def leaf3992Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32), chiLo := (39/128), chiHi := (5/16) }

private noncomputable def leaf3992Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435717/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905249792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (498419749/268435456) }, upper := { exponent := 0, mantissa := (967/512) } }, logOuter := sk109LogOuterCertificate, logK := sk109LogKCertificate, logChi := chi248LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811414357/45810499584) } }, logDArg := sk109LogDArgCertificate }

private noncomputable def leaf3992InnerLog : WideLogData :=
  innerPair199Data

set_option maxRecDepth 1000000 in
private theorem leaf3992LocalValidity :
    LeafFacts leaf3992Box leaf3992Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3992Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905249792) }) = true
      norm_num [leaf3992Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3992CertificateValid :
    WideCertificateValid leaf3992Box leaf3992Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk109ValidityFacts chi248ValidityFacts
    leaf3992LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3992CoverageChecked :
    coverageCheck (innerAD leaf3992Box) leaf3992InnerLog = true := by
  rfl'

private theorem leaf3992InnerLogValid :
    leaf3992InnerLog.Valid 8 (innerAD leaf3992Box) :=
  wideLogDataValid_of_cachedCheck endpoint61PositiveFacts
    endpoint69PositiveFacts.valid leaf3992CoverageChecked

private noncomputable def leaf3992InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453677/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3992InputLogOnePlusV_eq :
    leaf3992InputLogOnePlusV = outerEnclosure 24
      (leaf3992Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3992RoundedFacts : LeafRoundedFacts 8
    leaf3992Certificate.logOnePlusV leaf3992InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3992InputLogOnePlusV_eq }

private noncomputable def leaf3992Inputs : Inputs :=
  inputsOfCaches globalInput sk109RoundedInputs
    chi248InputQChi innerPair199Input
    leaf3992InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3992LowerChecked :
    lowerCheck 24 leaf3992Box leaf3992Inputs = true := by
  rfl'

private theorem leaf3992CoversExact : CoversExact 8
    leaf3992Box leaf3992Certificate leaf3992InnerLog leaf3992Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk109RoundedFacts chi248RoundedFacts
    innerPair199RoundedFacts leaf3992RoundedFacts (by rfl)

private theorem leaf3992FlatSound : Sound leaf3992Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3992CertificateValid
    leaf3992InnerLogValid leaf3992CoversExact leaf3992LowerChecked

private noncomputable def leaf3993Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8), chiLo := (19/64), chiHi := (39/128) }

private noncomputable def leaf3993Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435717/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715802624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (495012085/268435456) }, upper := { exponent := 0, mantissa := (1921/1024) } }, logOuter := sk110LogOuterCertificate, logK := sk110LogKCertificate, logChi := chi247LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434296319/137431605248) } }, logDArg := sk110LogDArgCertificate }

private noncomputable def leaf3993InnerLog : WideLogData :=
  innerPair199Data

set_option maxRecDepth 1000000 in
private theorem leaf3993LocalValidity :
    LeafFacts leaf3993Box leaf3993Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3993Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715802624) }) = true
      norm_num [leaf3993Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3993CertificateValid :
    WideCertificateValid leaf3993Box leaf3993Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk110ValidityFacts chi247ValidityFacts
    leaf3993LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3993CoverageChecked :
    coverageCheck (innerAD leaf3993Box) leaf3993InnerLog = true := by
  rfl'

private theorem leaf3993InnerLogValid :
    leaf3993InnerLog.Valid 8 (innerAD leaf3993Box) :=
  wideLogDataValid_of_cachedCheck endpoint61PositiveFacts
    endpoint69PositiveFacts.valid leaf3993CoverageChecked

private noncomputable def leaf3993InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629409/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3993InputLogOnePlusV_eq :
    leaf3993InputLogOnePlusV = outerEnclosure 24
      (leaf3993Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3993RoundedFacts : LeafRoundedFacts 8
    leaf3993Certificate.logOnePlusV leaf3993InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3993InputLogOnePlusV_eq }

private noncomputable def leaf3993Inputs : Inputs :=
  inputsOfCaches globalInput sk110RoundedInputs
    chi247InputQChi innerPair199Input
    leaf3993InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3993LowerChecked :
    lowerCheck 24 leaf3993Box leaf3993Inputs = true := by
  rfl'

private theorem leaf3993CoversExact : CoversExact 8
    leaf3993Box leaf3993Certificate leaf3993InnerLog leaf3993Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk110RoundedFacts chi247RoundedFacts
    innerPair199RoundedFacts leaf3993RoundedFacts (by rfl)

private theorem leaf3993FlatSound : Sound leaf3993Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3993CertificateValid
    leaf3993InnerLogValid leaf3993CoversExact leaf3993LowerChecked

private noncomputable def leaf3994Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8), chiLo := (39/128), chiHi := (5/16) }

private noncomputable def leaf3994Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435719/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715708416) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (500975495/268435456) }, upper := { exponent := 0, mantissa := (243/128) } }, logOuter := sk110LogOuterCertificate, logK := sk110LogKCertificate, logChi := chi248LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434202111/137431416832) } }, logDArg := sk110LogDArgCertificate }

private noncomputable def leaf3994InnerLog : WideLogData :=
  innerPair483Data

set_option maxRecDepth 1000000 in
private theorem leaf3994LocalValidity :
    LeafFacts leaf3994Box leaf3994Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3994Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715708416) }) = true
      norm_num [leaf3994Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3994CertificateValid :
    WideCertificateValid leaf3994Box leaf3994Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk110ValidityFacts chi248ValidityFacts
    leaf3994LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3994CoverageChecked :
    coverageCheck (innerAD leaf3994Box) leaf3994InnerLog = true := by
  rfl'

private theorem leaf3994InnerLogValid :
    leaf3994InnerLog.Valid 8 (innerAD leaf3994Box) :=
  wideLogDataValid_of_cachedCheck endpoint211PositiveFacts
    endpoint70PositiveFacts.valid leaf3994CoverageChecked

private noncomputable def leaf3994InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629421/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3994InputLogOnePlusV_eq :
    leaf3994InputLogOnePlusV = outerEnclosure 24
      (leaf3994Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3994RoundedFacts : LeafRoundedFacts 8
    leaf3994Certificate.logOnePlusV leaf3994InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3994InputLogOnePlusV_eq }

private noncomputable def leaf3994Inputs : Inputs :=
  inputsOfCaches globalInput sk110RoundedInputs
    chi248InputQChi innerPair483Input
    leaf3994InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3994LowerChecked :
    lowerCheck 24 leaf3994Box leaf3994Inputs = true := by
  rfl'

private theorem leaf3994CoversExact : CoversExact 8
    leaf3994Box leaf3994Certificate leaf3994InnerLog leaf3994Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk110RoundedFacts chi248RoundedFacts
    innerPair483RoundedFacts leaf3994RoundedFacts (by rfl)

private theorem leaf3994FlatSound : Sound leaf3994Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3994CertificateValid
    leaf3994InnerLogValid leaf3994CoversExact leaf3994LowerChecked

private noncomputable def component81Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component81Node0_sound : Sound component81Node0Box :=
  sound_of_literal_split component81Node0Box leaf3963Box leaf3964Box
    .chi (33/128) (by rfl) (by rfl)
    leaf3963FlatSound leaf3964FlatSound

private noncomputable def component81Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component81Node1_sound : Sound component81Node1Box :=
  sound_of_literal_split component81Node1Box leaf3965Box leaf3966Box
    .chi (33/128) (by rfl) (by rfl)
    leaf3965FlatSound leaf3966FlatSound

private noncomputable def component81Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component81Node2_sound : Sound component81Node2Box :=
  sound_of_literal_split component81Node2Box component81Node0Box component81Node1Box
    .k (89/32) (by rfl) (by rfl)
    component81Node0_sound component81Node1_sound

private noncomputable def component81Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component81Node3_sound : Sound component81Node3Box :=
  sound_of_literal_split component81Node3Box leaf3967Box leaf3968Box
    .chi (35/128) (by rfl) (by rfl)
    leaf3967FlatSound leaf3968FlatSound

private noncomputable def component81Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component81Node4_sound : Sound component81Node4Box :=
  sound_of_literal_split component81Node4Box leaf3969Box leaf3970Box
    .chi (35/128) (by rfl) (by rfl)
    leaf3969FlatSound leaf3970FlatSound

private noncomputable def component81Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component81Node5_sound : Sound component81Node5Box :=
  sound_of_literal_split component81Node5Box component81Node3Box component81Node4Box
    .k (89/32) (by rfl) (by rfl)
    component81Node3_sound component81Node4_sound

private noncomputable def component81Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (1/4), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component81Node6_sound : Sound component81Node6Box :=
  sound_of_literal_split component81Node6Box component81Node2Box component81Node5Box
    .chi (17/64) (by rfl) (by rfl)
    component81Node2_sound component81Node5_sound

private noncomputable def component81Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component81Node7_sound : Sound component81Node7Box :=
  sound_of_literal_split component81Node7Box leaf3971Box leaf3972Box
    .chi (33/128) (by rfl) (by rfl)
    leaf3971FlatSound leaf3972FlatSound

private noncomputable def component81Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component81Node8_sound : Sound component81Node8Box :=
  sound_of_literal_split component81Node8Box leaf3973Box leaf3974Box
    .chi (33/128) (by rfl) (by rfl)
    leaf3973FlatSound leaf3974FlatSound

private noncomputable def component81Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component81Node9_sound : Sound component81Node9Box :=
  sound_of_literal_split component81Node9Box component81Node7Box component81Node8Box
    .k (91/32) (by rfl) (by rfl)
    component81Node7_sound component81Node8_sound

private noncomputable def component81Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component81Node10_sound : Sound component81Node10Box :=
  sound_of_literal_split component81Node10Box leaf3975Box leaf3976Box
    .chi (35/128) (by rfl) (by rfl)
    leaf3975FlatSound leaf3976FlatSound

private noncomputable def component81Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component81Node11_sound : Sound component81Node11Box :=
  sound_of_literal_split component81Node11Box leaf3977Box leaf3978Box
    .chi (35/128) (by rfl) (by rfl)
    leaf3977FlatSound leaf3978FlatSound

private noncomputable def component81Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component81Node12_sound : Sound component81Node12Box :=
  sound_of_literal_split component81Node12Box component81Node10Box component81Node11Box
    .k (91/32) (by rfl) (by rfl)
    component81Node10_sound component81Node11_sound

private noncomputable def component81Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (1/4), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component81Node13_sound : Sound component81Node13Box :=
  sound_of_literal_split component81Node13Box component81Node9Box component81Node12Box
    .chi (17/64) (by rfl) (by rfl)
    component81Node9_sound component81Node12_sound

private noncomputable def component81Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (1/4), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component81Node14_sound : Sound component81Node14Box :=
  sound_of_literal_split component81Node14Box component81Node6Box component81Node13Box
    .k (45/16) (by rfl) (by rfl)
    component81Node6_sound component81Node13_sound

private noncomputable def component81Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component81Node15_sound : Sound component81Node15Box :=
  sound_of_literal_split component81Node15Box leaf3979Box leaf3980Box
    .chi (37/128) (by rfl) (by rfl)
    leaf3979FlatSound leaf3980FlatSound

private noncomputable def component81Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component81Node16_sound : Sound component81Node16Box :=
  sound_of_literal_split component81Node16Box leaf3981Box leaf3982Box
    .chi (37/128) (by rfl) (by rfl)
    leaf3981FlatSound leaf3982FlatSound

private noncomputable def component81Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component81Node17_sound : Sound component81Node17Box :=
  sound_of_literal_split component81Node17Box component81Node15Box component81Node16Box
    .k (89/32) (by rfl) (by rfl)
    component81Node15_sound component81Node16_sound

private noncomputable def component81Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (19/64), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component81Node18_sound : Sound component81Node18Box :=
  sound_of_literal_split component81Node18Box leaf3983Box leaf3984Box
    .chi (39/128) (by rfl) (by rfl)
    leaf3983FlatSound leaf3984FlatSound

private noncomputable def component81Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (19/64), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component81Node19_sound : Sound component81Node19Box :=
  sound_of_literal_split component81Node19Box leaf3985Box leaf3986Box
    .chi (39/128) (by rfl) (by rfl)
    leaf3985FlatSound leaf3986FlatSound

private noncomputable def component81Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (19/64), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component81Node20_sound : Sound component81Node20Box :=
  sound_of_literal_split component81Node20Box component81Node18Box component81Node19Box
    .k (89/32) (by rfl) (by rfl)
    component81Node18_sound component81Node19_sound

private noncomputable def component81Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (9/32), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component81Node21_sound : Sound component81Node21Box :=
  sound_of_literal_split component81Node21Box component81Node17Box component81Node20Box
    .chi (19/64) (by rfl) (by rfl)
    component81Node17_sound component81Node20_sound

private noncomputable def component81Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component81Node22_sound : Sound component81Node22Box :=
  sound_of_literal_split component81Node22Box leaf3987Box leaf3988Box
    .chi (37/128) (by rfl) (by rfl)
    leaf3987FlatSound leaf3988FlatSound

private noncomputable def component81Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component81Node23_sound : Sound component81Node23Box :=
  sound_of_literal_split component81Node23Box leaf3989Box leaf3990Box
    .chi (37/128) (by rfl) (by rfl)
    leaf3989FlatSound leaf3990FlatSound

private noncomputable def component81Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component81Node24_sound : Sound component81Node24Box :=
  sound_of_literal_split component81Node24Box component81Node22Box component81Node23Box
    .k (91/32) (by rfl) (by rfl)
    component81Node22_sound component81Node23_sound

private noncomputable def component81Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32), chiLo := (19/64), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component81Node25_sound : Sound component81Node25Box :=
  sound_of_literal_split component81Node25Box leaf3991Box leaf3992Box
    .chi (39/128) (by rfl) (by rfl)
    leaf3991FlatSound leaf3992FlatSound

private noncomputable def component81Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8), chiLo := (19/64), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component81Node26_sound : Sound component81Node26Box :=
  sound_of_literal_split component81Node26Box leaf3993Box leaf3994Box
    .chi (39/128) (by rfl) (by rfl)
    leaf3993FlatSound leaf3994FlatSound

private noncomputable def component81Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (19/64), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component81Node27_sound : Sound component81Node27Box :=
  sound_of_literal_split component81Node27Box component81Node25Box component81Node26Box
    .k (91/32) (by rfl) (by rfl)
    component81Node25_sound component81Node26_sound

private noncomputable def component81Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (9/32), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component81Node28_sound : Sound component81Node28Box :=
  sound_of_literal_split component81Node28Box component81Node24Box component81Node27Box
    .chi (19/64) (by rfl) (by rfl)
    component81Node24_sound component81Node27_sound

private noncomputable def component81Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (9/32), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component81Node29_sound : Sound component81Node29Box :=
  sound_of_literal_split component81Node29Box component81Node21Box component81Node28Box
    .k (45/16) (by rfl) (by rfl)
    component81Node21_sound component81Node28_sound

noncomputable def component81Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (1/4), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
theorem component81_sound : Sound component81Box :=
  sound_of_literal_split component81Box component81Node14Box component81Node29Box
    .chi (9/32) (by rfl) (by rfl)
    component81Node14_sound component81Node29_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
