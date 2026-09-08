import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch3
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

private noncomputable def leaf3846Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (81/32), chiLo := (1/4), chiHi := (33/128) }

private noncomputable def leaf3846Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435683/268435456) }, vSqrt := { lower := (32765/32768), upper := (4042264335/4042161152) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (436164383/268435456) }, upper := { exponent := 0, mantissa := (6769/4096) } }, logOuter := sk99LogOuterCertificate, logK := sk99LogKCertificate, logChi := chi241LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (8084425487/8084322304) } }, logDArg := sk99LogDArgCertificate }

private noncomputable def leaf3846InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf3846LocalValidity :
    LeafFacts leaf3846Box leaf3846Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3846Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4042264335/4042161152) }) = true
      norm_num [leaf3846Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3846CertificateValid :
    WideCertificateValid leaf3846Box leaf3846Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk99ValidityFacts chi241ValidityFacts
    leaf3846LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3846CoverageChecked :
    coverageCheck (innerAD leaf3846Box) leaf3846InnerLog = true := by
  rfl'

private theorem leaf3846InnerLogValid :
    leaf3846InnerLog.Valid 8 (innerAD leaf3846Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf3846CoverageChecked

private noncomputable def leaf3846InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629295/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3846InputLogOnePlusV_eq :
    leaf3846InputLogOnePlusV = outerEnclosure 24
      (leaf3846Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3846RoundedFacts : LeafRoundedFacts 8
    leaf3846Certificate.logOnePlusV leaf3846InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3846InputLogOnePlusV_eq }

private noncomputable def leaf3846Inputs : Inputs :=
  inputsOfCaches globalInput sk99RoundedInputs
    chi241InputQChi innerPair51Input
    leaf3846InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3846LowerChecked :
    lowerCheck 24 leaf3846Box leaf3846Inputs = true := by
  rfl'

private theorem leaf3846CoversExact : CoversExact 8
    leaf3846Box leaf3846Certificate leaf3846InnerLog leaf3846Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk99RoundedFacts chi241RoundedFacts
    innerPair51RoundedFacts leaf3846RoundedFacts (by rfl)

private theorem leaf3846FlatSound : Sound leaf3846Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3846CertificateValid
    leaf3846InnerLogValid leaf3846CoversExact leaf3846LowerChecked

private noncomputable def leaf3847Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (81/32), chiLo := (33/128), chiHi := (17/64) }

private noncomputable def leaf3847Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435685/268435456) }, vSqrt := { lower := (32765/32768), upper := (13743698739/13743331328) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (441406941/268435456) }, upper := { exponent := 0, mantissa := (3425/2048) } }, logOuter := sk99LogOuterCertificate, logK := sk99LogKCertificate, logChi := chi242LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (27487030067/27486662656) } }, logDArg := sk99LogDArgCertificate }

private noncomputable def leaf3847InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf3847LocalValidity :
    LeafFacts leaf3847Box leaf3847Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3847Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (13743698739/13743331328) }) = true
      norm_num [leaf3847Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3847CertificateValid :
    WideCertificateValid leaf3847Box leaf3847Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk99ValidityFacts chi242ValidityFacts
    leaf3847LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3847CoverageChecked :
    coverageCheck (innerAD leaf3847Box) leaf3847InnerLog = true := by
  rfl'

private theorem leaf3847InnerLogValid :
    leaf3847InnerLog.Valid 8 (innerAD leaf3847Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf3847CoverageChecked

private noncomputable def leaf3847InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629305/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3847InputLogOnePlusV_eq :
    leaf3847InputLogOnePlusV = outerEnclosure 24
      (leaf3847Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3847RoundedFacts : LeafRoundedFacts 8
    leaf3847Certificate.logOnePlusV leaf3847InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3847InputLogOnePlusV_eq }

private noncomputable def leaf3847Inputs : Inputs :=
  inputsOfCaches globalInput sk99RoundedInputs
    chi242InputQChi innerPair56Input
    leaf3847InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3847LowerChecked :
    lowerCheck 24 leaf3847Box leaf3847Inputs = true := by
  rfl'

private theorem leaf3847CoversExact : CoversExact 8
    leaf3847Box leaf3847Certificate leaf3847InnerLog leaf3847Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk99RoundedFacts chi242RoundedFacts
    innerPair56RoundedFacts leaf3847RoundedFacts (by rfl)

private theorem leaf3847FlatSound : Sound leaf3847Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3847CertificateValid
    leaf3847InnerLogValid leaf3847CoversExact leaf3847LowerChecked

private noncomputable def leaf3848Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (81/32), kHi := (41/16), chiLo := (1/4), chiHi := (33/128) }

private noncomputable def leaf3848Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435685/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716705792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (438261405/268435456) }, upper := { exponent := 0, mantissa := (3401/2048) } }, logOuter := sk100LogOuterCertificate, logK := sk100LogKCertificate, logChi := chi241LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435199487/137433411584) } }, logDArg := sk100LogDArgCertificate }

private noncomputable def leaf3848InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf3848LocalValidity :
    LeafFacts leaf3848Box leaf3848Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3848Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716705792) }) = true
      norm_num [leaf3848Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3848CertificateValid :
    WideCertificateValid leaf3848Box leaf3848Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk100ValidityFacts chi241ValidityFacts
    leaf3848LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3848CoverageChecked :
    coverageCheck (innerAD leaf3848Box) leaf3848InnerLog = true := by
  rfl'

private theorem leaf3848InnerLogValid :
    leaf3848InnerLog.Valid 8 (innerAD leaf3848Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf3848CoverageChecked

private noncomputable def leaf3848InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629299/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3848InputLogOnePlusV_eq :
    leaf3848InputLogOnePlusV = outerEnclosure 24
      (leaf3848Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3848RoundedFacts : LeafRoundedFacts 8
    leaf3848Certificate.logOnePlusV leaf3848InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3848InputLogOnePlusV_eq }

private noncomputable def leaf3848Inputs : Inputs :=
  inputsOfCaches globalInput sk100RoundedInputs
    chi241InputQChi innerPair56Input
    leaf3848InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3848LowerChecked :
    lowerCheck 24 leaf3848Box leaf3848Inputs = true := by
  rfl'

private theorem leaf3848CoversExact : CoversExact 8
    leaf3848Box leaf3848Certificate leaf3848InnerLog leaf3848Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk100RoundedFacts chi241RoundedFacts
    innerPair56RoundedFacts leaf3848RoundedFacts (by rfl)

private theorem leaf3848FlatSound : Sound leaf3848Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3848CertificateValid
    leaf3848InnerLogValid leaf3848CoversExact leaf3848LowerChecked

private noncomputable def leaf3849Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (81/32), kHi := (41/16), chiLo := (33/128), chiHi := (17/64) }

private noncomputable def leaf3849Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435687/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905540608) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (443569495/268435456) }, upper := { exponent := 0, mantissa := (1721/1024) } }, logOuter := sk100LogOuterCertificate, logK := sk100LogKCertificate, logChi := chi242LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811705173/45811081216) } }, logDArg := sk100LogDArgCertificate }

private noncomputable def leaf3849InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf3849LocalValidity :
    LeafFacts leaf3849Box leaf3849Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3849Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905540608) }) = true
      norm_num [leaf3849Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3849CertificateValid :
    WideCertificateValid leaf3849Box leaf3849Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk100ValidityFacts chi242ValidityFacts
    leaf3849LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3849CoverageChecked :
    coverageCheck (innerAD leaf3849Box) leaf3849InnerLog = true := by
  rfl'

private theorem leaf3849InnerLogValid :
    leaf3849InnerLog.Valid 8 (innerAD leaf3849Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf3849CoverageChecked

private noncomputable def leaf3849InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629309/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3849InputLogOnePlusV_eq :
    leaf3849InputLogOnePlusV = outerEnclosure 24
      (leaf3849Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3849RoundedFacts : LeafRoundedFacts 8
    leaf3849Certificate.logOnePlusV leaf3849InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3849InputLogOnePlusV_eq }

private noncomputable def leaf3849Inputs : Inputs :=
  inputsOfCaches globalInput sk100RoundedInputs
    chi242InputQChi innerPair56Input
    leaf3849InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3849LowerChecked :
    lowerCheck 24 leaf3849Box leaf3849Inputs = true := by
  rfl'

private theorem leaf3849CoversExact : CoversExact 8
    leaf3849Box leaf3849Certificate leaf3849InnerLog leaf3849Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk100RoundedFacts chi242RoundedFacts
    innerPair56RoundedFacts leaf3849RoundedFacts (by rfl)

private theorem leaf3849FlatSound : Sound leaf3849Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3849CertificateValid
    leaf3849InnerLogValid leaf3849CoversExact leaf3849LowerChecked

private noncomputable def leaf3850Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (81/32), chiLo := (17/64), chiHi := (35/128) }

private noncomputable def leaf3850Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435687/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716573696) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (446649499/268435456) }, upper := { exponent := 0, mantissa := (6931/4096) } }, logOuter := sk99LogOuterCertificate, logK := sk99LogKCertificate, logChi := chi243LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435067391/137433147392) } }, logDArg := sk99LogDArgCertificate }

private noncomputable def leaf3850InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf3850LocalValidity :
    LeafFacts leaf3850Box leaf3850Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3850Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716573696) }) = true
      norm_num [leaf3850Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3850CertificateValid :
    WideCertificateValid leaf3850Box leaf3850Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk99ValidityFacts chi243ValidityFacts
    leaf3850LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3850CoverageChecked :
    coverageCheck (innerAD leaf3850Box) leaf3850InnerLog = true := by
  rfl'

private theorem leaf3850InnerLogValid :
    leaf3850InnerLog.Valid 8 (innerAD leaf3850Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf3850CoverageChecked

private noncomputable def leaf3850InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629315/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3850InputLogOnePlusV_eq :
    leaf3850InputLogOnePlusV = outerEnclosure 24
      (leaf3850Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3850RoundedFacts : LeafRoundedFacts 8
    leaf3850Certificate.logOnePlusV leaf3850InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3850InputLogOnePlusV_eq }

private noncomputable def leaf3850Inputs : Inputs :=
  inputsOfCaches globalInput sk99RoundedInputs
    chi243InputQChi innerPair57Input
    leaf3850InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3850LowerChecked :
    lowerCheck 24 leaf3850Box leaf3850Inputs = true := by
  rfl'

private theorem leaf3850CoversExact : CoversExact 8
    leaf3850Box leaf3850Certificate leaf3850InnerLog leaf3850Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk99RoundedFacts chi243RoundedFacts
    innerPair57RoundedFacts leaf3850RoundedFacts (by rfl)

private theorem leaf3850FlatSound : Sound leaf3850Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3850CertificateValid
    leaf3850InnerLogValid leaf3850CoversExact leaf3850LowerChecked

private noncomputable def leaf3851Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (81/32), chiLo := (35/128), chiHi := (9/32) }

private noncomputable def leaf3851Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435689/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716490752) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (451892057/268435456) }, upper := { exponent := 0, mantissa := (1753/1024) } }, logOuter := sk99LogOuterCertificate, logK := sk99LogKCertificate, logChi := chi244LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434984447/137432981504) } }, logDArg := sk99LogDArgCertificate }

private noncomputable def leaf3851InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf3851LocalValidity :
    LeafFacts leaf3851Box leaf3851Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3851Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716490752) }) = true
      norm_num [leaf3851Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3851CertificateValid :
    WideCertificateValid leaf3851Box leaf3851Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk99ValidityFacts chi244ValidityFacts
    leaf3851LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3851CoverageChecked :
    coverageCheck (innerAD leaf3851Box) leaf3851InnerLog = true := by
  rfl'

private theorem leaf3851InnerLogValid :
    leaf3851InnerLog.Valid 8 (innerAD leaf3851Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf3851CoverageChecked

private noncomputable def leaf3851InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629325/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3851InputLogOnePlusV_eq :
    leaf3851InputLogOnePlusV = outerEnclosure 24
      (leaf3851Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3851RoundedFacts : LeafRoundedFacts 8
    leaf3851Certificate.logOnePlusV leaf3851InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3851InputLogOnePlusV_eq }

private noncomputable def leaf3851Inputs : Inputs :=
  inputsOfCaches globalInput sk99RoundedInputs
    chi244InputQChi innerPair57Input
    leaf3851InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3851LowerChecked :
    lowerCheck 24 leaf3851Box leaf3851Inputs = true := by
  rfl'

private theorem leaf3851CoversExact : CoversExact 8
    leaf3851Box leaf3851Certificate leaf3851InnerLog leaf3851Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk99RoundedFacts chi244RoundedFacts
    innerPair57RoundedFacts leaf3851RoundedFacts (by rfl)

private theorem leaf3851FlatSound : Sound leaf3851Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3851CertificateValid
    leaf3851InnerLogValid leaf3851CoversExact leaf3851LowerChecked

private noncomputable def leaf3852Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (81/32), kHi := (41/16), chiLo := (17/64), chiHi := (35/128) }

private noncomputable def leaf3852Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435689/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716537856) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (448877585/268435456) }, upper := { exponent := 0, mantissa := (3483/2048) } }, logOuter := sk100LogOuterCertificate, logK := sk100LogKCertificate, logChi := chi243LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435031551/137433075712) } }, logDArg := sk100LogDArgCertificate }

private noncomputable def leaf3852InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf3852LocalValidity :
    LeafFacts leaf3852Box leaf3852Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3852Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716537856) }) = true
      norm_num [leaf3852Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3852CertificateValid :
    WideCertificateValid leaf3852Box leaf3852Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk100ValidityFacts chi243ValidityFacts
    leaf3852LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3852CoverageChecked :
    coverageCheck (innerAD leaf3852Box) leaf3852InnerLog = true := by
  rfl'

private theorem leaf3852InnerLogValid :
    leaf3852InnerLog.Valid 8 (innerAD leaf3852Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf3852CoverageChecked

private noncomputable def leaf3852InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453665/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3852InputLogOnePlusV_eq :
    leaf3852InputLogOnePlusV = outerEnclosure 24
      (leaf3852Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3852RoundedFacts : LeafRoundedFacts 8
    leaf3852Certificate.logOnePlusV leaf3852InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3852InputLogOnePlusV_eq }

private noncomputable def leaf3852Inputs : Inputs :=
  inputsOfCaches globalInput sk100RoundedInputs
    chi243InputQChi innerPair57Input
    leaf3852InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3852LowerChecked :
    lowerCheck 24 leaf3852Box leaf3852Inputs = true := by
  rfl'

private theorem leaf3852CoversExact : CoversExact 8
    leaf3852Box leaf3852Certificate leaf3852InnerLog leaf3852Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk100RoundedFacts chi243RoundedFacts
    innerPair57RoundedFacts leaf3852RoundedFacts (by rfl)

private theorem leaf3852FlatSound : Sound leaf3852Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3852CertificateValid
    leaf3852InnerLogValid leaf3852CoversExact leaf3852LowerChecked

private noncomputable def leaf3853Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (81/32), kHi := (41/16), chiLo := (35/128), chiHi := (9/32) }

private noncomputable def leaf3853Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435691/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716453888) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (454185675/268435456) }, upper := { exponent := 0, mantissa := (881/512) } }, logOuter := sk100LogOuterCertificate, logK := sk100LogKCertificate, logChi := chi244LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434947583/137432907776) } }, logDArg := sk100LogDArgCertificate }

private noncomputable def leaf3853InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3853LocalValidity :
    LeafFacts leaf3853Box leaf3853Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3853Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716453888) }) = true
      norm_num [leaf3853Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3853CertificateValid :
    WideCertificateValid leaf3853Box leaf3853Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk100ValidityFacts chi244ValidityFacts
    leaf3853LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3853CoverageChecked :
    coverageCheck (innerAD leaf3853Box) leaf3853InnerLog = true := by
  rfl'

private theorem leaf3853InnerLogValid :
    leaf3853InnerLog.Valid 8 (innerAD leaf3853Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3853CoverageChecked

private noncomputable def leaf3853InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814665/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3853InputLogOnePlusV_eq :
    leaf3853InputLogOnePlusV = outerEnclosure 24
      (leaf3853Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3853RoundedFacts : LeafRoundedFacts 8
    leaf3853Certificate.logOnePlusV leaf3853InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3853InputLogOnePlusV_eq }

private noncomputable def leaf3853Inputs : Inputs :=
  inputsOfCaches globalInput sk100RoundedInputs
    chi244InputQChi innerPair64Input
    leaf3853InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3853LowerChecked :
    lowerCheck 24 leaf3853Box leaf3853Inputs = true := by
  rfl'

private theorem leaf3853CoversExact : CoversExact 8
    leaf3853Box leaf3853Certificate leaf3853InnerLog leaf3853Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk100RoundedFacts chi244RoundedFacts
    innerPair64RoundedFacts leaf3853RoundedFacts (by rfl)

private theorem leaf3853FlatSound : Sound leaf3853Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3853CertificateValid
    leaf3853InnerLogValid leaf3853CoversExact leaf3853LowerChecked

private noncomputable def leaf3854Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (83/32), chiLo := (1/4), chiHi := (33/128) }

private noncomputable def leaf3854Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435687/268435456) }, vSqrt := { lower := (32765/32768), upper := (13743698739/13743334400) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (440358427/268435456) }, upper := { exponent := 0, mantissa := (6835/4096) } }, logOuter := sk101LogOuterCertificate, logK := sk101LogKCertificate, logChi := chi241LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (27487033139/27486668800) } }, logDArg := sk101LogDArgCertificate }

private noncomputable def leaf3854InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf3854LocalValidity :
    LeafFacts leaf3854Box leaf3854Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3854Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (13743698739/13743334400) }) = true
      norm_num [leaf3854Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3854CertificateValid :
    WideCertificateValid leaf3854Box leaf3854Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk101ValidityFacts chi241ValidityFacts
    leaf3854LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3854CoverageChecked :
    coverageCheck (innerAD leaf3854Box) leaf3854InnerLog = true := by
  rfl'

private theorem leaf3854InnerLogValid :
    leaf3854InnerLog.Valid 8 (innerAD leaf3854Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf3854CoverageChecked

private noncomputable def leaf3854InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629303/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3854InputLogOnePlusV_eq :
    leaf3854InputLogOnePlusV = outerEnclosure 24
      (leaf3854Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3854RoundedFacts : LeafRoundedFacts 8
    leaf3854Certificate.logOnePlusV leaf3854InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3854InputLogOnePlusV_eq }

private noncomputable def leaf3854Inputs : Inputs :=
  inputsOfCaches globalInput sk101RoundedInputs
    chi241InputQChi innerPair56Input
    leaf3854InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3854LowerChecked :
    lowerCheck 24 leaf3854Box leaf3854Inputs = true := by
  rfl'

private theorem leaf3854CoversExact : CoversExact 8
    leaf3854Box leaf3854Certificate leaf3854InnerLog leaf3854Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk101RoundedFacts chi241RoundedFacts
    innerPair56RoundedFacts leaf3854RoundedFacts (by rfl)

private theorem leaf3854FlatSound : Sound leaf3854Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3854CertificateValid
    leaf3854InnerLogValid leaf3854CoversExact leaf3854LowerChecked

private noncomputable def leaf3855Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (83/32), chiLo := (33/128), chiHi := (17/64) }

private noncomputable def leaf3855Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435689/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716587008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (445732049/268435456) }, upper := { exponent := 0, mantissa := (3459/2048) } }, logOuter := sk101LogOuterCertificate, logK := sk101LogKCertificate, logChi := chi242LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435080703/137433174016) } }, logDArg := sk101LogDArgCertificate }

private noncomputable def leaf3855InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf3855LocalValidity :
    LeafFacts leaf3855Box leaf3855Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3855Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716587008) }) = true
      norm_num [leaf3855Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3855CertificateValid :
    WideCertificateValid leaf3855Box leaf3855Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk101ValidityFacts chi242ValidityFacts
    leaf3855LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3855CoverageChecked :
    coverageCheck (innerAD leaf3855Box) leaf3855InnerLog = true := by
  rfl'

private theorem leaf3855InnerLogValid :
    leaf3855InnerLog.Valid 8 (innerAD leaf3855Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf3855CoverageChecked

private noncomputable def leaf3855InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814657/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3855InputLogOnePlusV_eq :
    leaf3855InputLogOnePlusV = outerEnclosure 24
      (leaf3855Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3855RoundedFacts : LeafRoundedFacts 8
    leaf3855Certificate.logOnePlusV leaf3855InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3855InputLogOnePlusV_eq }

private noncomputable def leaf3855Inputs : Inputs :=
  inputsOfCaches globalInput sk101RoundedInputs
    chi242InputQChi innerPair57Input
    leaf3855InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3855LowerChecked :
    lowerCheck 24 leaf3855Box leaf3855Inputs = true := by
  rfl'

private theorem leaf3855CoversExact : CoversExact 8
    leaf3855Box leaf3855Certificate leaf3855InnerLog leaf3855Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk101RoundedFacts chi242RoundedFacts
    innerPair57RoundedFacts leaf3855RoundedFacts (by rfl)

private theorem leaf3855FlatSound : Sound leaf3855Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3855CertificateValid
    leaf3855InnerLogValid leaf3855CoversExact leaf3855LowerChecked

private noncomputable def leaf3856Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (83/32), kHi := (21/8), chiLo := (1/4), chiHi := (33/128) }

private noncomputable def leaf3856Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435689/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716638208) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (442455449/268435456) }, upper := { exponent := 0, mantissa := (1717/1024) } }, logOuter := sk102LogOuterCertificate, logK := sk102LogKCertificate, logChi := chi241LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435131903/137433276416) } }, logDArg := sk102LogDArgCertificate }

private noncomputable def leaf3856InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf3856LocalValidity :
    LeafFacts leaf3856Box leaf3856Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3856Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716638208) }) = true
      norm_num [leaf3856Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3856CertificateValid :
    WideCertificateValid leaf3856Box leaf3856Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk102ValidityFacts chi241ValidityFacts
    leaf3856LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3856CoverageChecked :
    coverageCheck (innerAD leaf3856Box) leaf3856InnerLog = true := by
  rfl'

private theorem leaf3856InnerLogValid :
    leaf3856InnerLog.Valid 8 (innerAD leaf3856Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf3856CoverageChecked

private noncomputable def leaf3856InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629307/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3856InputLogOnePlusV_eq :
    leaf3856InputLogOnePlusV = outerEnclosure 24
      (leaf3856Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3856RoundedFacts : LeafRoundedFacts 8
    leaf3856Certificate.logOnePlusV leaf3856InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3856InputLogOnePlusV_eq }

private noncomputable def leaf3856Inputs : Inputs :=
  inputsOfCaches globalInput sk102RoundedInputs
    chi241InputQChi innerPair56Input
    leaf3856InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3856LowerChecked :
    lowerCheck 24 leaf3856Box leaf3856Inputs = true := by
  rfl'

private theorem leaf3856CoversExact : CoversExact 8
    leaf3856Box leaf3856Certificate leaf3856InnerLog leaf3856Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk102RoundedFacts chi241RoundedFacts
    innerPair56RoundedFacts leaf3856RoundedFacts (by rfl)

private theorem leaf3856FlatSound : Sound leaf3856Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3856CertificateValid
    leaf3856InnerLogValid leaf3856CoversExact leaf3856LowerChecked

private noncomputable def leaf3857Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (83/32), kHi := (21/8), chiLo := (33/128), chiHi := (17/64) }

private noncomputable def leaf3857Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435691/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716552192) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (447894603/268435456) }, upper := { exponent := 0, mantissa := (869/512) } }, logOuter := sk102LogOuterCertificate, logK := sk102LogKCertificate, logChi := chi242LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435045887/137433104384) } }, logDArg := sk102LogDArgCertificate }

private noncomputable def leaf3857InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf3857LocalValidity :
    LeafFacts leaf3857Box leaf3857Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3857Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716552192) }) = true
      norm_num [leaf3857Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3857CertificateValid :
    WideCertificateValid leaf3857Box leaf3857Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk102ValidityFacts chi242ValidityFacts
    leaf3857LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3857CoverageChecked :
    coverageCheck (innerAD leaf3857Box) leaf3857InnerLog = true := by
  rfl'

private theorem leaf3857InnerLogValid :
    leaf3857InnerLog.Valid 8 (innerAD leaf3857Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf3857CoverageChecked

private noncomputable def leaf3857InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814659/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3857InputLogOnePlusV_eq :
    leaf3857InputLogOnePlusV = outerEnclosure 24
      (leaf3857Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3857RoundedFacts : LeafRoundedFacts 8
    leaf3857Certificate.logOnePlusV leaf3857InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3857InputLogOnePlusV_eq }

private noncomputable def leaf3857Inputs : Inputs :=
  inputsOfCaches globalInput sk102RoundedInputs
    chi242InputQChi innerPair57Input
    leaf3857InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3857LowerChecked :
    lowerCheck 24 leaf3857Box leaf3857Inputs = true := by
  rfl'

private theorem leaf3857CoversExact : CoversExact 8
    leaf3857Box leaf3857Certificate leaf3857InnerLog leaf3857Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk102RoundedFacts chi242RoundedFacts
    innerPair57RoundedFacts leaf3857RoundedFacts (by rfl)

private theorem leaf3857FlatSound : Sound leaf3857Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3857CertificateValid
    leaf3857InnerLogValid leaf3857CoversExact leaf3857LowerChecked

private noncomputable def leaf3858Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (83/32), chiLo := (17/64), chiHi := (35/128) }

private noncomputable def leaf3858Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435691/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905500672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (451105671/268435456) }, upper := { exponent := 0, mantissa := (7001/4096) } }, logOuter := sk101LogOuterCertificate, logK := sk101LogKCertificate, logChi := chi243LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811665237/45811001344) } }, logDArg := sk101LogDArgCertificate }

private noncomputable def leaf3858InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf3858LocalValidity :
    LeafFacts leaf3858Box leaf3858Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3858Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905500672) }) = true
      norm_num [leaf3858Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3858CertificateValid :
    WideCertificateValid leaf3858Box leaf3858Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk101ValidityFacts chi243ValidityFacts
    leaf3858LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3858CoverageChecked :
    coverageCheck (innerAD leaf3858Box) leaf3858InnerLog = true := by
  rfl'

private theorem leaf3858InnerLogValid :
    leaf3858InnerLog.Valid 8 (innerAD leaf3858Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf3858CoverageChecked

private noncomputable def leaf3858InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907331/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3858InputLogOnePlusV_eq :
    leaf3858InputLogOnePlusV = outerEnclosure 24
      (leaf3858Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3858RoundedFacts : LeafRoundedFacts 8
    leaf3858Certificate.logOnePlusV leaf3858InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3858InputLogOnePlusV_eq }

private noncomputable def leaf3858Inputs : Inputs :=
  inputsOfCaches globalInput sk101RoundedInputs
    chi243InputQChi innerPair57Input
    leaf3858InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3858LowerChecked :
    lowerCheck 24 leaf3858Box leaf3858Inputs = true := by
  rfl'

private theorem leaf3858CoversExact : CoversExact 8
    leaf3858Box leaf3858Certificate leaf3858InnerLog leaf3858Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk101RoundedFacts chi243RoundedFacts
    innerPair57RoundedFacts leaf3858RoundedFacts (by rfl)

private theorem leaf3858FlatSound : Sound leaf3858Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3858CertificateValid
    leaf3858InnerLogValid leaf3858CoversExact leaf3858LowerChecked

private noncomputable def leaf3859Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (83/32), chiLo := (35/128), chiHi := (9/32) }

private noncomputable def leaf3859Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435693/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716417024) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (456479293/268435456) }, upper := { exponent := 0, mantissa := (1771/1024) } }, logOuter := sk101LogOuterCertificate, logK := sk101LogKCertificate, logChi := chi244LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434910719/137432834048) } }, logDArg := sk101LogDArgCertificate }

private noncomputable def leaf3859InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3859LocalValidity :
    LeafFacts leaf3859Box leaf3859Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3859Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716417024) }) = true
      norm_num [leaf3859Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3859CertificateValid :
    WideCertificateValid leaf3859Box leaf3859Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk101ValidityFacts chi244ValidityFacts
    leaf3859LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3859CoverageChecked :
    coverageCheck (innerAD leaf3859Box) leaf3859InnerLog = true := by
  rfl'

private theorem leaf3859InnerLogValid :
    leaf3859InnerLog.Valid 8 (innerAD leaf3859Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3859CoverageChecked

private noncomputable def leaf3859InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814667/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3859InputLogOnePlusV_eq :
    leaf3859InputLogOnePlusV = outerEnclosure 24
      (leaf3859Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3859RoundedFacts : LeafRoundedFacts 8
    leaf3859Certificate.logOnePlusV leaf3859InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3859InputLogOnePlusV_eq }

private noncomputable def leaf3859Inputs : Inputs :=
  inputsOfCaches globalInput sk101RoundedInputs
    chi244InputQChi innerPair64Input
    leaf3859InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3859LowerChecked :
    lowerCheck 24 leaf3859Box leaf3859Inputs = true := by
  rfl'

private theorem leaf3859CoversExact : CoversExact 8
    leaf3859Box leaf3859Certificate leaf3859InnerLog leaf3859Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk101RoundedFacts chi244RoundedFacts
    innerPair64RoundedFacts leaf3859RoundedFacts (by rfl)

private theorem leaf3859FlatSound : Sound leaf3859Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3859CertificateValid
    leaf3859InnerLogValid leaf3859CoversExact leaf3859LowerChecked

private noncomputable def leaf3860Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (83/32), kHi := (21/8), chiLo := (17/64), chiHi := (35/128) }

private noncomputable def leaf3860Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435693/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716466176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (453333757/268435456) }, upper := { exponent := 0, mantissa := (1759/1024) } }, logOuter := sk102LogOuterCertificate, logK := sk102LogKCertificate, logChi := chi243LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434959871/137432932352) } }, logDArg := sk102LogDArgCertificate }

private noncomputable def leaf3860InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3860LocalValidity :
    LeafFacts leaf3860Box leaf3860Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3860Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716466176) }) = true
      norm_num [leaf3860Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3860CertificateValid :
    WideCertificateValid leaf3860Box leaf3860Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk102ValidityFacts chi243ValidityFacts
    leaf3860LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3860CoverageChecked :
    coverageCheck (innerAD leaf3860Box) leaf3860InnerLog = true := by
  rfl'

private theorem leaf3860InnerLogValid :
    leaf3860InnerLog.Valid 8 (innerAD leaf3860Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3860CoverageChecked

private noncomputable def leaf3860InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (726833/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf3860InputLogOnePlusV_eq :
    leaf3860InputLogOnePlusV = outerEnclosure 24
      (leaf3860Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3860RoundedFacts : LeafRoundedFacts 8
    leaf3860Certificate.logOnePlusV leaf3860InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3860InputLogOnePlusV_eq }

private noncomputable def leaf3860Inputs : Inputs :=
  inputsOfCaches globalInput sk102RoundedInputs
    chi243InputQChi innerPair64Input
    leaf3860InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3860LowerChecked :
    lowerCheck 24 leaf3860Box leaf3860Inputs = true := by
  rfl'

private theorem leaf3860CoversExact : CoversExact 8
    leaf3860Box leaf3860Certificate leaf3860InnerLog leaf3860Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk102RoundedFacts chi243RoundedFacts
    innerPair64RoundedFacts leaf3860RoundedFacts (by rfl)

private theorem leaf3860FlatSound : Sound leaf3860Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3860CertificateValid
    leaf3860InnerLogValid leaf3860CoversExact leaf3860LowerChecked

private noncomputable def leaf3861Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (83/32), kHi := (21/8), chiLo := (35/128), chiHi := (9/32) }

private noncomputable def leaf3861Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435695/268435456) }, vSqrt := { lower := (32765/32768), upper := (13743698739/13743276032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (458772911/268435456) }, upper := { exponent := 0, mantissa := (445/256) } }, logOuter := sk102LogOuterCertificate, logK := sk102LogKCertificate, logChi := chi244LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (27486974771/27486552064) } }, logDArg := sk102LogDArgCertificate }

private noncomputable def leaf3861InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3861LocalValidity :
    LeafFacts leaf3861Box leaf3861Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3861Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (13743698739/13743276032) }) = true
      norm_num [leaf3861Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3861CertificateValid :
    WideCertificateValid leaf3861Box leaf3861Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk102ValidityFacts chi244ValidityFacts
    leaf3861LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3861CoverageChecked :
    coverageCheck (innerAD leaf3861Box) leaf3861InnerLog = true := by
  rfl'

private theorem leaf3861InnerLogValid :
    leaf3861InnerLog.Valid 8 (innerAD leaf3861Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3861CoverageChecked

private noncomputable def leaf3861InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629339/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3861InputLogOnePlusV_eq :
    leaf3861InputLogOnePlusV = outerEnclosure 24
      (leaf3861Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3861RoundedFacts : LeafRoundedFacts 8
    leaf3861Certificate.logOnePlusV leaf3861InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3861InputLogOnePlusV_eq }

private noncomputable def leaf3861Inputs : Inputs :=
  inputsOfCaches globalInput sk102RoundedInputs
    chi244InputQChi innerPair64Input
    leaf3861InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3861LowerChecked :
    lowerCheck 24 leaf3861Box leaf3861Inputs = true := by
  rfl'

private theorem leaf3861CoversExact : CoversExact 8
    leaf3861Box leaf3861Certificate leaf3861InnerLog leaf3861Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk102RoundedFacts chi244RoundedFacts
    innerPair64RoundedFacts leaf3861RoundedFacts (by rfl)

private theorem leaf3861FlatSound : Sound leaf3861Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3861CertificateValid
    leaf3861InnerLogValid leaf3861CoversExact leaf3861LowerChecked

private noncomputable def leaf3862Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (81/32), chiLo := (9/32), chiHi := (37/128) }

private noncomputable def leaf3862Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435691/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716407808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (457134615/268435456) }, upper := { exponent := 0, mantissa := (7093/4096) } }, logOuter := sk99LogOuterCertificate, logK := sk99LogKCertificate, logChi := chi245LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434901503/137432815616) } }, logDArg := sk99LogDArgCertificate }

private noncomputable def leaf3862InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3862LocalValidity :
    LeafFacts leaf3862Box leaf3862Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3862Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716407808) }) = true
      norm_num [leaf3862Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3862CertificateValid :
    WideCertificateValid leaf3862Box leaf3862Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk99ValidityFacts chi245ValidityFacts
    leaf3862LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3862CoverageChecked :
    coverageCheck (innerAD leaf3862Box) leaf3862InnerLog = true := by
  rfl'

private theorem leaf3862InnerLogValid :
    leaf3862InnerLog.Valid 8 (innerAD leaf3862Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3862CoverageChecked

private noncomputable def leaf3862InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629335/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3862InputLogOnePlusV_eq :
    leaf3862InputLogOnePlusV = outerEnclosure 24
      (leaf3862Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3862RoundedFacts : LeafRoundedFacts 8
    leaf3862Certificate.logOnePlusV leaf3862InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3862InputLogOnePlusV_eq }

private noncomputable def leaf3862Inputs : Inputs :=
  inputsOfCaches globalInput sk99RoundedInputs
    chi245InputQChi innerPair64Input
    leaf3862InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3862LowerChecked :
    lowerCheck 24 leaf3862Box leaf3862Inputs = true := by
  rfl'

private theorem leaf3862CoversExact : CoversExact 8
    leaf3862Box leaf3862Certificate leaf3862InnerLog leaf3862Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk99RoundedFacts chi245RoundedFacts
    innerPair64RoundedFacts leaf3862RoundedFacts (by rfl)

private theorem leaf3862FlatSound : Sound leaf3862Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3862CertificateValid
    leaf3862InnerLogValid leaf3862CoversExact leaf3862LowerChecked

private noncomputable def leaf3863Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (81/32), chiLo := (37/128), chiHi := (19/64) }

private noncomputable def leaf3863Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435693/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716324864) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (462377173/268435456) }, upper := { exponent := 0, mantissa := (3587/2048) } }, logOuter := sk99LogOuterCertificate, logK := sk99LogKCertificate, logChi := chi246LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434818559/137432649728) } }, logDArg := sk99LogDArgCertificate }

private noncomputable def leaf3863InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf3863LocalValidity :
    LeafFacts leaf3863Box leaf3863Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3863Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716324864) }) = true
      norm_num [leaf3863Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3863CertificateValid :
    WideCertificateValid leaf3863Box leaf3863Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk99ValidityFacts chi246ValidityFacts
    leaf3863LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3863CoverageChecked :
    coverageCheck (innerAD leaf3863Box) leaf3863InnerLog = true := by
  rfl'

private theorem leaf3863InnerLogValid :
    leaf3863InnerLog.Valid 8 (innerAD leaf3863Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf3863CoverageChecked

private noncomputable def leaf3863InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814673/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3863InputLogOnePlusV_eq :
    leaf3863InputLogOnePlusV = outerEnclosure 24
      (leaf3863Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3863RoundedFacts : LeafRoundedFacts 8
    leaf3863Certificate.logOnePlusV leaf3863InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3863InputLogOnePlusV_eq }

private noncomputable def leaf3863Inputs : Inputs :=
  inputsOfCaches globalInput sk99RoundedInputs
    chi246InputQChi innerPair66Input
    leaf3863InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3863LowerChecked :
    lowerCheck 24 leaf3863Box leaf3863Inputs = true := by
  rfl'

private theorem leaf3863CoversExact : CoversExact 8
    leaf3863Box leaf3863Certificate leaf3863InnerLog leaf3863Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk99RoundedFacts chi246RoundedFacts
    innerPair66RoundedFacts leaf3863RoundedFacts (by rfl)

private theorem leaf3863FlatSound : Sound leaf3863Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3863CertificateValid
    leaf3863InnerLogValid leaf3863CoversExact leaf3863LowerChecked

private noncomputable def leaf3864Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (81/32), kHi := (41/16), chiLo := (9/32), chiHi := (37/128) }

private noncomputable def leaf3864Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435693/268435456) }, vSqrt := { lower := (32765/32768), upper := (4581232913/4581091328) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (459493765/268435456) }, upper := { exponent := 0, mantissa := (3565/2048) } }, logOuter := sk100LogOuterCertificate, logK := sk100LogKCertificate, logChi := chi245LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (9162324241/9162182656) } }, logDArg := sk100LogDArgCertificate }

private noncomputable def leaf3864InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3864LocalValidity :
    LeafFacts leaf3864Box leaf3864Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3864Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4581232913/4581091328) }) = true
      norm_num [leaf3864Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3864CertificateValid :
    WideCertificateValid leaf3864Box leaf3864Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk100ValidityFacts chi245ValidityFacts
    leaf3864LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3864CoverageChecked :
    coverageCheck (innerAD leaf3864Box) leaf3864InnerLog = true := by
  rfl'

private theorem leaf3864InnerLogValid :
    leaf3864InnerLog.Valid 8 (innerAD leaf3864Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3864CoverageChecked

private noncomputable def leaf3864InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907335/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3864InputLogOnePlusV_eq :
    leaf3864InputLogOnePlusV = outerEnclosure 24
      (leaf3864Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3864RoundedFacts : LeafRoundedFacts 8
    leaf3864Certificate.logOnePlusV leaf3864InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3864InputLogOnePlusV_eq }

private noncomputable def leaf3864Inputs : Inputs :=
  inputsOfCaches globalInput sk100RoundedInputs
    chi245InputQChi innerPair64Input
    leaf3864InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3864LowerChecked :
    lowerCheck 24 leaf3864Box leaf3864Inputs = true := by
  rfl'

private theorem leaf3864CoversExact : CoversExact 8
    leaf3864Box leaf3864Certificate leaf3864InnerLog leaf3864Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk100RoundedFacts chi245RoundedFacts
    innerPair64RoundedFacts leaf3864RoundedFacts (by rfl)

private theorem leaf3864FlatSound : Sound leaf3864Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3864CertificateValid
    leaf3864InnerLogValid leaf3864CoversExact leaf3864LowerChecked

private noncomputable def leaf3865Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (81/32), kHi := (41/16), chiLo := (37/128), chiHi := (19/64) }

private noncomputable def leaf3865Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435695/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716285952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (464801855/268435456) }, upper := { exponent := 0, mantissa := (1803/1024) } }, logOuter := sk100LogOuterCertificate, logK := sk100LogKCertificate, logChi := chi246LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434779647/137432571904) } }, logDArg := sk100LogDArgCertificate }

private noncomputable def leaf3865InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf3865LocalValidity :
    LeafFacts leaf3865Box leaf3865Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3865Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716285952) }) = true
      norm_num [leaf3865Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3865CertificateValid :
    WideCertificateValid leaf3865Box leaf3865Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk100ValidityFacts chi246ValidityFacts
    leaf3865LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3865CoverageChecked :
    coverageCheck (innerAD leaf3865Box) leaf3865InnerLog = true := by
  rfl'

private theorem leaf3865InnerLogValid :
    leaf3865InnerLog.Valid 8 (innerAD leaf3865Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf3865CoverageChecked

private noncomputable def leaf3865InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814675/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3865InputLogOnePlusV_eq :
    leaf3865InputLogOnePlusV = outerEnclosure 24
      (leaf3865Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3865RoundedFacts : LeafRoundedFacts 8
    leaf3865Certificate.logOnePlusV leaf3865InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3865InputLogOnePlusV_eq }

private noncomputable def leaf3865Inputs : Inputs :=
  inputsOfCaches globalInput sk100RoundedInputs
    chi246InputQChi innerPair66Input
    leaf3865InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3865LowerChecked :
    lowerCheck 24 leaf3865Box leaf3865Inputs = true := by
  rfl'

private theorem leaf3865CoversExact : CoversExact 8
    leaf3865Box leaf3865Certificate leaf3865InnerLog leaf3865Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk100RoundedFacts chi246RoundedFacts
    innerPair66RoundedFacts leaf3865RoundedFacts (by rfl)

private theorem leaf3865FlatSound : Sound leaf3865Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3865CertificateValid
    leaf3865InnerLogValid leaf3865CoversExact leaf3865LowerChecked

private noncomputable def leaf3866Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (81/32), chiLo := (19/64), chiHi := (39/128) }

private noncomputable def leaf3866Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435695/268435456) }, vSqrt := { lower := (32765/32768), upper := (13743698739/13743248384) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (467619731/268435456) }, upper := { exponent := 0, mantissa := (7255/4096) } }, logOuter := sk99LogOuterCertificate, logK := sk99LogKCertificate, logChi := chi247LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (27486947123/27486496768) } }, logDArg := sk99LogDArgCertificate }

private noncomputable def leaf3866InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf3866LocalValidity :
    LeafFacts leaf3866Box leaf3866Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3866Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (13743698739/13743248384) }) = true
      norm_num [leaf3866Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3866CertificateValid :
    WideCertificateValid leaf3866Box leaf3866Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk99ValidityFacts chi247ValidityFacts
    leaf3866LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3866CoverageChecked :
    coverageCheck (innerAD leaf3866Box) leaf3866InnerLog = true := by
  rfl'

private theorem leaf3866InnerLogValid :
    leaf3866InnerLog.Valid 8 (innerAD leaf3866Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf3866CoverageChecked

private noncomputable def leaf3866InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907339/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3866InputLogOnePlusV_eq :
    leaf3866InputLogOnePlusV = outerEnclosure 24
      (leaf3866Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3866RoundedFacts : LeafRoundedFacts 8
    leaf3866Certificate.logOnePlusV leaf3866InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3866InputLogOnePlusV_eq }

private noncomputable def leaf3866Inputs : Inputs :=
  inputsOfCaches globalInput sk99RoundedInputs
    chi247InputQChi innerPair66Input
    leaf3866InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3866LowerChecked :
    lowerCheck 24 leaf3866Box leaf3866Inputs = true := by
  rfl'

private theorem leaf3866CoversExact : CoversExact 8
    leaf3866Box leaf3866Certificate leaf3866InnerLog leaf3866Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk99RoundedFacts chi247RoundedFacts
    innerPair66RoundedFacts leaf3866RoundedFacts (by rfl)

private theorem leaf3866FlatSound : Sound leaf3866Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3866CertificateValid
    leaf3866InnerLogValid leaf3866CoversExact leaf3866LowerChecked

private noncomputable def leaf3867Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (81/32), chiLo := (39/128), chiHi := (5/16) }

private noncomputable def leaf3867Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435697/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716158976) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (472862289/268435456) }, upper := { exponent := 0, mantissa := (917/512) } }, logOuter := sk99LogOuterCertificate, logK := sk99LogKCertificate, logChi := chi248LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434652671/137432317952) } }, logDArg := sk99LogDArgCertificate }

private noncomputable def leaf3867InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3867LocalValidity :
    LeafFacts leaf3867Box leaf3867Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3867Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716158976) }) = true
      norm_num [leaf3867Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3867CertificateValid :
    WideCertificateValid leaf3867Box leaf3867Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk99ValidityFacts chi248ValidityFacts
    leaf3867LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3867CoverageChecked :
    coverageCheck (innerAD leaf3867Box) leaf3867InnerLog = true := by
  rfl'

private theorem leaf3867InnerLogValid :
    leaf3867InnerLog.Valid 8 (innerAD leaf3867Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3867CoverageChecked

private noncomputable def leaf3867InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814683/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3867InputLogOnePlusV_eq :
    leaf3867InputLogOnePlusV = outerEnclosure 24
      (leaf3867Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3867RoundedFacts : LeafRoundedFacts 8
    leaf3867Certificate.logOnePlusV leaf3867InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3867InputLogOnePlusV_eq }

private noncomputable def leaf3867Inputs : Inputs :=
  inputsOfCaches globalInput sk99RoundedInputs
    chi248InputQChi innerPair71Input
    leaf3867InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3867LowerChecked :
    lowerCheck 24 leaf3867Box leaf3867Inputs = true := by
  rfl'

private theorem leaf3867CoversExact : CoversExact 8
    leaf3867Box leaf3867Certificate leaf3867InnerLog leaf3867Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk99RoundedFacts chi248RoundedFacts
    innerPair71RoundedFacts leaf3867RoundedFacts (by rfl)

private theorem leaf3867FlatSound : Sound leaf3867Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3867CertificateValid
    leaf3867InnerLogValid leaf3867CoversExact leaf3867LowerChecked

private noncomputable def leaf3868Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (81/32), kHi := (41/16), chiLo := (19/64), chiHi := (39/128) }

private noncomputable def leaf3868Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435697/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716201984) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (470109945/268435456) }, upper := { exponent := 0, mantissa := (3647/2048) } }, logOuter := sk100LogOuterCertificate, logK := sk100LogKCertificate, logChi := chi247LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434695679/137432403968) } }, logDArg := sk100LogDArgCertificate }

private noncomputable def leaf3868InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3868LocalValidity :
    LeafFacts leaf3868Box leaf3868Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3868Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716201984) }) = true
      norm_num [leaf3868Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3868CertificateValid :
    WideCertificateValid leaf3868Box leaf3868Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk100ValidityFacts chi247ValidityFacts
    leaf3868LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3868CoverageChecked :
    coverageCheck (innerAD leaf3868Box) leaf3868InnerLog = true := by
  rfl'

private theorem leaf3868InnerLogValid :
    leaf3868InnerLog.Valid 8 (innerAD leaf3868Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3868CoverageChecked

private noncomputable def leaf3868InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629361/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3868InputLogOnePlusV_eq :
    leaf3868InputLogOnePlusV = outerEnclosure 24
      (leaf3868Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3868RoundedFacts : LeafRoundedFacts 8
    leaf3868Certificate.logOnePlusV leaf3868InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3868InputLogOnePlusV_eq }

private noncomputable def leaf3868Inputs : Inputs :=
  inputsOfCaches globalInput sk100RoundedInputs
    chi247InputQChi innerPair71Input
    leaf3868InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3868LowerChecked :
    lowerCheck 24 leaf3868Box leaf3868Inputs = true := by
  rfl'

private theorem leaf3868CoversExact : CoversExact 8
    leaf3868Box leaf3868Certificate leaf3868InnerLog leaf3868Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk100RoundedFacts chi247RoundedFacts
    innerPair71RoundedFacts leaf3868RoundedFacts (by rfl)

private theorem leaf3868FlatSound : Sound leaf3868Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3868CertificateValid
    leaf3868InnerLogValid leaf3868CoversExact leaf3868LowerChecked

private noncomputable def leaf3869Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (81/32), kHi := (41/16), chiLo := (39/128), chiHi := (5/16) }

private noncomputable def leaf3869Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435699/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905372672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (475418035/268435456) }, upper := { exponent := 0, mantissa := (461/256) } }, logOuter := sk100LogOuterCertificate, logK := sk100LogKCertificate, logChi := chi248LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811537237/45810745344) } }, logDArg := sk100LogDArgCertificate }

private noncomputable def leaf3869InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3869LocalValidity :
    LeafFacts leaf3869Box leaf3869Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3869Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905372672) }) = true
      norm_num [leaf3869Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3869CertificateValid :
    WideCertificateValid leaf3869Box leaf3869Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk100ValidityFacts chi248ValidityFacts
    leaf3869LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3869CoverageChecked :
    coverageCheck (innerAD leaf3869Box) leaf3869InnerLog = true := by
  rfl'

private theorem leaf3869InnerLogValid :
    leaf3869InnerLog.Valid 8 (innerAD leaf3869Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3869CoverageChecked

private noncomputable def leaf3869InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629371/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3869InputLogOnePlusV_eq :
    leaf3869InputLogOnePlusV = outerEnclosure 24
      (leaf3869Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3869RoundedFacts : LeafRoundedFacts 8
    leaf3869Certificate.logOnePlusV leaf3869InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3869InputLogOnePlusV_eq }

private noncomputable def leaf3869Inputs : Inputs :=
  inputsOfCaches globalInput sk100RoundedInputs
    chi248InputQChi innerPair71Input
    leaf3869InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3869LowerChecked :
    lowerCheck 24 leaf3869Box leaf3869Inputs = true := by
  rfl'

private theorem leaf3869CoversExact : CoversExact 8
    leaf3869Box leaf3869Certificate leaf3869InnerLog leaf3869Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk100RoundedFacts chi248RoundedFacts
    innerPair71RoundedFacts leaf3869RoundedFacts (by rfl)

private theorem leaf3869FlatSound : Sound leaf3869Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3869CertificateValid
    leaf3869InnerLogValid leaf3869CoversExact leaf3869LowerChecked

private noncomputable def leaf3870Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (83/32), chiLo := (9/32), chiHi := (37/128) }

private noncomputable def leaf3870Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435695/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716332032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (461852915/268435456) }, upper := { exponent := 0, mantissa := (7167/4096) } }, logOuter := sk101LogOuterCertificate, logK := sk101LogKCertificate, logChi := chi245LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434825727/137432664064) } }, logDArg := sk101LogDArgCertificate }

private noncomputable def leaf3870InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3870LocalValidity :
    LeafFacts leaf3870Box leaf3870Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3870Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716332032) }) = true
      norm_num [leaf3870Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3870CertificateValid :
    WideCertificateValid leaf3870Box leaf3870Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk101ValidityFacts chi245ValidityFacts
    leaf3870LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3870CoverageChecked :
    coverageCheck (innerAD leaf3870Box) leaf3870InnerLog = true := by
  rfl'

private theorem leaf3870InnerLogValid :
    leaf3870InnerLog.Valid 8 (innerAD leaf3870Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3870CoverageChecked

private noncomputable def leaf3870InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629345/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3870InputLogOnePlusV_eq :
    leaf3870InputLogOnePlusV = outerEnclosure 24
      (leaf3870Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3870RoundedFacts : LeafRoundedFacts 8
    leaf3870Certificate.logOnePlusV leaf3870InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3870InputLogOnePlusV_eq }

private noncomputable def leaf3870Inputs : Inputs :=
  inputsOfCaches globalInput sk101RoundedInputs
    chi245InputQChi innerPair64Input
    leaf3870InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3870LowerChecked :
    lowerCheck 24 leaf3870Box leaf3870Inputs = true := by
  rfl'

private theorem leaf3870CoversExact : CoversExact 8
    leaf3870Box leaf3870Certificate leaf3870InnerLog leaf3870Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk101RoundedFacts chi245RoundedFacts
    innerPair64RoundedFacts leaf3870RoundedFacts (by rfl)

private theorem leaf3870FlatSound : Sound leaf3870Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3870CertificateValid
    leaf3870InnerLogValid leaf3870CoversExact leaf3870LowerChecked

private noncomputable def leaf3871Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (83/32), chiLo := (37/128), chiHi := (19/64) }

private noncomputable def leaf3871Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435697/268435456) }, vSqrt := { lower := (32765/32768), upper := (4581232913/4581083136) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (467226537/268435456) }, upper := { exponent := 0, mantissa := (3625/2048) } }, logOuter := sk101LogOuterCertificate, logK := sk101LogKCertificate, logChi := chi246LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (9162316049/9162166272) } }, logDArg := sk101LogDArgCertificate }

private noncomputable def leaf3871InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf3871LocalValidity :
    LeafFacts leaf3871Box leaf3871Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3871Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4581232913/4581083136) }) = true
      norm_num [leaf3871Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3871CertificateValid :
    WideCertificateValid leaf3871Box leaf3871Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk101ValidityFacts chi246ValidityFacts
    leaf3871LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3871CoverageChecked :
    coverageCheck (innerAD leaf3871Box) leaf3871InnerLog = true := by
  rfl'

private theorem leaf3871InnerLogValid :
    leaf3871InnerLog.Valid 8 (innerAD leaf3871Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf3871CoverageChecked

private noncomputable def leaf3871InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629355/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3871InputLogOnePlusV_eq :
    leaf3871InputLogOnePlusV = outerEnclosure 24
      (leaf3871Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3871RoundedFacts : LeafRoundedFacts 8
    leaf3871Certificate.logOnePlusV leaf3871InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3871InputLogOnePlusV_eq }

private noncomputable def leaf3871Inputs : Inputs :=
  inputsOfCaches globalInput sk101RoundedInputs
    chi246InputQChi innerPair66Input
    leaf3871InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3871LowerChecked :
    lowerCheck 24 leaf3871Box leaf3871Inputs = true := by
  rfl'

private theorem leaf3871CoversExact : CoversExact 8
    leaf3871Box leaf3871Certificate leaf3871InnerLog leaf3871Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk101RoundedFacts chi246RoundedFacts
    innerPair66RoundedFacts leaf3871RoundedFacts (by rfl)

private theorem leaf3871FlatSound : Sound leaf3871Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3871CertificateValid
    leaf3871InnerLogValid leaf3871CoversExact leaf3871LowerChecked

private noncomputable def leaf3872Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (83/32), kHi := (21/8), chiLo := (9/32), chiHi := (37/128) }

private noncomputable def leaf3872Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435697/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716294144) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (464212065/268435456) }, upper := { exponent := 0, mantissa := (1801/1024) } }, logOuter := sk102LogOuterCertificate, logK := sk102LogKCertificate, logChi := chi245LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434787839/137432588288) } }, logDArg := sk102LogDArgCertificate }

private noncomputable def leaf3872InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf3872LocalValidity :
    LeafFacts leaf3872Box leaf3872Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3872Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716294144) }) = true
      norm_num [leaf3872Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3872CertificateValid :
    WideCertificateValid leaf3872Box leaf3872Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk102ValidityFacts chi245ValidityFacts
    leaf3872LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3872CoverageChecked :
    coverageCheck (innerAD leaf3872Box) leaf3872InnerLog = true := by
  rfl'

private theorem leaf3872InnerLogValid :
    leaf3872InnerLog.Valid 8 (innerAD leaf3872Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf3872CoverageChecked

private noncomputable def leaf3872InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629349/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3872InputLogOnePlusV_eq :
    leaf3872InputLogOnePlusV = outerEnclosure 24
      (leaf3872Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3872RoundedFacts : LeafRoundedFacts 8
    leaf3872Certificate.logOnePlusV leaf3872InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3872InputLogOnePlusV_eq }

private noncomputable def leaf3872Inputs : Inputs :=
  inputsOfCaches globalInput sk102RoundedInputs
    chi245InputQChi innerPair66Input
    leaf3872InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3872LowerChecked :
    lowerCheck 24 leaf3872Box leaf3872Inputs = true := by
  rfl'

private theorem leaf3872CoversExact : CoversExact 8
    leaf3872Box leaf3872Certificate leaf3872InnerLog leaf3872Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk102RoundedFacts chi245RoundedFacts
    innerPair66RoundedFacts leaf3872RoundedFacts (by rfl)

private theorem leaf3872FlatSound : Sound leaf3872Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3872CertificateValid
    leaf3872InnerLogValid leaf3872CoversExact leaf3872LowerChecked

private noncomputable def leaf3873Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (83/32), kHi := (21/8), chiLo := (37/128), chiHi := (19/64) }

private noncomputable def leaf3873Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435699/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716208128) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (469651219/268435456) }, upper := { exponent := 0, mantissa := (911/512) } }, logOuter := sk102LogOuterCertificate, logK := sk102LogKCertificate, logChi := chi246LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434701823/137432416256) } }, logDArg := sk102LogDArgCertificate }

private noncomputable def leaf3873InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf3873LocalValidity :
    LeafFacts leaf3873Box leaf3873Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3873Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716208128) }) = true
      norm_num [leaf3873Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3873CertificateValid :
    WideCertificateValid leaf3873Box leaf3873Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk102ValidityFacts chi246ValidityFacts
    leaf3873LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3873CoverageChecked :
    coverageCheck (innerAD leaf3873Box) leaf3873InnerLog = true := by
  rfl'

private theorem leaf3873InnerLogValid :
    leaf3873InnerLog.Valid 8 (innerAD leaf3873Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf3873CoverageChecked

private noncomputable def leaf3873InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (726835/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf3873InputLogOnePlusV_eq :
    leaf3873InputLogOnePlusV = outerEnclosure 24
      (leaf3873Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3873RoundedFacts : LeafRoundedFacts 8
    leaf3873Certificate.logOnePlusV leaf3873InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3873InputLogOnePlusV_eq }

private noncomputable def leaf3873Inputs : Inputs :=
  inputsOfCaches globalInput sk102RoundedInputs
    chi246InputQChi innerPair66Input
    leaf3873InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3873LowerChecked :
    lowerCheck 24 leaf3873Box leaf3873Inputs = true := by
  rfl'

private theorem leaf3873CoversExact : CoversExact 8
    leaf3873Box leaf3873Certificate leaf3873InnerLog leaf3873Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk102RoundedFacts chi246RoundedFacts
    innerPair66RoundedFacts leaf3873RoundedFacts (by rfl)

private theorem leaf3873FlatSound : Sound leaf3873Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3873CertificateValid
    leaf3873InnerLogValid leaf3873CoversExact leaf3873LowerChecked

private noncomputable def leaf3874Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (83/32), chiLo := (19/64), chiHi := (39/128) }

private noncomputable def leaf3874Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435699/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716162048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (472600159/268435456) }, upper := { exponent := 0, mantissa := (7333/4096) } }, logOuter := sk101LogOuterCertificate, logK := sk101LogKCertificate, logChi := chi247LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434655743/137432324096) } }, logDArg := sk101LogDArgCertificate }

private noncomputable def leaf3874InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3874LocalValidity :
    LeafFacts leaf3874Box leaf3874Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3874Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716162048) }) = true
      norm_num [leaf3874Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3874CertificateValid :
    WideCertificateValid leaf3874Box leaf3874Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk101ValidityFacts chi247ValidityFacts
    leaf3874LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3874CoverageChecked :
    coverageCheck (innerAD leaf3874Box) leaf3874InnerLog = true := by
  rfl'

private theorem leaf3874InnerLogValid :
    leaf3874InnerLog.Valid 8 (innerAD leaf3874Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3874CoverageChecked

private noncomputable def leaf3874InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629365/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3874InputLogOnePlusV_eq :
    leaf3874InputLogOnePlusV = outerEnclosure 24
      (leaf3874Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3874RoundedFacts : LeafRoundedFacts 8
    leaf3874Certificate.logOnePlusV leaf3874InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3874InputLogOnePlusV_eq }

private noncomputable def leaf3874Inputs : Inputs :=
  inputsOfCaches globalInput sk101RoundedInputs
    chi247InputQChi innerPair71Input
    leaf3874InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3874LowerChecked :
    lowerCheck 24 leaf3874Box leaf3874Inputs = true := by
  rfl'

private theorem leaf3874CoversExact : CoversExact 8
    leaf3874Box leaf3874Certificate leaf3874InnerLog leaf3874Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk101RoundedFacts chi247RoundedFacts
    innerPair71RoundedFacts leaf3874RoundedFacts (by rfl)

private theorem leaf3874FlatSound : Sound leaf3874Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3874CertificateValid
    leaf3874InnerLogValid leaf3874CoversExact leaf3874LowerChecked

private noncomputable def leaf3875Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (83/32), chiLo := (39/128), chiHi := (5/16) }

private noncomputable def leaf3875Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435701/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716077056) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (477973781/268435456) }, upper := { exponent := 0, mantissa := (927/512) } }, logOuter := sk101LogOuterCertificate, logK := sk101LogKCertificate, logChi := chi248LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434570751/137432154112) } }, logDArg := sk101LogDArgCertificate }

private noncomputable def leaf3875InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3875LocalValidity :
    LeafFacts leaf3875Box leaf3875Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3875Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716077056) }) = true
      norm_num [leaf3875Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3875CertificateValid :
    WideCertificateValid leaf3875Box leaf3875Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk101ValidityFacts chi248ValidityFacts
    leaf3875LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3875CoverageChecked :
    coverageCheck (innerAD leaf3875Box) leaf3875InnerLog = true := by
  rfl'

private theorem leaf3875InnerLogValid :
    leaf3875InnerLog.Valid 8 (innerAD leaf3875Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3875CoverageChecked

private noncomputable def leaf3875InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (181709/262144) }

set_option maxRecDepth 1000000 in
private theorem leaf3875InputLogOnePlusV_eq :
    leaf3875InputLogOnePlusV = outerEnclosure 24
      (leaf3875Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3875RoundedFacts : LeafRoundedFacts 8
    leaf3875Certificate.logOnePlusV leaf3875InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3875InputLogOnePlusV_eq }

private noncomputable def leaf3875Inputs : Inputs :=
  inputsOfCaches globalInput sk101RoundedInputs
    chi248InputQChi innerPair71Input
    leaf3875InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3875LowerChecked :
    lowerCheck 24 leaf3875Box leaf3875Inputs = true := by
  rfl'

private theorem leaf3875CoversExact : CoversExact 8
    leaf3875Box leaf3875Certificate leaf3875InnerLog leaf3875Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk101RoundedFacts chi248RoundedFacts
    innerPair71RoundedFacts leaf3875RoundedFacts (by rfl)

private theorem leaf3875FlatSound : Sound leaf3875Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3875CertificateValid
    leaf3875InnerLogValid leaf3875CoversExact leaf3875LowerChecked

private noncomputable def leaf3876Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (83/32), kHi := (21/8), chiLo := (19/64), chiHi := (39/128) }

private noncomputable def leaf3876Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435701/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716122112) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (475090373/268435456) }, upper := { exponent := 0, mantissa := (1843/1024) } }, logOuter := sk102LogOuterCertificate, logK := sk102LogKCertificate, logChi := chi247LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434615807/137432244224) } }, logDArg := sk102LogDArgCertificate }

private noncomputable def leaf3876InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3876LocalValidity :
    LeafFacts leaf3876Box leaf3876Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3876Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716122112) }) = true
      norm_num [leaf3876Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3876CertificateValid :
    WideCertificateValid leaf3876Box leaf3876Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk102ValidityFacts chi247ValidityFacts
    leaf3876LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3876CoverageChecked :
    coverageCheck (innerAD leaf3876Box) leaf3876InnerLog = true := by
  rfl'

private theorem leaf3876InnerLogValid :
    leaf3876InnerLog.Valid 8 (innerAD leaf3876Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3876CoverageChecked

private noncomputable def leaf3876InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814685/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3876InputLogOnePlusV_eq :
    leaf3876InputLogOnePlusV = outerEnclosure 24
      (leaf3876Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3876RoundedFacts : LeafRoundedFacts 8
    leaf3876Certificate.logOnePlusV leaf3876InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3876InputLogOnePlusV_eq }

private noncomputable def leaf3876Inputs : Inputs :=
  inputsOfCaches globalInput sk102RoundedInputs
    chi247InputQChi innerPair71Input
    leaf3876InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3876LowerChecked :
    lowerCheck 24 leaf3876Box leaf3876Inputs = true := by
  rfl'

private theorem leaf3876CoversExact : CoversExact 8
    leaf3876Box leaf3876Certificate leaf3876InnerLog leaf3876Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk102RoundedFacts chi247RoundedFacts
    innerPair71RoundedFacts leaf3876RoundedFacts (by rfl)

private theorem leaf3876FlatSound : Sound leaf3876Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3876CertificateValid
    leaf3876InnerLogValid leaf3876CoversExact leaf3876LowerChecked

private noncomputable def leaf3877Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (83/32), kHi := (21/8), chiLo := (39/128), chiHi := (5/16) }

private noncomputable def leaf3877Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435703/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716036096) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (480529527/268435456) }, upper := { exponent := 0, mantissa := (233/128) } }, logOuter := sk102LogOuterCertificate, logK := sk102LogKCertificate, logChi := chi248LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434529791/137432072192) } }, logDArg := sk102LogDArgCertificate }

private noncomputable def leaf3877InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf3877LocalValidity :
    LeafFacts leaf3877Box leaf3877Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3877Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716036096) }) = true
      norm_num [leaf3877Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3877CertificateValid :
    WideCertificateValid leaf3877Box leaf3877Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk102ValidityFacts chi248ValidityFacts
    leaf3877LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3877CoverageChecked :
    coverageCheck (innerAD leaf3877Box) leaf3877InnerLog = true := by
  rfl'

private theorem leaf3877InnerLogValid :
    leaf3877InnerLog.Valid 8 (innerAD leaf3877Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf3877CoverageChecked

private noncomputable def leaf3877InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629381/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3877InputLogOnePlusV_eq :
    leaf3877InputLogOnePlusV = outerEnclosure 24
      (leaf3877Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3877RoundedFacts : LeafRoundedFacts 8
    leaf3877Certificate.logOnePlusV leaf3877InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3877InputLogOnePlusV_eq }

private noncomputable def leaf3877Inputs : Inputs :=
  inputsOfCaches globalInput sk102RoundedInputs
    chi248InputQChi innerPair72Input
    leaf3877InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3877LowerChecked :
    lowerCheck 24 leaf3877Box leaf3877Inputs = true := by
  rfl'

private theorem leaf3877CoversExact : CoversExact 8
    leaf3877Box leaf3877Certificate leaf3877InnerLog leaf3877Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk102RoundedFacts chi248RoundedFacts
    innerPair72RoundedFacts leaf3877RoundedFacts (by rfl)

private theorem leaf3877FlatSound : Sound leaf3877Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3877CertificateValid
    leaf3877InnerLogValid leaf3877CoversExact leaf3877LowerChecked

private noncomputable def leaf3878Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (85/32), chiLo := (1/4), chiHi := (33/128) }

private noncomputable def leaf3878Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435691/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716604416) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (444552471/268435456) }, upper := { exponent := 0, mantissa := (6901/4096) } }, logOuter := sk105LogOuterCertificate, logK := sk105LogKCertificate, logChi := chi241LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435098111/137433208832) } }, logDArg := sk105LogDArgCertificate }

private noncomputable def leaf3878InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf3878LocalValidity :
    LeafFacts leaf3878Box leaf3878Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3878Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716604416) }) = true
      norm_num [leaf3878Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3878CertificateValid :
    WideCertificateValid leaf3878Box leaf3878Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk105ValidityFacts chi241ValidityFacts
    leaf3878LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3878CoverageChecked :
    coverageCheck (innerAD leaf3878Box) leaf3878InnerLog = true := by
  rfl'

private theorem leaf3878InnerLogValid :
    leaf3878InnerLog.Valid 8 (innerAD leaf3878Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf3878CoverageChecked

private noncomputable def leaf3878InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629311/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3878InputLogOnePlusV_eq :
    leaf3878InputLogOnePlusV = outerEnclosure 24
      (leaf3878Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3878RoundedFacts : LeafRoundedFacts 8
    leaf3878Certificate.logOnePlusV leaf3878InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3878InputLogOnePlusV_eq }

private noncomputable def leaf3878Inputs : Inputs :=
  inputsOfCaches globalInput sk105RoundedInputs
    chi241InputQChi innerPair56Input
    leaf3878InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3878LowerChecked :
    lowerCheck 24 leaf3878Box leaf3878Inputs = true := by
  rfl'

private theorem leaf3878CoversExact : CoversExact 8
    leaf3878Box leaf3878Certificate leaf3878InnerLog leaf3878Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk105RoundedFacts chi241RoundedFacts
    innerPair56RoundedFacts leaf3878RoundedFacts (by rfl)

private theorem leaf3878FlatSound : Sound leaf3878Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3878CertificateValid
    leaf3878InnerLogValid leaf3878CoversExact leaf3878LowerChecked

private noncomputable def leaf3879Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (85/32), chiLo := (33/128), chiHi := (17/64) }

private noncomputable def leaf3879Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435693/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905505792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (450057157/268435456) }, upper := { exponent := 0, mantissa := (3493/2048) } }, logOuter := sk105LogOuterCertificate, logK := sk105LogKCertificate, logChi := chi242LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811670357/45811011584) } }, logDArg := sk105LogDArgCertificate }

private noncomputable def leaf3879InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf3879LocalValidity :
    LeafFacts leaf3879Box leaf3879Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3879Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905505792) }) = true
      norm_num [leaf3879Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3879CertificateValid :
    WideCertificateValid leaf3879Box leaf3879Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk105ValidityFacts chi242ValidityFacts
    leaf3879LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3879CoverageChecked :
    coverageCheck (innerAD leaf3879Box) leaf3879InnerLog = true := by
  rfl'

private theorem leaf3879InnerLogValid :
    leaf3879InnerLog.Valid 8 (innerAD leaf3879Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf3879CoverageChecked

private noncomputable def leaf3879InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814661/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3879InputLogOnePlusV_eq :
    leaf3879InputLogOnePlusV = outerEnclosure 24
      (leaf3879Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3879RoundedFacts : LeafRoundedFacts 8
    leaf3879Certificate.logOnePlusV leaf3879InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3879InputLogOnePlusV_eq }

private noncomputable def leaf3879Inputs : Inputs :=
  inputsOfCaches globalInput sk105RoundedInputs
    chi242InputQChi innerPair57Input
    leaf3879InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3879LowerChecked :
    lowerCheck 24 leaf3879Box leaf3879Inputs = true := by
  rfl'

private theorem leaf3879CoversExact : CoversExact 8
    leaf3879Box leaf3879Certificate leaf3879InnerLog leaf3879Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk105RoundedFacts chi242RoundedFacts
    innerPair57RoundedFacts leaf3879RoundedFacts (by rfl)

private theorem leaf3879FlatSound : Sound leaf3879Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3879CertificateValid
    leaf3879InnerLogValid leaf3879CoversExact leaf3879LowerChecked

private noncomputable def leaf3880Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (85/32), kHi := (43/16), chiLo := (1/4), chiHi := (33/128) }

private noncomputable def leaf3880Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435693/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716570624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (446649493/268435456) }, upper := { exponent := 0, mantissa := (3467/2048) } }, logOuter := sk106LogOuterCertificate, logK := sk106LogKCertificate, logChi := chi241LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435064319/137433141248) } }, logDArg := sk106LogDArgCertificate }

private noncomputable def leaf3880InnerLog : WideLogData :=
  innerPair173Data

set_option maxRecDepth 1000000 in
private theorem leaf3880LocalValidity :
    LeafFacts leaf3880Box leaf3880Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3880Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716570624) }) = true
      norm_num [leaf3880Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3880CertificateValid :
    WideCertificateValid leaf3880Box leaf3880Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk106ValidityFacts chi241ValidityFacts
    leaf3880LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3880CoverageChecked :
    coverageCheck (innerAD leaf3880Box) leaf3880InnerLog = true := by
  rfl'

private theorem leaf3880InnerLogValid :
    leaf3880InnerLog.Valid 8 (innerAD leaf3880Box) :=
  wideLogDataValid_of_cachedCheck endpoint48PositiveFacts
    endpoint20PositiveFacts.valid leaf3880CoverageChecked

private noncomputable def leaf3880InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907329/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3880InputLogOnePlusV_eq :
    leaf3880InputLogOnePlusV = outerEnclosure 24
      (leaf3880Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3880RoundedFacts : LeafRoundedFacts 8
    leaf3880Certificate.logOnePlusV leaf3880InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3880InputLogOnePlusV_eq }

private noncomputable def leaf3880Inputs : Inputs :=
  inputsOfCaches globalInput sk106RoundedInputs
    chi241InputQChi innerPair173Input
    leaf3880InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3880LowerChecked :
    lowerCheck 24 leaf3880Box leaf3880Inputs = true := by
  rfl'

private theorem leaf3880CoversExact : CoversExact 8
    leaf3880Box leaf3880Certificate leaf3880InnerLog leaf3880Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk106RoundedFacts chi241RoundedFacts
    innerPair173RoundedFacts leaf3880RoundedFacts (by rfl)

private theorem leaf3880FlatSound : Sound leaf3880Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3880CertificateValid
    leaf3880InnerLogValid leaf3880CoversExact leaf3880LowerChecked

private noncomputable def leaf3881Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (85/32), kHi := (43/16), chiLo := (33/128), chiHi := (17/64) }

private noncomputable def leaf3881Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435695/268435456) }, vSqrt := { lower := (32765/32768), upper := (13743698739/13743296512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (452219711/268435456) }, upper := { exponent := 0, mantissa := (1755/1024) } }, logOuter := sk106LogOuterCertificate, logK := sk106LogKCertificate, logChi := chi242LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (27486995251/27486593024) } }, logDArg := sk106LogDArgCertificate }

private noncomputable def leaf3881InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf3881LocalValidity :
    LeafFacts leaf3881Box leaf3881Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3881Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (13743698739/13743296512) }) = true
      norm_num [leaf3881Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3881CertificateValid :
    WideCertificateValid leaf3881Box leaf3881Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk106ValidityFacts chi242ValidityFacts
    leaf3881LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3881CoverageChecked :
    coverageCheck (innerAD leaf3881Box) leaf3881InnerLog = true := by
  rfl'

private theorem leaf3881InnerLogValid :
    leaf3881InnerLog.Valid 8 (innerAD leaf3881Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf3881CoverageChecked

private noncomputable def leaf3881InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814663/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3881InputLogOnePlusV_eq :
    leaf3881InputLogOnePlusV = outerEnclosure 24
      (leaf3881Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3881RoundedFacts : LeafRoundedFacts 8
    leaf3881Certificate.logOnePlusV leaf3881InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3881InputLogOnePlusV_eq }

private noncomputable def leaf3881Inputs : Inputs :=
  inputsOfCaches globalInput sk106RoundedInputs
    chi242InputQChi innerPair57Input
    leaf3881InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3881LowerChecked :
    lowerCheck 24 leaf3881Box leaf3881Inputs = true := by
  rfl'

private theorem leaf3881CoversExact : CoversExact 8
    leaf3881Box leaf3881Certificate leaf3881InnerLog leaf3881Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk106RoundedFacts chi242RoundedFacts
    innerPair57RoundedFacts leaf3881RoundedFacts (by rfl)

private theorem leaf3881FlatSound : Sound leaf3881Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3881CertificateValid
    leaf3881InnerLogValid leaf3881CoversExact leaf3881LowerChecked

private noncomputable def leaf3882Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (85/32), chiLo := (17/64), chiHi := (35/128) }

private noncomputable def leaf3882Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435695/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716430336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (455561843/268435456) }, upper := { exponent := 0, mantissa := (7071/4096) } }, logOuter := sk105LogOuterCertificate, logK := sk105LogKCertificate, logChi := chi243LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434924031/137432860672) } }, logDArg := sk105LogDArgCertificate }

private noncomputable def leaf3882InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3882LocalValidity :
    LeafFacts leaf3882Box leaf3882Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3882Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716430336) }) = true
      norm_num [leaf3882Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3882CertificateValid :
    WideCertificateValid leaf3882Box leaf3882Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk105ValidityFacts chi243ValidityFacts
    leaf3882LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3882CoverageChecked :
    coverageCheck (innerAD leaf3882Box) leaf3882InnerLog = true := by
  rfl'

private theorem leaf3882InnerLogValid :
    leaf3882InnerLog.Valid 8 (innerAD leaf3882Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3882CoverageChecked

private noncomputable def leaf3882InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629333/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3882InputLogOnePlusV_eq :
    leaf3882InputLogOnePlusV = outerEnclosure 24
      (leaf3882Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3882RoundedFacts : LeafRoundedFacts 8
    leaf3882Certificate.logOnePlusV leaf3882InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3882InputLogOnePlusV_eq }

private noncomputable def leaf3882Inputs : Inputs :=
  inputsOfCaches globalInput sk105RoundedInputs
    chi243InputQChi innerPair64Input
    leaf3882InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3882LowerChecked :
    lowerCheck 24 leaf3882Box leaf3882Inputs = true := by
  rfl'

private theorem leaf3882CoversExact : CoversExact 8
    leaf3882Box leaf3882Certificate leaf3882InnerLog leaf3882Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk105RoundedFacts chi243RoundedFacts
    innerPair64RoundedFacts leaf3882RoundedFacts (by rfl)

private theorem leaf3882FlatSound : Sound leaf3882Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3882CertificateValid
    leaf3882InnerLogValid leaf3882CoversExact leaf3882LowerChecked

private noncomputable def leaf3883Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (85/32), chiLo := (35/128), chiHi := (9/32) }

private noncomputable def leaf3883Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435697/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716343296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (461066529/268435456) }, upper := { exponent := 0, mantissa := (1789/1024) } }, logOuter := sk105LogOuterCertificate, logK := sk105LogKCertificate, logChi := chi244LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434836991/137432686592) } }, logDArg := sk105LogDArgCertificate }

private noncomputable def leaf3883InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3883LocalValidity :
    LeafFacts leaf3883Box leaf3883Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3883Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716343296) }) = true
      norm_num [leaf3883Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3883CertificateValid :
    WideCertificateValid leaf3883Box leaf3883Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk105ValidityFacts chi244ValidityFacts
    leaf3883LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3883CoverageChecked :
    coverageCheck (innerAD leaf3883Box) leaf3883InnerLog = true := by
  rfl'

private theorem leaf3883InnerLogValid :
    leaf3883InnerLog.Valid 8 (innerAD leaf3883Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3883CoverageChecked

private noncomputable def leaf3883InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629343/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3883InputLogOnePlusV_eq :
    leaf3883InputLogOnePlusV = outerEnclosure 24
      (leaf3883Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3883RoundedFacts : LeafRoundedFacts 8
    leaf3883Certificate.logOnePlusV leaf3883InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3883InputLogOnePlusV_eq }

private noncomputable def leaf3883Inputs : Inputs :=
  inputsOfCaches globalInput sk105RoundedInputs
    chi244InputQChi innerPair64Input
    leaf3883InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3883LowerChecked :
    lowerCheck 24 leaf3883Box leaf3883Inputs = true := by
  rfl'

private theorem leaf3883CoversExact : CoversExact 8
    leaf3883Box leaf3883Certificate leaf3883InnerLog leaf3883Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk105RoundedFacts chi244RoundedFacts
    innerPair64RoundedFacts leaf3883RoundedFacts (by rfl)

private theorem leaf3883FlatSound : Sound leaf3883Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3883CertificateValid
    leaf3883InnerLogValid leaf3883CoversExact leaf3883LowerChecked

private noncomputable def leaf3884Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (85/32), kHi := (43/16), chiLo := (17/64), chiHi := (35/128) }

private noncomputable def leaf3884Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435697/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905464832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (457789929/268435456) }, upper := { exponent := 0, mantissa := (3553/2048) } }, logOuter := sk106LogOuterCertificate, logK := sk106LogKCertificate, logChi := chi243LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811629397/45810929664) } }, logDArg := sk106LogDArgCertificate }

private noncomputable def leaf3884InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3884LocalValidity :
    LeafFacts leaf3884Box leaf3884Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3884Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905464832) }) = true
      norm_num [leaf3884Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3884CertificateValid :
    WideCertificateValid leaf3884Box leaf3884Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk106ValidityFacts chi243ValidityFacts
    leaf3884LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3884CoverageChecked :
    coverageCheck (innerAD leaf3884Box) leaf3884InnerLog = true := by
  rfl'

private theorem leaf3884InnerLogValid :
    leaf3884InnerLog.Valid 8 (innerAD leaf3884Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3884CoverageChecked

private noncomputable def leaf3884InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629337/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3884InputLogOnePlusV_eq :
    leaf3884InputLogOnePlusV = outerEnclosure 24
      (leaf3884Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3884RoundedFacts : LeafRoundedFacts 8
    leaf3884Certificate.logOnePlusV leaf3884InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3884InputLogOnePlusV_eq }

private noncomputable def leaf3884Inputs : Inputs :=
  inputsOfCaches globalInput sk106RoundedInputs
    chi243InputQChi innerPair64Input
    leaf3884InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3884LowerChecked :
    lowerCheck 24 leaf3884Box leaf3884Inputs = true := by
  rfl'

private theorem leaf3884CoversExact : CoversExact 8
    leaf3884Box leaf3884Certificate leaf3884InnerLog leaf3884Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk106RoundedFacts chi243RoundedFacts
    innerPair64RoundedFacts leaf3884RoundedFacts (by rfl)

private theorem leaf3884FlatSound : Sound leaf3884Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3884CertificateValid
    leaf3884InnerLogValid leaf3884CoversExact leaf3884LowerChecked

private noncomputable def leaf3885Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (85/32), kHi := (43/16), chiLo := (35/128), chiHi := (9/32) }

private noncomputable def leaf3885Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435699/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716306432) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (463360147/268435456) }, upper := { exponent := 0, mantissa := (899/512) } }, logOuter := sk106LogOuterCertificate, logK := sk106LogKCertificate, logChi := chi244LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434800127/137432612864) } }, logDArg := sk106LogDArgCertificate }

private noncomputable def leaf3885InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf3885LocalValidity :
    LeafFacts leaf3885Box leaf3885Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3885Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716306432) }) = true
      norm_num [leaf3885Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3885CertificateValid :
    WideCertificateValid leaf3885Box leaf3885Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk106ValidityFacts chi244ValidityFacts
    leaf3885LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3885CoverageChecked :
    coverageCheck (innerAD leaf3885Box) leaf3885InnerLog = true := by
  rfl'

private theorem leaf3885InnerLogValid :
    leaf3885InnerLog.Valid 8 (innerAD leaf3885Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf3885CoverageChecked

private noncomputable def leaf3885InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907337/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3885InputLogOnePlusV_eq :
    leaf3885InputLogOnePlusV = outerEnclosure 24
      (leaf3885Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3885RoundedFacts : LeafRoundedFacts 8
    leaf3885Certificate.logOnePlusV leaf3885InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3885InputLogOnePlusV_eq }

private noncomputable def leaf3885Inputs : Inputs :=
  inputsOfCaches globalInput sk106RoundedInputs
    chi244InputQChi innerPair66Input
    leaf3885InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3885LowerChecked :
    lowerCheck 24 leaf3885Box leaf3885Inputs = true := by
  rfl'

private theorem leaf3885CoversExact : CoversExact 8
    leaf3885Box leaf3885Certificate leaf3885InnerLog leaf3885Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk106RoundedFacts chi244RoundedFacts
    innerPair66RoundedFacts leaf3885RoundedFacts (by rfl)

private theorem leaf3885FlatSound : Sound leaf3885Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3885CertificateValid
    leaf3885InnerLogValid leaf3885CoversExact leaf3885LowerChecked

private noncomputable def leaf3886Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (1/4), chiHi := (33/128) }

private noncomputable def leaf3886Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435695/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716536832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (448746515/268435456) }, upper := { exponent := 0, mantissa := (6967/4096) } }, logOuter := sk103LogOuterCertificate, logK := sk103LogKCertificate, logChi := chi241LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435030527/137433073664) } }, logDArg := sk103LogDArgCertificate }

private noncomputable def leaf3886InnerLog : WideLogData :=
  innerPair173Data

set_option maxRecDepth 1000000 in
private theorem leaf3886LocalValidity :
    LeafFacts leaf3886Box leaf3886Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3886Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716536832) }) = true
      norm_num [leaf3886Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3886CertificateValid :
    WideCertificateValid leaf3886Box leaf3886Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk103ValidityFacts chi241ValidityFacts
    leaf3886LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3886CoverageChecked :
    coverageCheck (innerAD leaf3886Box) leaf3886InnerLog = true := by
  rfl'

private theorem leaf3886InnerLogValid :
    leaf3886InnerLog.Valid 8 (innerAD leaf3886Box) :=
  wideLogDataValid_of_cachedCheck endpoint48PositiveFacts
    endpoint20PositiveFacts.valid leaf3886CoverageChecked

private noncomputable def leaf3886InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453665/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3886InputLogOnePlusV_eq :
    leaf3886InputLogOnePlusV = outerEnclosure 24
      (leaf3886Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3886RoundedFacts : LeafRoundedFacts 8
    leaf3886Certificate.logOnePlusV leaf3886InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3886InputLogOnePlusV_eq }

private noncomputable def leaf3886Inputs : Inputs :=
  inputsOfCaches globalInput sk103RoundedInputs
    chi241InputQChi innerPair173Input
    leaf3886InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3886LowerChecked :
    lowerCheck 24 leaf3886Box leaf3886Inputs = true := by
  rfl'

private theorem leaf3886CoversExact : CoversExact 8
    leaf3886Box leaf3886Certificate leaf3886InnerLog leaf3886Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk103RoundedFacts chi241RoundedFacts
    innerPair173RoundedFacts leaf3886RoundedFacts (by rfl)

private theorem leaf3886FlatSound : Sound leaf3886Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3886CertificateValid
    leaf3886InnerLogValid leaf3886CoversExact leaf3886LowerChecked

private noncomputable def leaf3887Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (33/128), chiHi := (17/64) }

private noncomputable def leaf3887Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435697/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716447744) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (454382265/268435456) }, upper := { exponent := 0, mantissa := (3527/2048) } }, logOuter := sk103LogOuterCertificate, logK := sk103LogKCertificate, logChi := chi242LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434941439/137432895488) } }, logDArg := sk103LogDArgCertificate }

private noncomputable def leaf3887InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3887LocalValidity :
    LeafFacts leaf3887Box leaf3887Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3887Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716447744) }) = true
      norm_num [leaf3887Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3887CertificateValid :
    WideCertificateValid leaf3887Box leaf3887Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk103ValidityFacts chi242ValidityFacts
    leaf3887LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3887CoverageChecked :
    coverageCheck (innerAD leaf3887Box) leaf3887InnerLog = true := by
  rfl'

private theorem leaf3887InnerLogValid :
    leaf3887InnerLog.Valid 8 (innerAD leaf3887Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3887CoverageChecked

private noncomputable def leaf3887InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629331/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3887InputLogOnePlusV_eq :
    leaf3887InputLogOnePlusV = outerEnclosure 24
      (leaf3887Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3887RoundedFacts : LeafRoundedFacts 8
    leaf3887Certificate.logOnePlusV leaf3887InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3887InputLogOnePlusV_eq }

private noncomputable def leaf3887Inputs : Inputs :=
  inputsOfCaches globalInput sk103RoundedInputs
    chi242InputQChi innerPair64Input
    leaf3887InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3887LowerChecked :
    lowerCheck 24 leaf3887Box leaf3887Inputs = true := by
  rfl'

private theorem leaf3887CoversExact : CoversExact 8
    leaf3887Box leaf3887Certificate leaf3887InnerLog leaf3887Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk103RoundedFacts chi242RoundedFacts
    innerPair64RoundedFacts leaf3887RoundedFacts (by rfl)

private theorem leaf3887FlatSound : Sound leaf3887Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3887CertificateValid
    leaf3887InnerLogValid leaf3887CoversExact leaf3887LowerChecked

private noncomputable def leaf3888Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (1/4), chiHi := (33/128) }

private noncomputable def leaf3888Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435697/268435456) }, vSqrt := { lower := (32765/32768), upper := (13743698739/13743300608) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (450843537/268435456) }, upper := { exponent := 0, mantissa := (875/512) } }, logOuter := sk104LogOuterCertificate, logK := sk104LogKCertificate, logChi := chi241LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (27486999347/27486601216) } }, logDArg := sk104LogDArgCertificate }

private noncomputable def leaf3888InnerLog : WideLogData :=
  innerPair421Data

set_option maxRecDepth 1000000 in
private theorem leaf3888LocalValidity :
    LeafFacts leaf3888Box leaf3888Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3888Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (13743698739/13743300608) }) = true
      norm_num [leaf3888Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3888CertificateValid :
    WideCertificateValid leaf3888Box leaf3888Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk104ValidityFacts chi241ValidityFacts
    leaf3888LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3888CoverageChecked :
    coverageCheck (innerAD leaf3888Box) leaf3888InnerLog = true := by
  rfl'

private theorem leaf3888InnerLogValid :
    leaf3888InnerLog.Valid 8 (innerAD leaf3888Box) :=
  wideLogDataValid_of_cachedCheck endpoint133PositiveFacts
    endpoint62PositiveFacts.valid leaf3888CoverageChecked

private noncomputable def leaf3888InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907331/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3888InputLogOnePlusV_eq :
    leaf3888InputLogOnePlusV = outerEnclosure 24
      (leaf3888Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3888RoundedFacts : LeafRoundedFacts 8
    leaf3888Certificate.logOnePlusV leaf3888InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3888InputLogOnePlusV_eq }

private noncomputable def leaf3888Inputs : Inputs :=
  inputsOfCaches globalInput sk104RoundedInputs
    chi241InputQChi innerPair421Input
    leaf3888InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3888LowerChecked :
    lowerCheck 24 leaf3888Box leaf3888Inputs = true := by
  rfl'

private theorem leaf3888CoversExact : CoversExact 8
    leaf3888Box leaf3888Certificate leaf3888InnerLog leaf3888Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk104RoundedFacts chi241RoundedFacts
    innerPair421RoundedFacts leaf3888RoundedFacts (by rfl)

private theorem leaf3888FlatSound : Sound leaf3888Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3888CertificateValid
    leaf3888InnerLogValid leaf3888CoversExact leaf3888LowerChecked

private noncomputable def leaf3889Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (33/128), chiHi := (17/64) }

private noncomputable def leaf3889Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435699/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905470976) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (456544819/268435456) }, upper := { exponent := 0, mantissa := (443/256) } }, logOuter := sk104LogOuterCertificate, logK := sk104LogKCertificate, logChi := chi242LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811635541/45810941952) } }, logDArg := sk104LogDArgCertificate }

private noncomputable def leaf3889InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3889LocalValidity :
    LeafFacts leaf3889Box leaf3889Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3889Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905470976) }) = true
      norm_num [leaf3889Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3889CertificateValid :
    WideCertificateValid leaf3889Box leaf3889Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk104ValidityFacts chi242ValidityFacts
    leaf3889LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3889CoverageChecked :
    coverageCheck (innerAD leaf3889Box) leaf3889InnerLog = true := by
  rfl'

private theorem leaf3889InnerLogValid :
    leaf3889InnerLog.Valid 8 (innerAD leaf3889Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3889CoverageChecked

private noncomputable def leaf3889InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629335/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3889InputLogOnePlusV_eq :
    leaf3889InputLogOnePlusV = outerEnclosure 24
      (leaf3889Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3889RoundedFacts : LeafRoundedFacts 8
    leaf3889Certificate.logOnePlusV leaf3889InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3889InputLogOnePlusV_eq }

private noncomputable def leaf3889Inputs : Inputs :=
  inputsOfCaches globalInput sk104RoundedInputs
    chi242InputQChi innerPair64Input
    leaf3889InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3889LowerChecked :
    lowerCheck 24 leaf3889Box leaf3889Inputs = true := by
  rfl'

private theorem leaf3889CoversExact : CoversExact 8
    leaf3889Box leaf3889Certificate leaf3889InnerLog leaf3889Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk104RoundedFacts chi242RoundedFacts
    innerPair64RoundedFacts leaf3889RoundedFacts (by rfl)

private theorem leaf3889FlatSound : Sound leaf3889Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3889CertificateValid
    leaf3889InnerLogValid leaf3889CoversExact leaf3889LowerChecked

private noncomputable def leaf3890Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (17/64), chiHi := (35/128) }

private noncomputable def leaf3890Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435699/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716358656) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (460018015/268435456) }, upper := { exponent := 0, mantissa := (7141/4096) } }, logOuter := sk103LogOuterCertificate, logK := sk103LogKCertificate, logChi := chi243LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434852351/137432717312) } }, logDArg := sk103LogDArgCertificate }

private noncomputable def leaf3890InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3890LocalValidity :
    LeafFacts leaf3890Box leaf3890Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3890Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716358656) }) = true
      norm_num [leaf3890Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3890CertificateValid :
    WideCertificateValid leaf3890Box leaf3890Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk103ValidityFacts chi243ValidityFacts
    leaf3890LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3890CoverageChecked :
    coverageCheck (innerAD leaf3890Box) leaf3890InnerLog = true := by
  rfl'

private theorem leaf3890InnerLogValid :
    leaf3890InnerLog.Valid 8 (innerAD leaf3890Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3890CoverageChecked

private noncomputable def leaf3890InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629341/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3890InputLogOnePlusV_eq :
    leaf3890InputLogOnePlusV = outerEnclosure 24
      (leaf3890Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3890RoundedFacts : LeafRoundedFacts 8
    leaf3890Certificate.logOnePlusV leaf3890InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3890InputLogOnePlusV_eq }

private noncomputable def leaf3890Inputs : Inputs :=
  inputsOfCaches globalInput sk103RoundedInputs
    chi243InputQChi innerPair64Input
    leaf3890InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3890LowerChecked :
    lowerCheck 24 leaf3890Box leaf3890Inputs = true := by
  rfl'

private theorem leaf3890CoversExact : CoversExact 8
    leaf3890Box leaf3890Certificate leaf3890InnerLog leaf3890Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk103RoundedFacts chi243RoundedFacts
    innerPair64RoundedFacts leaf3890RoundedFacts (by rfl)

private theorem leaf3890FlatSound : Sound leaf3890Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3890CertificateValid
    leaf3890InnerLogValid leaf3890CoversExact leaf3890LowerChecked

private noncomputable def leaf3891Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (35/128), chiHi := (9/32) }

private noncomputable def leaf3891Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435701/268435456) }, vSqrt := { lower := (32765/32768), upper := (4042264335/4042133504) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (465653765/268435456) }, upper := { exponent := 0, mantissa := (1807/1024) } }, logOuter := sk103LogOuterCertificate, logK := sk103LogKCertificate, logChi := chi244LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (8084397839/8084267008) } }, logDArg := sk103LogDArgCertificate }

private noncomputable def leaf3891InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf3891LocalValidity :
    LeafFacts leaf3891Box leaf3891Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3891Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4042264335/4042133504) }) = true
      norm_num [leaf3891Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3891CertificateValid :
    WideCertificateValid leaf3891Box leaf3891Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk103ValidityFacts chi244ValidityFacts
    leaf3891LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3891CoverageChecked :
    coverageCheck (innerAD leaf3891Box) leaf3891InnerLog = true := by
  rfl'

private theorem leaf3891InnerLogValid :
    leaf3891InnerLog.Valid 8 (innerAD leaf3891Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf3891CoverageChecked

private noncomputable def leaf3891InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453669/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3891InputLogOnePlusV_eq :
    leaf3891InputLogOnePlusV = outerEnclosure 24
      (leaf3891Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3891RoundedFacts : LeafRoundedFacts 8
    leaf3891Certificate.logOnePlusV leaf3891InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3891InputLogOnePlusV_eq }

private noncomputable def leaf3891Inputs : Inputs :=
  inputsOfCaches globalInput sk103RoundedInputs
    chi244InputQChi innerPair66Input
    leaf3891InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3891LowerChecked :
    lowerCheck 24 leaf3891Box leaf3891Inputs = true := by
  rfl'

private theorem leaf3891CoversExact : CoversExact 8
    leaf3891Box leaf3891Certificate leaf3891InnerLog leaf3891Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk103RoundedFacts chi244RoundedFacts
    innerPair66RoundedFacts leaf3891RoundedFacts (by rfl)

private theorem leaf3891FlatSound : Sound leaf3891Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3891CertificateValid
    leaf3891InnerLogValid leaf3891CoversExact leaf3891LowerChecked

private noncomputable def leaf3892Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (17/64), chiHi := (35/128) }

private noncomputable def leaf3892Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435701/268435456) }, vSqrt := { lower := (32765/32768), upper := (267387135/267378688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (462246101/268435456) }, upper := { exponent := 0, mantissa := (897/512) } }, logOuter := sk104LogOuterCertificate, logK := sk104LogKCertificate, logChi := chi243LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (534765823/534757376) } }, logDArg := sk104LogDArgCertificate }

private noncomputable def leaf3892InnerLog : WideLogData :=
  innerPair204Data

set_option maxRecDepth 1000000 in
private theorem leaf3892LocalValidity :
    LeafFacts leaf3892Box leaf3892Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3892Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (267387135/267378688) }) = true
      norm_num [leaf3892Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3892CertificateValid :
    WideCertificateValid leaf3892Box leaf3892Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk104ValidityFacts chi243ValidityFacts
    leaf3892LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3892CoverageChecked :
    coverageCheck (innerAD leaf3892Box) leaf3892InnerLog = true := by
  rfl'

private theorem leaf3892InnerLogValid :
    leaf3892InnerLog.Valid 8 (innerAD leaf3892Box) :=
  wideLogDataValid_of_cachedCheck endpoint62PositiveFacts
    endpoint63PositiveFacts.valid leaf3892CoverageChecked

private noncomputable def leaf3892InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814673/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3892InputLogOnePlusV_eq :
    leaf3892InputLogOnePlusV = outerEnclosure 24
      (leaf3892Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3892RoundedFacts : LeafRoundedFacts 8
    leaf3892Certificate.logOnePlusV leaf3892InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3892InputLogOnePlusV_eq }

private noncomputable def leaf3892Inputs : Inputs :=
  inputsOfCaches globalInput sk104RoundedInputs
    chi243InputQChi innerPair204Input
    leaf3892InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3892LowerChecked :
    lowerCheck 24 leaf3892Box leaf3892Inputs = true := by
  rfl'

private theorem leaf3892CoversExact : CoversExact 8
    leaf3892Box leaf3892Certificate leaf3892InnerLog leaf3892Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk104RoundedFacts chi243RoundedFacts
    innerPair204RoundedFacts leaf3892RoundedFacts (by rfl)

private theorem leaf3892FlatSound : Sound leaf3892Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3892CertificateValid
    leaf3892InnerLogValid leaf3892CoversExact leaf3892LowerChecked

private noncomputable def leaf3893Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (35/128), chiHi := (9/32) }

private noncomputable def leaf3893Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435703/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716232704) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (467947383/268435456) }, upper := { exponent := 0, mantissa := (227/128) } }, logOuter := sk104LogOuterCertificate, logK := sk104LogKCertificate, logChi := chi244LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434726399/137432465408) } }, logDArg := sk104LogDArgCertificate }

private noncomputable def leaf3893InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf3893LocalValidity :
    LeafFacts leaf3893Box leaf3893Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3893Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716232704) }) = true
      norm_num [leaf3893Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3893CertificateValid :
    WideCertificateValid leaf3893Box leaf3893Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk104ValidityFacts chi244ValidityFacts
    leaf3893LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3893CoverageChecked :
    coverageCheck (innerAD leaf3893Box) leaf3893InnerLog = true := by
  rfl'

private theorem leaf3893InnerLogValid :
    leaf3893InnerLog.Valid 8 (innerAD leaf3893Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf3893CoverageChecked

private noncomputable def leaf3893InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629357/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3893InputLogOnePlusV_eq :
    leaf3893InputLogOnePlusV = outerEnclosure 24
      (leaf3893Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3893RoundedFacts : LeafRoundedFacts 8
    leaf3893Certificate.logOnePlusV leaf3893InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3893InputLogOnePlusV_eq }

private noncomputable def leaf3893Inputs : Inputs :=
  inputsOfCaches globalInput sk104RoundedInputs
    chi244InputQChi innerPair66Input
    leaf3893InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3893LowerChecked :
    lowerCheck 24 leaf3893Box leaf3893Inputs = true := by
  rfl'

private theorem leaf3893CoversExact : CoversExact 8
    leaf3893Box leaf3893Certificate leaf3893InnerLog leaf3893Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk104RoundedFacts chi244RoundedFacts
    innerPair66RoundedFacts leaf3893RoundedFacts (by rfl)

private theorem leaf3893FlatSound : Sound leaf3893Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3893CertificateValid
    leaf3893InnerLogValid leaf3893CoversExact leaf3893LowerChecked

private noncomputable def leaf3894Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (85/32), chiLo := (9/32), chiHi := (37/128) }

private noncomputable def leaf3894Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435699/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905418752) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (466571215/268435456) }, upper := { exponent := 0, mantissa := (7241/4096) } }, logOuter := sk105LogOuterCertificate, logK := sk105LogKCertificate, logChi := chi245LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811583317/45810837504) } }, logDArg := sk105LogDArgCertificate }

private noncomputable def leaf3894InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf3894LocalValidity :
    LeafFacts leaf3894Box leaf3894Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3894Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905418752) }) = true
      norm_num [leaf3894Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3894CertificateValid :
    WideCertificateValid leaf3894Box leaf3894Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk105ValidityFacts chi245ValidityFacts
    leaf3894LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3894CoverageChecked :
    coverageCheck (innerAD leaf3894Box) leaf3894InnerLog = true := by
  rfl'

private theorem leaf3894InnerLogValid :
    leaf3894InnerLog.Valid 8 (innerAD leaf3894Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf3894CoverageChecked

private noncomputable def leaf3894InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814677/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3894InputLogOnePlusV_eq :
    leaf3894InputLogOnePlusV = outerEnclosure 24
      (leaf3894Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3894RoundedFacts : LeafRoundedFacts 8
    leaf3894Certificate.logOnePlusV leaf3894InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3894InputLogOnePlusV_eq }

private noncomputable def leaf3894Inputs : Inputs :=
  inputsOfCaches globalInput sk105RoundedInputs
    chi245InputQChi innerPair66Input
    leaf3894InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3894LowerChecked :
    lowerCheck 24 leaf3894Box leaf3894Inputs = true := by
  rfl'

private theorem leaf3894CoversExact : CoversExact 8
    leaf3894Box leaf3894Certificate leaf3894InnerLog leaf3894Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk105RoundedFacts chi245RoundedFacts
    innerPair66RoundedFacts leaf3894RoundedFacts (by rfl)

private theorem leaf3894FlatSound : Sound leaf3894Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3894CertificateValid
    leaf3894InnerLogValid leaf3894CoversExact leaf3894LowerChecked

private noncomputable def leaf3895Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (85/32), chiLo := (37/128), chiHi := (19/64) }

private noncomputable def leaf3895Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435701/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716169216) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (472075901/268435456) }, upper := { exponent := 0, mantissa := (3663/2048) } }, logOuter := sk105LogOuterCertificate, logK := sk105LogKCertificate, logChi := chi246LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434662911/137432338432) } }, logDArg := sk105LogDArgCertificate }

private noncomputable def leaf3895InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3895LocalValidity :
    LeafFacts leaf3895Box leaf3895Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3895Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716169216) }) = true
      norm_num [leaf3895Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3895CertificateValid :
    WideCertificateValid leaf3895Box leaf3895Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk105ValidityFacts chi246ValidityFacts
    leaf3895LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3895CoverageChecked :
    coverageCheck (innerAD leaf3895Box) leaf3895InnerLog = true := by
  rfl'

private theorem leaf3895InnerLogValid :
    leaf3895InnerLog.Valid 8 (innerAD leaf3895Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3895CoverageChecked

private noncomputable def leaf3895InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629365/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3895InputLogOnePlusV_eq :
    leaf3895InputLogOnePlusV = outerEnclosure 24
      (leaf3895Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3895RoundedFacts : LeafRoundedFacts 8
    leaf3895Certificate.logOnePlusV leaf3895InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3895InputLogOnePlusV_eq }

private noncomputable def leaf3895Inputs : Inputs :=
  inputsOfCaches globalInput sk105RoundedInputs
    chi246InputQChi innerPair71Input
    leaf3895InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3895LowerChecked :
    lowerCheck 24 leaf3895Box leaf3895Inputs = true := by
  rfl'

private theorem leaf3895CoversExact : CoversExact 8
    leaf3895Box leaf3895Certificate leaf3895InnerLog leaf3895Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk105RoundedFacts chi246RoundedFacts
    innerPair71RoundedFacts leaf3895RoundedFacts (by rfl)

private theorem leaf3895FlatSound : Sound leaf3895Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3895CertificateValid
    leaf3895InnerLogValid leaf3895CoversExact leaf3895LowerChecked

private noncomputable def leaf3896Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (85/32), kHi := (43/16), chiLo := (9/32), chiHi := (37/128) }

private noncomputable def leaf3896Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435701/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716218368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (468930365/268435456) }, upper := { exponent := 0, mantissa := (3639/2048) } }, logOuter := sk106LogOuterCertificate, logK := sk106LogKCertificate, logChi := chi245LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434712063/137432436736) } }, logDArg := sk106LogDArgCertificate }

private noncomputable def leaf3896InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf3896LocalValidity :
    LeafFacts leaf3896Box leaf3896Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3896Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716218368) }) = true
      norm_num [leaf3896Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3896CertificateValid :
    WideCertificateValid leaf3896Box leaf3896Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk106ValidityFacts chi245ValidityFacts
    leaf3896LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3896CoverageChecked :
    coverageCheck (innerAD leaf3896Box) leaf3896InnerLog = true := by
  rfl'

private theorem leaf3896InnerLogValid :
    leaf3896InnerLog.Valid 8 (innerAD leaf3896Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf3896CoverageChecked

private noncomputable def leaf3896InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629359/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3896InputLogOnePlusV_eq :
    leaf3896InputLogOnePlusV = outerEnclosure 24
      (leaf3896Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3896RoundedFacts : LeafRoundedFacts 8
    leaf3896Certificate.logOnePlusV leaf3896InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3896InputLogOnePlusV_eq }

private noncomputable def leaf3896Inputs : Inputs :=
  inputsOfCaches globalInput sk106RoundedInputs
    chi245InputQChi innerPair66Input
    leaf3896InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3896LowerChecked :
    lowerCheck 24 leaf3896Box leaf3896Inputs = true := by
  rfl'

private theorem leaf3896CoversExact : CoversExact 8
    leaf3896Box leaf3896Certificate leaf3896InnerLog leaf3896Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk106RoundedFacts chi245RoundedFacts
    innerPair66RoundedFacts leaf3896RoundedFacts (by rfl)

private theorem leaf3896FlatSound : Sound leaf3896Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3896CertificateValid
    leaf3896InnerLogValid leaf3896CoversExact leaf3896LowerChecked

private noncomputable def leaf3897Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (85/32), kHi := (43/16), chiLo := (37/128), chiHi := (19/64) }

private noncomputable def leaf3897Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435703/268435456) }, vSqrt := { lower := (32765/32768), upper := (1347421445/1347375104) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (474500583/268435456) }, upper := { exponent := 0, mantissa := (1841/1024) } }, logOuter := sk106LogOuterCertificate, logK := sk106LogKCertificate, logChi := chi246LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (2694796549/2694750208) } }, logDArg := sk106LogDArgCertificate }

private noncomputable def leaf3897InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3897LocalValidity :
    LeafFacts leaf3897Box leaf3897Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3897Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (1347421445/1347375104) }) = true
      norm_num [leaf3897Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3897CertificateValid :
    WideCertificateValid leaf3897Box leaf3897Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk106ValidityFacts chi246ValidityFacts
    leaf3897LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3897CoverageChecked :
    coverageCheck (innerAD leaf3897Box) leaf3897InnerLog = true := by
  rfl'

private theorem leaf3897InnerLogValid :
    leaf3897InnerLog.Valid 8 (innerAD leaf3897Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3897CoverageChecked

private noncomputable def leaf3897InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629369/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3897InputLogOnePlusV_eq :
    leaf3897InputLogOnePlusV = outerEnclosure 24
      (leaf3897Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3897RoundedFacts : LeafRoundedFacts 8
    leaf3897Certificate.logOnePlusV leaf3897InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3897InputLogOnePlusV_eq }

private noncomputable def leaf3897Inputs : Inputs :=
  inputsOfCaches globalInput sk106RoundedInputs
    chi246InputQChi innerPair71Input
    leaf3897InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3897LowerChecked :
    lowerCheck 24 leaf3897Box leaf3897Inputs = true := by
  rfl'

private theorem leaf3897CoversExact : CoversExact 8
    leaf3897Box leaf3897Certificate leaf3897InnerLog leaf3897Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk106RoundedFacts chi246RoundedFacts
    innerPair71RoundedFacts leaf3897RoundedFacts (by rfl)

private theorem leaf3897FlatSound : Sound leaf3897Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3897CertificateValid
    leaf3897InnerLogValid leaf3897CoversExact leaf3897LowerChecked

private noncomputable def leaf3898Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (85/32), chiLo := (19/64), chiHi := (39/128) }

private noncomputable def leaf3898Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435703/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716082176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (477580587/268435456) }, upper := { exponent := 0, mantissa := (7411/4096) } }, logOuter := sk105LogOuterCertificate, logK := sk105LogKCertificate, logChi := chi247LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434575871/137432164352) } }, logDArg := sk105LogDArgCertificate }

private noncomputable def leaf3898InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3898LocalValidity :
    LeafFacts leaf3898Box leaf3898Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3898Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716082176) }) = true
      norm_num [leaf3898Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3898CertificateValid :
    WideCertificateValid leaf3898Box leaf3898Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk105ValidityFacts chi247ValidityFacts
    leaf3898LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3898CoverageChecked :
    coverageCheck (innerAD leaf3898Box) leaf3898InnerLog = true := by
  rfl'

private theorem leaf3898InnerLogValid :
    leaf3898InnerLog.Valid 8 (innerAD leaf3898Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3898CoverageChecked

private noncomputable def leaf3898InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629375/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3898InputLogOnePlusV_eq :
    leaf3898InputLogOnePlusV = outerEnclosure 24
      (leaf3898Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3898RoundedFacts : LeafRoundedFacts 8
    leaf3898Certificate.logOnePlusV leaf3898InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3898InputLogOnePlusV_eq }

private noncomputable def leaf3898Inputs : Inputs :=
  inputsOfCaches globalInput sk105RoundedInputs
    chi247InputQChi innerPair71Input
    leaf3898InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3898LowerChecked :
    lowerCheck 24 leaf3898Box leaf3898Inputs = true := by
  rfl'

private theorem leaf3898CoversExact : CoversExact 8
    leaf3898Box leaf3898Certificate leaf3898InnerLog leaf3898Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk105RoundedFacts chi247RoundedFacts
    innerPair71RoundedFacts leaf3898RoundedFacts (by rfl)

private theorem leaf3898FlatSound : Sound leaf3898Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3898CertificateValid
    leaf3898InnerLogValid leaf3898CoversExact leaf3898LowerChecked

private noncomputable def leaf3899Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (85/32), chiLo := (39/128), chiHi := (5/16) }

private noncomputable def leaf3899Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435705/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905331712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (483085273/268435456) }, upper := { exponent := 0, mantissa := (937/512) } }, logOuter := sk105LogOuterCertificate, logK := sk105LogKCertificate, logChi := chi248LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811496277/45810663424) } }, logDArg := sk105LogDArgCertificate }

private noncomputable def leaf3899InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf3899LocalValidity :
    LeafFacts leaf3899Box leaf3899Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3899Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905331712) }) = true
      norm_num [leaf3899Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3899CertificateValid :
    WideCertificateValid leaf3899Box leaf3899Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk105ValidityFacts chi248ValidityFacts
    leaf3899LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3899CoverageChecked :
    coverageCheck (innerAD leaf3899Box) leaf3899InnerLog = true := by
  rfl'

private theorem leaf3899InnerLogValid :
    leaf3899InnerLog.Valid 8 (innerAD leaf3899Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf3899CoverageChecked

private noncomputable def leaf3899InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814693/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3899InputLogOnePlusV_eq :
    leaf3899InputLogOnePlusV = outerEnclosure 24
      (leaf3899Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3899RoundedFacts : LeafRoundedFacts 8
    leaf3899Certificate.logOnePlusV leaf3899InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3899InputLogOnePlusV_eq }

private noncomputable def leaf3899Inputs : Inputs :=
  inputsOfCaches globalInput sk105RoundedInputs
    chi248InputQChi innerPair72Input
    leaf3899InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3899LowerChecked :
    lowerCheck 24 leaf3899Box leaf3899Inputs = true := by
  rfl'

private theorem leaf3899CoversExact : CoversExact 8
    leaf3899Box leaf3899Certificate leaf3899InnerLog leaf3899Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk105RoundedFacts chi248RoundedFacts
    innerPair72RoundedFacts leaf3899RoundedFacts (by rfl)

private theorem leaf3899FlatSound : Sound leaf3899Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3899CertificateValid
    leaf3899InnerLogValid leaf3899CoversExact leaf3899LowerChecked

private noncomputable def leaf3900Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (85/32), kHi := (43/16), chiLo := (19/64), chiHi := (39/128) }

private noncomputable def leaf3900Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435705/268435456) }, vSqrt := { lower := (32765/32768), upper := (13743698739/13743208448) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (480070801/268435456) }, upper := { exponent := 0, mantissa := (3725/2048) } }, logOuter := sk106LogOuterCertificate, logK := sk106LogKCertificate, logChi := chi247LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (27486907187/27486416896) } }, logDArg := sk106LogDArgCertificate }

private noncomputable def leaf3900InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf3900LocalValidity :
    LeafFacts leaf3900Box leaf3900Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3900Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (13743698739/13743208448) }) = true
      norm_num [leaf3900Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3900CertificateValid :
    WideCertificateValid leaf3900Box leaf3900Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk106ValidityFacts chi247ValidityFacts
    leaf3900LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3900CoverageChecked :
    coverageCheck (innerAD leaf3900Box) leaf3900InnerLog = true := by
  rfl'

private theorem leaf3900InnerLogValid :
    leaf3900InnerLog.Valid 8 (innerAD leaf3900Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf3900CoverageChecked

private noncomputable def leaf3900InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907345/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3900InputLogOnePlusV_eq :
    leaf3900InputLogOnePlusV = outerEnclosure 24
      (leaf3900Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3900RoundedFacts : LeafRoundedFacts 8
    leaf3900Certificate.logOnePlusV leaf3900InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3900InputLogOnePlusV_eq }

private noncomputable def leaf3900Inputs : Inputs :=
  inputsOfCaches globalInput sk106RoundedInputs
    chi247InputQChi innerPair72Input
    leaf3900InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3900LowerChecked :
    lowerCheck 24 leaf3900Box leaf3900Inputs = true := by
  rfl'

private theorem leaf3900CoversExact : CoversExact 8
    leaf3900Box leaf3900Certificate leaf3900InnerLog leaf3900Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk106RoundedFacts chi247RoundedFacts
    innerPair72RoundedFacts leaf3900RoundedFacts (by rfl)

private theorem leaf3900FlatSound : Sound leaf3900Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3900CertificateValid
    leaf3900InnerLogValid leaf3900CoversExact leaf3900LowerChecked

private noncomputable def leaf3901Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (85/32), kHi := (43/16), chiLo := (39/128), chiHi := (5/16) }

private noncomputable def leaf3901Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435707/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715954176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (485641019/268435456) }, upper := { exponent := 0, mantissa := (471/256) } }, logOuter := sk106LogOuterCertificate, logK := sk106LogKCertificate, logChi := chi248LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434447871/137431908352) } }, logDArg := sk106LogDArgCertificate }

private noncomputable def leaf3901InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf3901LocalValidity :
    LeafFacts leaf3901Box leaf3901Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3901Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715954176) }) = true
      norm_num [leaf3901Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3901CertificateValid :
    WideCertificateValid leaf3901Box leaf3901Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk106ValidityFacts chi248ValidityFacts
    leaf3901LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3901CoverageChecked :
    coverageCheck (innerAD leaf3901Box) leaf3901InnerLog = true := by
  rfl'

private theorem leaf3901InnerLogValid :
    leaf3901InnerLog.Valid 8 (innerAD leaf3901Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf3901CoverageChecked

private noncomputable def leaf3901InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629391/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3901InputLogOnePlusV_eq :
    leaf3901InputLogOnePlusV = outerEnclosure 24
      (leaf3901Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3901RoundedFacts : LeafRoundedFacts 8
    leaf3901Certificate.logOnePlusV leaf3901InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3901InputLogOnePlusV_eq }

private noncomputable def leaf3901Inputs : Inputs :=
  inputsOfCaches globalInput sk106RoundedInputs
    chi248InputQChi innerPair72Input
    leaf3901InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3901LowerChecked :
    lowerCheck 24 leaf3901Box leaf3901Inputs = true := by
  rfl'

private theorem leaf3901CoversExact : CoversExact 8
    leaf3901Box leaf3901Certificate leaf3901InnerLog leaf3901Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk106RoundedFacts chi248RoundedFacts
    innerPair72RoundedFacts leaf3901RoundedFacts (by rfl)

private theorem leaf3901FlatSound : Sound leaf3901Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3901CertificateValid
    leaf3901InnerLogValid leaf3901CoversExact leaf3901LowerChecked

private noncomputable def leaf3902Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (9/32), chiHi := (37/128) }

private noncomputable def leaf3902Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435703/268435456) }, vSqrt := { lower := (32765/32768), upper := (13743698739/13743236096) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (471289515/268435456) }, upper := { exponent := 0, mantissa := (7315/4096) } }, logOuter := sk103LogOuterCertificate, logK := sk103LogKCertificate, logChi := chi245LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (27486934835/27486472192) } }, logDArg := sk103LogDArgCertificate }

private noncomputable def leaf3902InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3902LocalValidity :
    LeafFacts leaf3902Box leaf3902Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3902Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (13743698739/13743236096) }) = true
      norm_num [leaf3902Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3902CertificateValid :
    WideCertificateValid leaf3902Box leaf3902Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk103ValidityFacts chi245ValidityFacts
    leaf3902LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3902CoverageChecked :
    coverageCheck (innerAD leaf3902Box) leaf3902InnerLog = true := by
  rfl'

private theorem leaf3902InnerLogValid :
    leaf3902InnerLog.Valid 8 (innerAD leaf3902Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3902CoverageChecked

private noncomputable def leaf3902InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629363/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3902InputLogOnePlusV_eq :
    leaf3902InputLogOnePlusV = outerEnclosure 24
      (leaf3902Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3902RoundedFacts : LeafRoundedFacts 8
    leaf3902Certificate.logOnePlusV leaf3902InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3902InputLogOnePlusV_eq }

private noncomputable def leaf3902Inputs : Inputs :=
  inputsOfCaches globalInput sk103RoundedInputs
    chi245InputQChi innerPair71Input
    leaf3902InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3902LowerChecked :
    lowerCheck 24 leaf3902Box leaf3902Inputs = true := by
  rfl'

private theorem leaf3902CoversExact : CoversExact 8
    leaf3902Box leaf3902Certificate leaf3902InnerLog leaf3902Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk103RoundedFacts chi245RoundedFacts
    innerPair71RoundedFacts leaf3902RoundedFacts (by rfl)

private theorem leaf3902FlatSound : Sound leaf3902Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3902CertificateValid
    leaf3902InnerLogValid leaf3902CoversExact leaf3902LowerChecked

private noncomputable def leaf3903Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (37/128), chiHi := (19/64) }

private noncomputable def leaf3903Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435705/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716091392) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (476925265/268435456) }, upper := { exponent := 0, mantissa := (3701/2048) } }, logOuter := sk103LogOuterCertificate, logK := sk103LogKCertificate, logChi := chi246LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434585087/137432182784) } }, logDArg := sk103LogDArgCertificate }

private noncomputable def leaf3903InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3903LocalValidity :
    LeafFacts leaf3903Box leaf3903Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3903Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716091392) }) = true
      norm_num [leaf3903Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3903CertificateValid :
    WideCertificateValid leaf3903Box leaf3903Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk103ValidityFacts chi246ValidityFacts
    leaf3903LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3903CoverageChecked :
    coverageCheck (innerAD leaf3903Box) leaf3903InnerLog = true := by
  rfl'

private theorem leaf3903InnerLogValid :
    leaf3903InnerLog.Valid 8 (innerAD leaf3903Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3903CoverageChecked

private noncomputable def leaf3903InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814687/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3903InputLogOnePlusV_eq :
    leaf3903InputLogOnePlusV = outerEnclosure 24
      (leaf3903Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3903RoundedFacts : LeafRoundedFacts 8
    leaf3903Certificate.logOnePlusV leaf3903InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3903InputLogOnePlusV_eq }

private noncomputable def leaf3903Inputs : Inputs :=
  inputsOfCaches globalInput sk103RoundedInputs
    chi246InputQChi innerPair71Input
    leaf3903InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3903LowerChecked :
    lowerCheck 24 leaf3903Box leaf3903Inputs = true := by
  rfl'

private theorem leaf3903CoversExact : CoversExact 8
    leaf3903Box leaf3903Certificate leaf3903InnerLog leaf3903Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk103RoundedFacts chi246RoundedFacts
    innerPair71RoundedFacts leaf3903RoundedFacts (by rfl)

private theorem leaf3903FlatSound : Sound leaf3903Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3903CertificateValid
    leaf3903InnerLogValid leaf3903CoversExact leaf3903LowerChecked

private noncomputable def leaf3904Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (9/32), chiHi := (37/128) }

private noncomputable def leaf3904Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435705/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905380864) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (473648665/268435456) }, upper := { exponent := 0, mantissa := (919/512) } }, logOuter := sk104LogOuterCertificate, logK := sk104LogKCertificate, logChi := chi245LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811545429/45810761728) } }, logDArg := sk104LogDArgCertificate }

private noncomputable def leaf3904InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3904LocalValidity :
    LeafFacts leaf3904Box leaf3904Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3904Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905380864) }) = true
      norm_num [leaf3904Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3904CertificateValid :
    WideCertificateValid leaf3904Box leaf3904Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk104ValidityFacts chi245ValidityFacts
    leaf3904LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3904CoverageChecked :
    coverageCheck (innerAD leaf3904Box) leaf3904InnerLog = true := by
  rfl'

private theorem leaf3904InnerLogValid :
    leaf3904InnerLog.Valid 8 (innerAD leaf3904Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3904CoverageChecked

private noncomputable def leaf3904InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453671/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3904InputLogOnePlusV_eq :
    leaf3904InputLogOnePlusV = outerEnclosure 24
      (leaf3904Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3904RoundedFacts : LeafRoundedFacts 8
    leaf3904Certificate.logOnePlusV leaf3904InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3904InputLogOnePlusV_eq }

private noncomputable def leaf3904Inputs : Inputs :=
  inputsOfCaches globalInput sk104RoundedInputs
    chi245InputQChi innerPair71Input
    leaf3904InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3904LowerChecked :
    lowerCheck 24 leaf3904Box leaf3904Inputs = true := by
  rfl'

private theorem leaf3904CoversExact : CoversExact 8
    leaf3904Box leaf3904Certificate leaf3904InnerLog leaf3904Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk104RoundedFacts chi245RoundedFacts
    innerPair71RoundedFacts leaf3904RoundedFacts (by rfl)

private theorem leaf3904FlatSound : Sound leaf3904Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3904CertificateValid
    leaf3904InnerLogValid leaf3904CoversExact leaf3904LowerChecked

private noncomputable def leaf3905Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (37/128), chiHi := (19/64) }

private noncomputable def leaf3905Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435707/268435456) }, vSqrt := { lower := (32765/32768), upper := (13743698739/13743210496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (479349947/268435456) }, upper := { exponent := 0, mantissa := (465/256) } }, logOuter := sk104LogOuterCertificate, logK := sk104LogKCertificate, logChi := chi246LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (27486909235/27486420992) } }, logDArg := sk104LogDArgCertificate }

private noncomputable def leaf3905InnerLog : WideLogData :=
  innerPair226Data

set_option maxRecDepth 1000000 in
private theorem leaf3905LocalValidity :
    LeafFacts leaf3905Box leaf3905Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3905Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (13743698739/13743210496) }) = true
      norm_num [leaf3905Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3905CertificateValid :
    WideCertificateValid leaf3905Box leaf3905Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk104ValidityFacts chi246ValidityFacts
    leaf3905LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3905CoverageChecked :
    coverageCheck (innerAD leaf3905Box) leaf3905InnerLog = true := by
  rfl'

private theorem leaf3905InnerLogValid :
    leaf3905InnerLog.Valid 8 (innerAD leaf3905Box) :=
  wideLogDataValid_of_cachedCheck endpoint68PositiveFacts
    endpoint64PositiveFacts.valid leaf3905CoverageChecked

private noncomputable def leaf3905InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629379/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3905InputLogOnePlusV_eq :
    leaf3905InputLogOnePlusV = outerEnclosure 24
      (leaf3905Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3905RoundedFacts : LeafRoundedFacts 8
    leaf3905Certificate.logOnePlusV leaf3905InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3905InputLogOnePlusV_eq }

private noncomputable def leaf3905Inputs : Inputs :=
  inputsOfCaches globalInput sk104RoundedInputs
    chi246InputQChi innerPair226Input
    leaf3905InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3905LowerChecked :
    lowerCheck 24 leaf3905Box leaf3905Inputs = true := by
  rfl'

private theorem leaf3905CoversExact : CoversExact 8
    leaf3905Box leaf3905Certificate leaf3905InnerLog leaf3905Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk104RoundedFacts chi246RoundedFacts
    innerPair226RoundedFacts leaf3905RoundedFacts (by rfl)

private theorem leaf3905FlatSound : Sound leaf3905Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3905CertificateValid
    leaf3905InnerLogValid leaf3905CoversExact leaf3905LowerChecked

private noncomputable def leaf3906Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (19/64), chiHi := (39/128) }

private noncomputable def leaf3906Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435707/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716002304) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (482561015/268435456) }, upper := { exponent := 0, mantissa := (7489/4096) } }, logOuter := sk103LogOuterCertificate, logK := sk103LogKCertificate, logChi := chi247LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434495999/137432004608) } }, logDArg := sk103LogDArgCertificate }

private noncomputable def leaf3906InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf3906LocalValidity :
    LeafFacts leaf3906Box leaf3906Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3906Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716002304) }) = true
      norm_num [leaf3906Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3906CertificateValid :
    WideCertificateValid leaf3906Box leaf3906Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk103ValidityFacts chi247ValidityFacts
    leaf3906LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3906CoverageChecked :
    coverageCheck (innerAD leaf3906Box) leaf3906InnerLog = true := by
  rfl'

private theorem leaf3906InnerLogValid :
    leaf3906InnerLog.Valid 8 (innerAD leaf3906Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf3906CoverageChecked

private noncomputable def leaf3906InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629385/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3906InputLogOnePlusV_eq :
    leaf3906InputLogOnePlusV = outerEnclosure 24
      (leaf3906Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3906RoundedFacts : LeafRoundedFacts 8
    leaf3906Certificate.logOnePlusV leaf3906InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3906InputLogOnePlusV_eq }

private noncomputable def leaf3906Inputs : Inputs :=
  inputsOfCaches globalInput sk103RoundedInputs
    chi247InputQChi innerPair72Input
    leaf3906InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3906LowerChecked :
    lowerCheck 24 leaf3906Box leaf3906Inputs = true := by
  rfl'

private theorem leaf3906CoversExact : CoversExact 8
    leaf3906Box leaf3906Certificate leaf3906InnerLog leaf3906Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk103RoundedFacts chi247RoundedFacts
    innerPair72RoundedFacts leaf3906RoundedFacts (by rfl)

private theorem leaf3906FlatSound : Sound leaf3906Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3906CertificateValid
    leaf3906InnerLogValid leaf3906CoversExact leaf3906LowerChecked

private noncomputable def leaf3907Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (39/128), chiHi := (5/16) }

private noncomputable def leaf3907Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435709/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715913216) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (488196765/268435456) }, upper := { exponent := 0, mantissa := (947/512) } }, logOuter := sk103LogOuterCertificate, logK := sk103LogKCertificate, logChi := chi248LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434406911/137431826432) } }, logDArg := sk103LogDArgCertificate }

private noncomputable def leaf3907InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3907LocalValidity :
    LeafFacts leaf3907Box leaf3907Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3907Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715913216) }) = true
      norm_num [leaf3907Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3907CertificateValid :
    WideCertificateValid leaf3907Box leaf3907Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk103ValidityFacts chi248ValidityFacts
    leaf3907LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3907CoverageChecked :
    coverageCheck (innerAD leaf3907Box) leaf3907InnerLog = true := by
  rfl'

private theorem leaf3907InnerLogValid :
    leaf3907InnerLog.Valid 8 (innerAD leaf3907Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3907CoverageChecked

private noncomputable def leaf3907InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907349/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3907InputLogOnePlusV_eq :
    leaf3907InputLogOnePlusV = outerEnclosure 24
      (leaf3907Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3907RoundedFacts : LeafRoundedFacts 8
    leaf3907Certificate.logOnePlusV leaf3907InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3907InputLogOnePlusV_eq }

private noncomputable def leaf3907Inputs : Inputs :=
  inputsOfCaches globalInput sk103RoundedInputs
    chi248InputQChi innerPair91Input
    leaf3907InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3907LowerChecked :
    lowerCheck 24 leaf3907Box leaf3907Inputs = true := by
  rfl'

private theorem leaf3907CoversExact : CoversExact 8
    leaf3907Box leaf3907Certificate leaf3907InnerLog leaf3907Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk103RoundedFacts chi248RoundedFacts
    innerPair91RoundedFacts leaf3907RoundedFacts (by rfl)

private theorem leaf3907FlatSound : Sound leaf3907Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3907CertificateValid
    leaf3907InnerLogValid leaf3907CoversExact leaf3907LowerChecked

private noncomputable def leaf3908Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (19/64), chiHi := (39/128) }

private noncomputable def leaf3908Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435709/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715962368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (485051229/268435456) }, upper := { exponent := 0, mantissa := (941/512) } }, logOuter := sk104LogOuterCertificate, logK := sk104LogKCertificate, logChi := chi247LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434456063/137431924736) } }, logDArg := sk104LogDArgCertificate }

private noncomputable def leaf3908InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf3908LocalValidity :
    LeafFacts leaf3908Box leaf3908Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3908Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715962368) }) = true
      norm_num [leaf3908Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3908CertificateValid :
    WideCertificateValid leaf3908Box leaf3908Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk104ValidityFacts chi247ValidityFacts
    leaf3908LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3908CoverageChecked :
    coverageCheck (innerAD leaf3908Box) leaf3908InnerLog = true := by
  rfl'

private theorem leaf3908InnerLogValid :
    leaf3908InnerLog.Valid 8 (innerAD leaf3908Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf3908CoverageChecked

private noncomputable def leaf3908InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814695/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3908InputLogOnePlusV_eq :
    leaf3908InputLogOnePlusV = outerEnclosure 24
      (leaf3908Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3908RoundedFacts : LeafRoundedFacts 8
    leaf3908Certificate.logOnePlusV leaf3908InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3908InputLogOnePlusV_eq }

private noncomputable def leaf3908Inputs : Inputs :=
  inputsOfCaches globalInput sk104RoundedInputs
    chi247InputQChi innerPair72Input
    leaf3908InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3908LowerChecked :
    lowerCheck 24 leaf3908Box leaf3908Inputs = true := by
  rfl'

private theorem leaf3908CoversExact : CoversExact 8
    leaf3908Box leaf3908Certificate leaf3908InnerLog leaf3908Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk104RoundedFacts chi247RoundedFacts
    innerPair72RoundedFacts leaf3908RoundedFacts (by rfl)

private theorem leaf3908FlatSound : Sound leaf3908Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3908CertificateValid
    leaf3908InnerLogValid leaf3908CoversExact leaf3908LowerChecked

private noncomputable def leaf3909Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (39/128), chiHi := (5/16) }

private noncomputable def leaf3909Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435711/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905290752) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (490752511/268435456) }, upper := { exponent := 0, mantissa := (119/64) } }, logOuter := sk104LogOuterCertificate, logK := sk104LogKCertificate, logChi := chi248LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811455317/45810581504) } }, logDArg := sk104LogDArgCertificate }

private noncomputable def leaf3909InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3909LocalValidity :
    LeafFacts leaf3909Box leaf3909Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3909Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905290752) }) = true
      norm_num [leaf3909Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3909CertificateValid :
    WideCertificateValid leaf3909Box leaf3909Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk104ValidityFacts chi248ValidityFacts
    leaf3909LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3909CoverageChecked :
    coverageCheck (innerAD leaf3909Box) leaf3909InnerLog = true := by
  rfl'

private theorem leaf3909InnerLogValid :
    leaf3909InnerLog.Valid 8 (innerAD leaf3909Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3909CoverageChecked

private noncomputable def leaf3909InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629401/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3909InputLogOnePlusV_eq :
    leaf3909InputLogOnePlusV = outerEnclosure 24
      (leaf3909Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3909RoundedFacts : LeafRoundedFacts 8
    leaf3909Certificate.logOnePlusV leaf3909InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3909InputLogOnePlusV_eq }

private noncomputable def leaf3909Inputs : Inputs :=
  inputsOfCaches globalInput sk104RoundedInputs
    chi248InputQChi innerPair91Input
    leaf3909InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3909LowerChecked :
    lowerCheck 24 leaf3909Box leaf3909Inputs = true := by
  rfl'

private theorem leaf3909CoversExact : CoversExact 8
    leaf3909Box leaf3909Certificate leaf3909InnerLog leaf3909Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk104RoundedFacts chi248RoundedFacts
    innerPair91RoundedFacts leaf3909RoundedFacts (by rfl)

private theorem leaf3909FlatSound : Sound leaf3909Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3909CertificateValid
    leaf3909InnerLogValid leaf3909CoversExact leaf3909LowerChecked

private noncomputable def component79Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (81/32), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component79Node0_sound : Sound component79Node0Box :=
  sound_of_literal_split component79Node0Box leaf3846Box leaf3847Box
    .chi (33/128) (by rfl) (by rfl)
    leaf3846FlatSound leaf3847FlatSound

private noncomputable def component79Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (81/32), kHi := (41/16), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component79Node1_sound : Sound component79Node1Box :=
  sound_of_literal_split component79Node1Box leaf3848Box leaf3849Box
    .chi (33/128) (by rfl) (by rfl)
    leaf3848FlatSound leaf3849FlatSound

private noncomputable def component79Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component79Node2_sound : Sound component79Node2Box :=
  sound_of_literal_split component79Node2Box component79Node0Box component79Node1Box
    .k (81/32) (by rfl) (by rfl)
    component79Node0_sound component79Node1_sound

private noncomputable def component79Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (81/32), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component79Node3_sound : Sound component79Node3Box :=
  sound_of_literal_split component79Node3Box leaf3850Box leaf3851Box
    .chi (35/128) (by rfl) (by rfl)
    leaf3850FlatSound leaf3851FlatSound

private noncomputable def component79Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (81/32), kHi := (41/16), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component79Node4_sound : Sound component79Node4Box :=
  sound_of_literal_split component79Node4Box leaf3852Box leaf3853Box
    .chi (35/128) (by rfl) (by rfl)
    leaf3852FlatSound leaf3853FlatSound

private noncomputable def component79Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component79Node5_sound : Sound component79Node5Box :=
  sound_of_literal_split component79Node5Box component79Node3Box component79Node4Box
    .k (81/32) (by rfl) (by rfl)
    component79Node3_sound component79Node4_sound

private noncomputable def component79Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (1/4), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component79Node6_sound : Sound component79Node6Box :=
  sound_of_literal_split component79Node6Box component79Node2Box component79Node5Box
    .chi (17/64) (by rfl) (by rfl)
    component79Node2_sound component79Node5_sound

private noncomputable def component79Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (83/32), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component79Node7_sound : Sound component79Node7Box :=
  sound_of_literal_split component79Node7Box leaf3854Box leaf3855Box
    .chi (33/128) (by rfl) (by rfl)
    leaf3854FlatSound leaf3855FlatSound

private noncomputable def component79Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (83/32), kHi := (21/8), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component79Node8_sound : Sound component79Node8Box :=
  sound_of_literal_split component79Node8Box leaf3856Box leaf3857Box
    .chi (33/128) (by rfl) (by rfl)
    leaf3856FlatSound leaf3857FlatSound

private noncomputable def component79Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component79Node9_sound : Sound component79Node9Box :=
  sound_of_literal_split component79Node9Box component79Node7Box component79Node8Box
    .k (83/32) (by rfl) (by rfl)
    component79Node7_sound component79Node8_sound

private noncomputable def component79Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (83/32), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component79Node10_sound : Sound component79Node10Box :=
  sound_of_literal_split component79Node10Box leaf3858Box leaf3859Box
    .chi (35/128) (by rfl) (by rfl)
    leaf3858FlatSound leaf3859FlatSound

private noncomputable def component79Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (83/32), kHi := (21/8), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component79Node11_sound : Sound component79Node11Box :=
  sound_of_literal_split component79Node11Box leaf3860Box leaf3861Box
    .chi (35/128) (by rfl) (by rfl)
    leaf3860FlatSound leaf3861FlatSound

private noncomputable def component79Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component79Node12_sound : Sound component79Node12Box :=
  sound_of_literal_split component79Node12Box component79Node10Box component79Node11Box
    .k (83/32) (by rfl) (by rfl)
    component79Node10_sound component79Node11_sound

private noncomputable def component79Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (1/4), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component79Node13_sound : Sound component79Node13Box :=
  sound_of_literal_split component79Node13Box component79Node9Box component79Node12Box
    .chi (17/64) (by rfl) (by rfl)
    component79Node9_sound component79Node12_sound

private noncomputable def component79Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (1/4), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component79Node14_sound : Sound component79Node14Box :=
  sound_of_literal_split component79Node14Box component79Node6Box component79Node13Box
    .k (41/16) (by rfl) (by rfl)
    component79Node6_sound component79Node13_sound

private noncomputable def component79Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (81/32), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component79Node15_sound : Sound component79Node15Box :=
  sound_of_literal_split component79Node15Box leaf3862Box leaf3863Box
    .chi (37/128) (by rfl) (by rfl)
    leaf3862FlatSound leaf3863FlatSound

private noncomputable def component79Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (81/32), kHi := (41/16), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component79Node16_sound : Sound component79Node16Box :=
  sound_of_literal_split component79Node16Box leaf3864Box leaf3865Box
    .chi (37/128) (by rfl) (by rfl)
    leaf3864FlatSound leaf3865FlatSound

private noncomputable def component79Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component79Node17_sound : Sound component79Node17Box :=
  sound_of_literal_split component79Node17Box component79Node15Box component79Node16Box
    .k (81/32) (by rfl) (by rfl)
    component79Node15_sound component79Node16_sound

private noncomputable def component79Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (81/32), chiLo := (19/64), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component79Node18_sound : Sound component79Node18Box :=
  sound_of_literal_split component79Node18Box leaf3866Box leaf3867Box
    .chi (39/128) (by rfl) (by rfl)
    leaf3866FlatSound leaf3867FlatSound

private noncomputable def component79Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (81/32), kHi := (41/16), chiLo := (19/64), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component79Node19_sound : Sound component79Node19Box :=
  sound_of_literal_split component79Node19Box leaf3868Box leaf3869Box
    .chi (39/128) (by rfl) (by rfl)
    leaf3868FlatSound leaf3869FlatSound

private noncomputable def component79Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (19/64), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component79Node20_sound : Sound component79Node20Box :=
  sound_of_literal_split component79Node20Box component79Node18Box component79Node19Box
    .k (81/32) (by rfl) (by rfl)
    component79Node18_sound component79Node19_sound

private noncomputable def component79Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (9/32), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component79Node21_sound : Sound component79Node21Box :=
  sound_of_literal_split component79Node21Box component79Node17Box component79Node20Box
    .chi (19/64) (by rfl) (by rfl)
    component79Node17_sound component79Node20_sound

private noncomputable def component79Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (83/32), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component79Node22_sound : Sound component79Node22Box :=
  sound_of_literal_split component79Node22Box leaf3870Box leaf3871Box
    .chi (37/128) (by rfl) (by rfl)
    leaf3870FlatSound leaf3871FlatSound

private noncomputable def component79Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (83/32), kHi := (21/8), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component79Node23_sound : Sound component79Node23Box :=
  sound_of_literal_split component79Node23Box leaf3872Box leaf3873Box
    .chi (37/128) (by rfl) (by rfl)
    leaf3872FlatSound leaf3873FlatSound

private noncomputable def component79Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component79Node24_sound : Sound component79Node24Box :=
  sound_of_literal_split component79Node24Box component79Node22Box component79Node23Box
    .k (83/32) (by rfl) (by rfl)
    component79Node22_sound component79Node23_sound

private noncomputable def component79Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (83/32), chiLo := (19/64), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component79Node25_sound : Sound component79Node25Box :=
  sound_of_literal_split component79Node25Box leaf3874Box leaf3875Box
    .chi (39/128) (by rfl) (by rfl)
    leaf3874FlatSound leaf3875FlatSound

private noncomputable def component79Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (83/32), kHi := (21/8), chiLo := (19/64), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component79Node26_sound : Sound component79Node26Box :=
  sound_of_literal_split component79Node26Box leaf3876Box leaf3877Box
    .chi (39/128) (by rfl) (by rfl)
    leaf3876FlatSound leaf3877FlatSound

private noncomputable def component79Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (19/64), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component79Node27_sound : Sound component79Node27Box :=
  sound_of_literal_split component79Node27Box component79Node25Box component79Node26Box
    .k (83/32) (by rfl) (by rfl)
    component79Node25_sound component79Node26_sound

private noncomputable def component79Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (9/32), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component79Node28_sound : Sound component79Node28Box :=
  sound_of_literal_split component79Node28Box component79Node24Box component79Node27Box
    .chi (19/64) (by rfl) (by rfl)
    component79Node24_sound component79Node27_sound

private noncomputable def component79Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (9/32), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component79Node29_sound : Sound component79Node29Box :=
  sound_of_literal_split component79Node29Box component79Node21Box component79Node28Box
    .k (41/16) (by rfl) (by rfl)
    component79Node21_sound component79Node28_sound

private noncomputable def component79Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (1/4), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component79Node30_sound : Sound component79Node30Box :=
  sound_of_literal_split component79Node30Box component79Node14Box component79Node29Box
    .chi (9/32) (by rfl) (by rfl)
    component79Node14_sound component79Node29_sound

private noncomputable def component79Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (85/32), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component79Node31_sound : Sound component79Node31Box :=
  sound_of_literal_split component79Node31Box leaf3878Box leaf3879Box
    .chi (33/128) (by rfl) (by rfl)
    leaf3878FlatSound leaf3879FlatSound

private noncomputable def component79Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (85/32), kHi := (43/16), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component79Node32_sound : Sound component79Node32Box :=
  sound_of_literal_split component79Node32Box leaf3880Box leaf3881Box
    .chi (33/128) (by rfl) (by rfl)
    leaf3880FlatSound leaf3881FlatSound

private noncomputable def component79Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component79Node33_sound : Sound component79Node33Box :=
  sound_of_literal_split component79Node33Box component79Node31Box component79Node32Box
    .k (85/32) (by rfl) (by rfl)
    component79Node31_sound component79Node32_sound

private noncomputable def component79Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (85/32), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component79Node34_sound : Sound component79Node34Box :=
  sound_of_literal_split component79Node34Box leaf3882Box leaf3883Box
    .chi (35/128) (by rfl) (by rfl)
    leaf3882FlatSound leaf3883FlatSound

private noncomputable def component79Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (85/32), kHi := (43/16), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component79Node35_sound : Sound component79Node35Box :=
  sound_of_literal_split component79Node35Box leaf3884Box leaf3885Box
    .chi (35/128) (by rfl) (by rfl)
    leaf3884FlatSound leaf3885FlatSound

private noncomputable def component79Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component79Node36_sound : Sound component79Node36Box :=
  sound_of_literal_split component79Node36Box component79Node34Box component79Node35Box
    .k (85/32) (by rfl) (by rfl)
    component79Node34_sound component79Node35_sound

private noncomputable def component79Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (1/4), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component79Node37_sound : Sound component79Node37Box :=
  sound_of_literal_split component79Node37Box component79Node33Box component79Node36Box
    .chi (17/64) (by rfl) (by rfl)
    component79Node33_sound component79Node36_sound

private noncomputable def component79Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component79Node38_sound : Sound component79Node38Box :=
  sound_of_literal_split component79Node38Box leaf3886Box leaf3887Box
    .chi (33/128) (by rfl) (by rfl)
    leaf3886FlatSound leaf3887FlatSound

private noncomputable def component79Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component79Node39_sound : Sound component79Node39Box :=
  sound_of_literal_split component79Node39Box leaf3888Box leaf3889Box
    .chi (33/128) (by rfl) (by rfl)
    leaf3888FlatSound leaf3889FlatSound

private noncomputable def component79Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component79Node40_sound : Sound component79Node40Box :=
  sound_of_literal_split component79Node40Box component79Node38Box component79Node39Box
    .k (87/32) (by rfl) (by rfl)
    component79Node38_sound component79Node39_sound

private noncomputable def component79Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component79Node41_sound : Sound component79Node41Box :=
  sound_of_literal_split component79Node41Box leaf3890Box leaf3891Box
    .chi (35/128) (by rfl) (by rfl)
    leaf3890FlatSound leaf3891FlatSound

private noncomputable def component79Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component79Node42_sound : Sound component79Node42Box :=
  sound_of_literal_split component79Node42Box leaf3892Box leaf3893Box
    .chi (35/128) (by rfl) (by rfl)
    leaf3892FlatSound leaf3893FlatSound

private noncomputable def component79Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component79Node43_sound : Sound component79Node43Box :=
  sound_of_literal_split component79Node43Box component79Node41Box component79Node42Box
    .k (87/32) (by rfl) (by rfl)
    component79Node41_sound component79Node42_sound

private noncomputable def component79Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (1/4), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component79Node44_sound : Sound component79Node44Box :=
  sound_of_literal_split component79Node44Box component79Node40Box component79Node43Box
    .chi (17/64) (by rfl) (by rfl)
    component79Node40_sound component79Node43_sound

private noncomputable def component79Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (1/4), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component79Node45_sound : Sound component79Node45Box :=
  sound_of_literal_split component79Node45Box component79Node37Box component79Node44Box
    .k (43/16) (by rfl) (by rfl)
    component79Node37_sound component79Node44_sound

private noncomputable def component79Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (85/32), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component79Node46_sound : Sound component79Node46Box :=
  sound_of_literal_split component79Node46Box leaf3894Box leaf3895Box
    .chi (37/128) (by rfl) (by rfl)
    leaf3894FlatSound leaf3895FlatSound

private noncomputable def component79Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (85/32), kHi := (43/16), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component79Node47_sound : Sound component79Node47Box :=
  sound_of_literal_split component79Node47Box leaf3896Box leaf3897Box
    .chi (37/128) (by rfl) (by rfl)
    leaf3896FlatSound leaf3897FlatSound

private noncomputable def component79Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component79Node48_sound : Sound component79Node48Box :=
  sound_of_literal_split component79Node48Box component79Node46Box component79Node47Box
    .k (85/32) (by rfl) (by rfl)
    component79Node46_sound component79Node47_sound

private noncomputable def component79Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (85/32), chiLo := (19/64), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component79Node49_sound : Sound component79Node49Box :=
  sound_of_literal_split component79Node49Box leaf3898Box leaf3899Box
    .chi (39/128) (by rfl) (by rfl)
    leaf3898FlatSound leaf3899FlatSound

private noncomputable def component79Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (85/32), kHi := (43/16), chiLo := (19/64), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component79Node50_sound : Sound component79Node50Box :=
  sound_of_literal_split component79Node50Box leaf3900Box leaf3901Box
    .chi (39/128) (by rfl) (by rfl)
    leaf3900FlatSound leaf3901FlatSound

private noncomputable def component79Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (19/64), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component79Node51_sound : Sound component79Node51Box :=
  sound_of_literal_split component79Node51Box component79Node49Box component79Node50Box
    .k (85/32) (by rfl) (by rfl)
    component79Node49_sound component79Node50_sound

private noncomputable def component79Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (9/32), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component79Node52_sound : Sound component79Node52Box :=
  sound_of_literal_split component79Node52Box component79Node48Box component79Node51Box
    .chi (19/64) (by rfl) (by rfl)
    component79Node48_sound component79Node51_sound

private noncomputable def component79Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component79Node53_sound : Sound component79Node53Box :=
  sound_of_literal_split component79Node53Box leaf3902Box leaf3903Box
    .chi (37/128) (by rfl) (by rfl)
    leaf3902FlatSound leaf3903FlatSound

private noncomputable def component79Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component79Node54_sound : Sound component79Node54Box :=
  sound_of_literal_split component79Node54Box leaf3904Box leaf3905Box
    .chi (37/128) (by rfl) (by rfl)
    leaf3904FlatSound leaf3905FlatSound

private noncomputable def component79Node55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component79Node55_sound : Sound component79Node55Box :=
  sound_of_literal_split component79Node55Box component79Node53Box component79Node54Box
    .k (87/32) (by rfl) (by rfl)
    component79Node53_sound component79Node54_sound

private noncomputable def component79Node56Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (19/64), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component79Node56_sound : Sound component79Node56Box :=
  sound_of_literal_split component79Node56Box leaf3906Box leaf3907Box
    .chi (39/128) (by rfl) (by rfl)
    leaf3906FlatSound leaf3907FlatSound

private noncomputable def component79Node57Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (19/64), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component79Node57_sound : Sound component79Node57Box :=
  sound_of_literal_split component79Node57Box leaf3908Box leaf3909Box
    .chi (39/128) (by rfl) (by rfl)
    leaf3908FlatSound leaf3909FlatSound

private noncomputable def component79Node58Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (19/64), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component79Node58_sound : Sound component79Node58Box :=
  sound_of_literal_split component79Node58Box component79Node56Box component79Node57Box
    .k (87/32) (by rfl) (by rfl)
    component79Node56_sound component79Node57_sound

private noncomputable def component79Node59Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (9/32), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component79Node59_sound : Sound component79Node59Box :=
  sound_of_literal_split component79Node59Box component79Node55Box component79Node58Box
    .chi (19/64) (by rfl) (by rfl)
    component79Node55_sound component79Node58_sound

private noncomputable def component79Node60Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (9/32), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component79Node60_sound : Sound component79Node60Box :=
  sound_of_literal_split component79Node60Box component79Node52Box component79Node59Box
    .k (43/16) (by rfl) (by rfl)
    component79Node52_sound component79Node59_sound

private noncomputable def component79Node61Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (1/4), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component79Node61_sound : Sound component79Node61Box :=
  sound_of_literal_split component79Node61Box component79Node45Box component79Node60Box
    .chi (9/32) (by rfl) (by rfl)
    component79Node45_sound component79Node60_sound

noncomputable def component79Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (11/4), chiLo := (1/4), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
theorem component79_sound : Sound component79Box :=
  sound_of_literal_split component79Box component79Node30Box component79Node61Box
    .k (21/8) (by rfl) (by rfl)
    component79Node30_sound component79Node61_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
