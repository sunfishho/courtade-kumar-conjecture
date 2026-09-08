import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
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

private noncomputable def leaf3995Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32), chiLo := (1/4), chiHi := (33/128) }

private noncomputable def leaf3995Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435707/268435456) }, vSqrt := { lower := (32765/32768), upper := (13743698739/13743266816) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (461328647/268435456) }, upper := { exponent := 0, mantissa := (7165/4096) } }, logOuter := sk111LogOuterCertificate, logK := sk111LogKCertificate, logChi := chi241LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (27486965555/27486533632) } }, logDArg := sk111LogDArgCertificate }

private noncomputable def leaf3995InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3995LocalValidity :
    LeafFacts leaf3995Box leaf3995Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3995Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (13743698739/13743266816) }) = true
      norm_num [leaf3995Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3995CertificateValid :
    WideCertificateValid leaf3995Box leaf3995Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk111ValidityFacts chi241ValidityFacts
    leaf3995LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3995CoverageChecked :
    coverageCheck (innerAD leaf3995Box) leaf3995InnerLog = true := by
  rfl'

private theorem leaf3995InnerLogValid :
    leaf3995InnerLog.Valid 8 (innerAD leaf3995Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3995CoverageChecked

private noncomputable def leaf3995InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (363417/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf3995InputLogOnePlusV_eq :
    leaf3995InputLogOnePlusV = outerEnclosure 24
      (leaf3995Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3995RoundedFacts : LeafRoundedFacts 8
    leaf3995Certificate.logOnePlusV leaf3995InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3995InputLogOnePlusV_eq }

private noncomputable def leaf3995Inputs : Inputs :=
  inputsOfCaches globalInput sk111RoundedInputs
    chi241InputQChi innerPair64Input
    leaf3995InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3995LowerChecked :
    lowerCheck 24 leaf3995Box leaf3995Inputs = true := by
  rfl'

private theorem leaf3995CoversExact : CoversExact 8
    leaf3995Box leaf3995Certificate leaf3995InnerLog leaf3995Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk111RoundedFacts chi241RoundedFacts
    innerPair64RoundedFacts leaf3995RoundedFacts (by rfl)

private theorem leaf3995FlatSound : Sound leaf3995Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3995CertificateValid
    leaf3995InnerLogValid leaf3995CoversExact leaf3995LowerChecked

private noncomputable def leaf3996Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32), chiLo := (33/128), chiHi := (17/64) }

private noncomputable def leaf3996Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435709/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716238848) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (467357589/268435456) }, upper := { exponent := 0, mantissa := (3629/2048) } }, logOuter := sk111LogOuterCertificate, logK := sk111LogKCertificate, logChi := chi242LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434732543/137432477696) } }, logDArg := sk111LogDArgCertificate }

private noncomputable def leaf3996InnerLog : WideLogData :=
  innerPair431Data

set_option maxRecDepth 1000000 in
private theorem leaf3996LocalValidity :
    LeafFacts leaf3996Box leaf3996Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3996Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716238848) }) = true
      norm_num [leaf3996Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3996CertificateValid :
    WideCertificateValid leaf3996Box leaf3996Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk111ValidityFacts chi242ValidityFacts
    leaf3996LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3996CoverageChecked :
    coverageCheck (innerAD leaf3996Box) leaf3996InnerLog = true := by
  rfl'

private theorem leaf3996InnerLogValid :
    leaf3996InnerLog.Valid 8 (innerAD leaf3996Box) :=
  wideLogDataValid_of_cachedCheck endpoint139PositiveFacts
    endpoint68PositiveFacts.valid leaf3996CoverageChecked

private noncomputable def leaf3996InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907339/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3996InputLogOnePlusV_eq :
    leaf3996InputLogOnePlusV = outerEnclosure 24
      (leaf3996Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3996RoundedFacts : LeafRoundedFacts 8
    leaf3996Certificate.logOnePlusV leaf3996InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3996InputLogOnePlusV_eq }

private noncomputable def leaf3996Inputs : Inputs :=
  inputsOfCaches globalInput sk111RoundedInputs
    chi242InputQChi innerPair431Input
    leaf3996InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3996LowerChecked :
    lowerCheck 24 leaf3996Box leaf3996Inputs = true := by
  rfl'

private theorem leaf3996CoversExact : CoversExact 8
    leaf3996Box leaf3996Certificate leaf3996InnerLog leaf3996Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk111RoundedFacts chi242RoundedFacts
    innerPair431RoundedFacts leaf3996RoundedFacts (by rfl)

private theorem leaf3996FlatSound : Sound leaf3996Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3996CertificateValid
    leaf3996InnerLogValid leaf3996CoversExact leaf3996LowerChecked

private noncomputable def leaf3997Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16), chiLo := (1/4), chiHi := (33/128) }

private noncomputable def leaf3997Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435709/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716300288) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (463425669/268435456) }, upper := { exponent := 0, mantissa := (3599/2048) } }, logOuter := sk112LogOuterCertificate, logK := sk112LogKCertificate, logChi := chi241LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434793983/137432600576) } }, logDArg := sk112LogDArgCertificate }

private noncomputable def leaf3997InnerLog : WideLogData :=
  innerPair459Data

set_option maxRecDepth 1000000 in
private theorem leaf3997LocalValidity :
    LeafFacts leaf3997Box leaf3997Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3997Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716300288) }) = true
      norm_num [leaf3997Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3997CertificateValid :
    WideCertificateValid leaf3997Box leaf3997Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk112ValidityFacts chi241ValidityFacts
    leaf3997LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3997CoverageChecked :
    coverageCheck (innerAD leaf3997Box) leaf3997InnerLog = true := by
  rfl'

private theorem leaf3997InnerLogValid :
    leaf3997InnerLog.Valid 8 (innerAD leaf3997Box) :=
  wideLogDataValid_of_cachedCheck endpoint179PositiveFacts
    endpoint66PositiveFacts.valid leaf3997CoverageChecked

private noncomputable def leaf3997InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629349/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3997InputLogOnePlusV_eq :
    leaf3997InputLogOnePlusV = outerEnclosure 24
      (leaf3997Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3997RoundedFacts : LeafRoundedFacts 8
    leaf3997Certificate.logOnePlusV leaf3997InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3997InputLogOnePlusV_eq }

private noncomputable def leaf3997Inputs : Inputs :=
  inputsOfCaches globalInput sk112RoundedInputs
    chi241InputQChi innerPair459Input
    leaf3997InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3997LowerChecked :
    lowerCheck 24 leaf3997Box leaf3997Inputs = true := by
  rfl'

private theorem leaf3997CoversExact : CoversExact 8
    leaf3997Box leaf3997Certificate leaf3997InnerLog leaf3997Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk112RoundedFacts chi241RoundedFacts
    innerPair459RoundedFacts leaf3997RoundedFacts (by rfl)

private theorem leaf3997FlatSound : Sound leaf3997Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3997CertificateValid
    leaf3997InnerLogValid leaf3997CoversExact leaf3997LowerChecked

private noncomputable def leaf3998Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16), chiLo := (33/128), chiHi := (17/64) }

private noncomputable def leaf3998Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435711/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905401344) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (469520143/268435456) }, upper := { exponent := 0, mantissa := (1823/1024) } }, logOuter := sk112LogOuterCertificate, logK := sk112LogKCertificate, logChi := chi242LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811565909/45810802688) } }, logDArg := sk112LogDArgCertificate }

private noncomputable def leaf3998InnerLog : WideLogData :=
  innerPair431Data

set_option maxRecDepth 1000000 in
private theorem leaf3998LocalValidity :
    LeafFacts leaf3998Box leaf3998Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3998Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905401344) }) = true
      norm_num [leaf3998Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3998CertificateValid :
    WideCertificateValid leaf3998Box leaf3998Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk112ValidityFacts chi242ValidityFacts
    leaf3998LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3998CoverageChecked :
    coverageCheck (innerAD leaf3998Box) leaf3998InnerLog = true := by
  rfl'

private theorem leaf3998InnerLogValid :
    leaf3998InnerLog.Valid 8 (innerAD leaf3998Box) :=
  wideLogDataValid_of_cachedCheck endpoint139PositiveFacts
    endpoint68PositiveFacts.valid leaf3998CoverageChecked

private noncomputable def leaf3998InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (726835/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf3998InputLogOnePlusV_eq :
    leaf3998InputLogOnePlusV = outerEnclosure 24
      (leaf3998Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3998RoundedFacts : LeafRoundedFacts 8
    leaf3998Certificate.logOnePlusV leaf3998InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3998InputLogOnePlusV_eq }

private noncomputable def leaf3998Inputs : Inputs :=
  inputsOfCaches globalInput sk112RoundedInputs
    chi242InputQChi innerPair431Input
    leaf3998InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3998LowerChecked :
    lowerCheck 24 leaf3998Box leaf3998Inputs = true := by
  rfl'

private theorem leaf3998CoversExact : CoversExact 8
    leaf3998Box leaf3998Certificate leaf3998InnerLog leaf3998Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk112RoundedFacts chi242RoundedFacts
    innerPair431RoundedFacts leaf3998RoundedFacts (by rfl)

private theorem leaf3998FlatSound : Sound leaf3998Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3998CertificateValid
    leaf3998InnerLogValid leaf3998CoversExact leaf3998LowerChecked

private noncomputable def leaf3999Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32), chiLo := (17/64), chiHi := (35/128) }

private noncomputable def leaf3999Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435711/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716143616) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (473386531/268435456) }, upper := { exponent := 0, mantissa := (7351/4096) } }, logOuter := sk111LogOuterCertificate, logK := sk111LogKCertificate, logChi := chi243LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434637311/137432287232) } }, logDArg := sk111LogDArgCertificate }

private noncomputable def leaf3999InnerLog : WideLogData :=
  innerPair77Data

set_option maxRecDepth 1000000 in
private theorem leaf3999LocalValidity :
    LeafFacts leaf3999Box leaf3999Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3999Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716143616) }) = true
      norm_num [leaf3999Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3999CertificateValid :
    WideCertificateValid leaf3999Box leaf3999Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk111ValidityFacts chi243ValidityFacts
    leaf3999LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3999CoverageChecked :
    coverageCheck (innerAD leaf3999Box) leaf3999InnerLog = true := by
  rfl'

private theorem leaf3999InnerLogValid :
    leaf3999InnerLog.Valid 8 (innerAD leaf3999Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint67PositiveFacts.valid leaf3999CoverageChecked

private noncomputable def leaf3999InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453671/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3999InputLogOnePlusV_eq :
    leaf3999InputLogOnePlusV = outerEnclosure 24
      (leaf3999Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3999RoundedFacts : LeafRoundedFacts 8
    leaf3999Certificate.logOnePlusV leaf3999InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3999InputLogOnePlusV_eq }

private noncomputable def leaf3999Inputs : Inputs :=
  inputsOfCaches globalInput sk111RoundedInputs
    chi243InputQChi innerPair77Input
    leaf3999InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3999LowerChecked :
    lowerCheck 24 leaf3999Box leaf3999Inputs = true := by
  rfl'

private theorem leaf3999CoversExact : CoversExact 8
    leaf3999Box leaf3999Certificate leaf3999InnerLog leaf3999Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk111RoundedFacts chi243RoundedFacts
    innerPair77RoundedFacts leaf3999RoundedFacts (by rfl)

private theorem leaf3999FlatSound : Sound leaf3999Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3999CertificateValid
    leaf3999InnerLogValid leaf3999CoversExact leaf3999LowerChecked

private noncomputable def leaf4000Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32), chiLo := (35/128), chiHi := (9/32) }

private noncomputable def leaf4000Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435713/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716048384) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (479415473/268435456) }, upper := { exponent := 0, mantissa := (1861/1024) } }, logOuter := sk111LogOuterCertificate, logK := sk111LogKCertificate, logChi := chi244LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434542079/137432096768) } }, logDArg := sk111LogDArgCertificate }

private noncomputable def leaf4000InnerLog : WideLogData :=
  innerPair226Data

set_option maxRecDepth 1000000 in
private theorem leaf4000LocalValidity :
    LeafFacts leaf4000Box leaf4000Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4000Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716048384) }) = true
      norm_num [leaf4000Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4000CertificateValid :
    WideCertificateValid leaf4000Box leaf4000Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk111ValidityFacts chi244ValidityFacts
    leaf4000LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4000CoverageChecked :
    coverageCheck (innerAD leaf4000Box) leaf4000InnerLog = true := by
  rfl'

private theorem leaf4000InnerLogValid :
    leaf4000InnerLog.Valid 8 (innerAD leaf4000Box) :=
  wideLogDataValid_of_cachedCheck endpoint68PositiveFacts
    endpoint64PositiveFacts.valid leaf4000CoverageChecked

private noncomputable def leaf4000InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629379/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4000InputLogOnePlusV_eq :
    leaf4000InputLogOnePlusV = outerEnclosure 24
      (leaf4000Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4000RoundedFacts : LeafRoundedFacts 8
    leaf4000Certificate.logOnePlusV leaf4000InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4000InputLogOnePlusV_eq }

private noncomputable def leaf4000Inputs : Inputs :=
  inputsOfCaches globalInput sk111RoundedInputs
    chi244InputQChi innerPair226Input
    leaf4000InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4000LowerChecked :
    lowerCheck 24 leaf4000Box leaf4000Inputs = true := by
  rfl'

private theorem leaf4000CoversExact : CoversExact 8
    leaf4000Box leaf4000Certificate leaf4000InnerLog leaf4000Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk111RoundedFacts chi244RoundedFacts
    innerPair226RoundedFacts leaf4000RoundedFacts (by rfl)

private theorem leaf4000FlatSound : Sound leaf4000Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4000CertificateValid
    leaf4000InnerLogValid leaf4000CoversExact leaf4000LowerChecked

private noncomputable def leaf4001Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16), chiLo := (17/64), chiHi := (35/128) }

private noncomputable def leaf4001Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435713/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716107776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (475614617/268435456) }, upper := { exponent := 0, mantissa := (3693/2048) } }, logOuter := sk112LogOuterCertificate, logK := sk112LogKCertificate, logChi := chi243LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434601471/137432215552) } }, logDArg := sk112LogDArgCertificate }

private noncomputable def leaf4001InnerLog : WideLogData :=
  innerPair492Data

set_option maxRecDepth 1000000 in
private theorem leaf4001LocalValidity :
    LeafFacts leaf4001Box leaf4001Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4001Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716107776) }) = true
      norm_num [leaf4001Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4001CertificateValid :
    WideCertificateValid leaf4001Box leaf4001Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk112ValidityFacts chi243ValidityFacts
    leaf4001LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4001CoverageChecked :
    coverageCheck (innerAD leaf4001Box) leaf4001InnerLog = true := by
  rfl'

private theorem leaf4001InnerLogValid :
    leaf4001InnerLog.Valid 8 (innerAD leaf4001Box) :=
  wideLogDataValid_of_cachedCheck endpoint216PositiveFacts
    endpoint185PositiveFacts.valid leaf4001CoverageChecked

private noncomputable def leaf4001InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907343/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4001InputLogOnePlusV_eq :
    leaf4001InputLogOnePlusV = outerEnclosure 24
      (leaf4001Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4001RoundedFacts : LeafRoundedFacts 8
    leaf4001Certificate.logOnePlusV leaf4001InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4001InputLogOnePlusV_eq }

private noncomputable def leaf4001Inputs : Inputs :=
  inputsOfCaches globalInput sk112RoundedInputs
    chi243InputQChi innerPair492Input
    leaf4001InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4001LowerChecked :
    lowerCheck 24 leaf4001Box leaf4001Inputs = true := by
  rfl'

private theorem leaf4001CoversExact : CoversExact 8
    leaf4001Box leaf4001Certificate leaf4001InnerLog leaf4001Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk112RoundedFacts chi243RoundedFacts
    innerPair492RoundedFacts leaf4001RoundedFacts (by rfl)

private theorem leaf4001FlatSound : Sound leaf4001Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4001CertificateValid
    leaf4001InnerLogValid leaf4001CoversExact leaf4001LowerChecked

private noncomputable def leaf4002Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16), chiLo := (35/128), chiHi := (9/32) }

private noncomputable def leaf4002Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435715/268435456) }, vSqrt := { lower := (32765/32768), upper := (13743698739/13743202304) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (481709091/268435456) }, upper := { exponent := 0, mantissa := (935/512) } }, logOuter := sk112LogOuterCertificate, logK := sk112LogKCertificate, logChi := chi244LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (27486901043/27486404608) } }, logDArg := sk112LogDArgCertificate }

private noncomputable def leaf4002InnerLog : WideLogData :=
  innerPair226Data

set_option maxRecDepth 1000000 in
private theorem leaf4002LocalValidity :
    LeafFacts leaf4002Box leaf4002Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4002Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (13743698739/13743202304) }) = true
      norm_num [leaf4002Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4002CertificateValid :
    WideCertificateValid leaf4002Box leaf4002Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk112ValidityFacts chi244ValidityFacts
    leaf4002LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4002CoverageChecked :
    coverageCheck (innerAD leaf4002Box) leaf4002InnerLog = true := by
  rfl'

private theorem leaf4002InnerLogValid :
    leaf4002InnerLog.Valid 8 (innerAD leaf4002Box) :=
  wideLogDataValid_of_cachedCheck endpoint68PositiveFacts
    endpoint64PositiveFacts.valid leaf4002CoverageChecked

private noncomputable def leaf4002InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453673/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf4002InputLogOnePlusV_eq :
    leaf4002InputLogOnePlusV = outerEnclosure 24
      (leaf4002Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4002RoundedFacts : LeafRoundedFacts 8
    leaf4002Certificate.logOnePlusV leaf4002InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4002InputLogOnePlusV_eq }

private noncomputable def leaf4002Inputs : Inputs :=
  inputsOfCaches globalInput sk112RoundedInputs
    chi244InputQChi innerPair226Input
    leaf4002InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4002LowerChecked :
    lowerCheck 24 leaf4002Box leaf4002Inputs = true := by
  rfl'

private theorem leaf4002CoversExact : CoversExact 8
    leaf4002Box leaf4002Certificate leaf4002InnerLog leaf4002Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk112RoundedFacts chi244RoundedFacts
    innerPair226RoundedFacts leaf4002RoundedFacts (by rfl)

private theorem leaf4002FlatSound : Sound leaf4002Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4002CertificateValid
    leaf4002InnerLogValid leaf4002CoversExact leaf4002LowerChecked

private noncomputable def leaf4003Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (189/64), chiLo := (1/4), chiHi := (33/128) }

private noncomputable def leaf4003Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871355/536870912) }, vSqrt := { lower := (32765/32768), upper := (137436921855/137432566784) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (931078215/536870912) }, upper := { exponent := 0, mantissa := (14429/8192) } }, logOuter := sk115LogOuterCertificate, logK := sk115LogKCertificate, logChi := chi241LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (274869488639/274865133568) } }, logDArg := sk115LogDArgCertificate }

private noncomputable def leaf4003InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf4003LocalValidity :
    LeafFacts leaf4003Box leaf4003Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4003Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (137436921855/137432566784) }) = true
      norm_num [leaf4003Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4003CertificateValid :
    WideCertificateValid leaf4003Box leaf4003Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk115ValidityFacts chi241ValidityFacts
    leaf4003LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4003CoverageChecked :
    coverageCheck (innerAD leaf4003Box) leaf4003InnerLog = true := by
  rfl'

private theorem leaf4003InnerLogValid :
    leaf4003InnerLog.Valid 8 (innerAD leaf4003Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf4003CoverageChecked

private noncomputable def leaf4003InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629347/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4003InputLogOnePlusV_eq :
    leaf4003InputLogOnePlusV = outerEnclosure 24
      (leaf4003Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4003RoundedFacts : LeafRoundedFacts 8
    leaf4003Certificate.logOnePlusV leaf4003InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4003InputLogOnePlusV_eq }

private noncomputable def leaf4003Inputs : Inputs :=
  inputsOfCaches globalInput sk115RoundedInputs
    chi241InputQChi innerPair66Input
    leaf4003InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4003LowerChecked :
    lowerCheck 24 leaf4003Box leaf4003Inputs = true := by
  rfl'

private theorem leaf4003CoversExact : CoversExact 8
    leaf4003Box leaf4003Certificate leaf4003InnerLog leaf4003Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk115RoundedFacts chi241RoundedFacts
    innerPair66RoundedFacts leaf4003RoundedFacts (by rfl)

private theorem leaf4003FlatSound : Sound leaf4003Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4003CertificateValid
    leaf4003InnerLogValid leaf4003CoversExact leaf4003LowerChecked

private noncomputable def leaf4004Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (189/64), kHi := (95/32), chiLo := (1/4), chiHi := (33/128) }

private noncomputable def leaf4004Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871357/536870912) }, vSqrt := { lower := (32765/32768), upper := (137436921855/137432532992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (933175237/536870912) }, upper := { exponent := 0, mantissa := (7231/4096) } }, logOuter := sk116LogOuterCertificate, logK := sk116LogKCertificate, logChi := chi241LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (274869454847/274865065984) } }, logDArg := sk116LogDArgCertificate }

private noncomputable def leaf4004InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf4004LocalValidity :
    LeafFacts leaf4004Box leaf4004Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4004Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (137436921855/137432532992) }) = true
      norm_num [leaf4004Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4004CertificateValid :
    WideCertificateValid leaf4004Box leaf4004Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk116ValidityFacts chi241ValidityFacts
    leaf4004LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4004CoverageChecked :
    coverageCheck (innerAD leaf4004Box) leaf4004InnerLog = true := by
  rfl'

private theorem leaf4004InnerLogValid :
    leaf4004InnerLog.Valid 8 (innerAD leaf4004Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf4004CoverageChecked

private noncomputable def leaf4004InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629349/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4004InputLogOnePlusV_eq :
    leaf4004InputLogOnePlusV = outerEnclosure 24
      (leaf4004Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4004RoundedFacts : LeafRoundedFacts 8
    leaf4004Certificate.logOnePlusV leaf4004InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4004InputLogOnePlusV_eq }

private noncomputable def leaf4004Inputs : Inputs :=
  inputsOfCaches globalInput sk116RoundedInputs
    chi241InputQChi innerPair66Input
    leaf4004InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4004LowerChecked :
    lowerCheck 24 leaf4004Box leaf4004Inputs = true := by
  rfl'

private theorem leaf4004CoversExact : CoversExact 8
    leaf4004Box leaf4004Certificate leaf4004InnerLog leaf4004Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk116RoundedFacts chi241RoundedFacts
    innerPair66RoundedFacts leaf4004RoundedFacts (by rfl)

private theorem leaf4004FlatSound : Sound leaf4004Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4004CertificateValid
    leaf4004InnerLogValid leaf4004CoversExact leaf4004LowerChecked

private noncomputable def leaf4005Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (189/64), chiLo := (33/128), chiHi := (17/64) }

private noncomputable def leaf4005Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871357/536870912) }, vSqrt := { lower := (32765/32768), upper := (137436921855/137432373248) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (943398229/536870912) }, upper := { exponent := 0, mantissa := (7309/4096) } }, logOuter := sk115LogOuterCertificate, logK := sk115LogKCertificate, logChi := chi242LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (274869295103/274864746496) } }, logDArg := sk115LogDArgCertificate }

private noncomputable def leaf4005InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf4005LocalValidity :
    LeafFacts leaf4005Box leaf4005Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4005Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (137436921855/137432373248) }) = true
      norm_num [leaf4005Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4005CertificateValid :
    WideCertificateValid leaf4005Box leaf4005Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk115ValidityFacts chi242ValidityFacts
    leaf4005LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4005CoverageChecked :
    coverageCheck (innerAD leaf4005Box) leaf4005InnerLog = true := by
  rfl'

private theorem leaf4005InnerLogValid :
    leaf4005InnerLog.Valid 8 (innerAD leaf4005Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf4005CoverageChecked

private noncomputable def leaf4005InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814679/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4005InputLogOnePlusV_eq :
    leaf4005InputLogOnePlusV = outerEnclosure 24
      (leaf4005Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4005RoundedFacts : LeafRoundedFacts 8
    leaf4005Certificate.logOnePlusV leaf4005InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4005InputLogOnePlusV_eq }

private noncomputable def leaf4005Inputs : Inputs :=
  inputsOfCaches globalInput sk115RoundedInputs
    chi242InputQChi innerPair71Input
    leaf4005InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4005LowerChecked :
    lowerCheck 24 leaf4005Box leaf4005Inputs = true := by
  rfl'

private theorem leaf4005CoversExact : CoversExact 8
    leaf4005Box leaf4005Certificate leaf4005InnerLog leaf4005Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk115RoundedFacts chi242RoundedFacts
    innerPair71RoundedFacts leaf4005RoundedFacts (by rfl)

private theorem leaf4005FlatSound : Sound leaf4005Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4005CertificateValid
    leaf4005InnerLogValid leaf4005CoversExact leaf4005LowerChecked

private noncomputable def leaf4006Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (189/64), kHi := (95/32), chiLo := (33/128), chiHi := (17/64) }

private noncomputable def leaf4006Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871359/536870912) }, vSqrt := { lower := (32765/32768), upper := (137436921855/137432338432) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (945560783/536870912) }, upper := { exponent := 0, mantissa := (3663/2048) } }, logOuter := sk116LogOuterCertificate, logK := sk116LogKCertificate, logChi := chi242LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (274869260287/274864676864) } }, logDArg := sk116LogDArgCertificate }

private noncomputable def leaf4006InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf4006LocalValidity :
    LeafFacts leaf4006Box leaf4006Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4006Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (137436921855/137432338432) }) = true
      norm_num [leaf4006Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4006CertificateValid :
    WideCertificateValid leaf4006Box leaf4006Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk116ValidityFacts chi242ValidityFacts
    leaf4006LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4006CoverageChecked :
    coverageCheck (innerAD leaf4006Box) leaf4006InnerLog = true := by
  rfl'

private theorem leaf4006InnerLogValid :
    leaf4006InnerLog.Valid 8 (innerAD leaf4006Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf4006CoverageChecked

private noncomputable def leaf4006InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629361/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4006InputLogOnePlusV_eq :
    leaf4006InputLogOnePlusV = outerEnclosure 24
      (leaf4006Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4006RoundedFacts : LeafRoundedFacts 8
    leaf4006Certificate.logOnePlusV leaf4006InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4006InputLogOnePlusV_eq }

private noncomputable def leaf4006Inputs : Inputs :=
  inputsOfCaches globalInput sk116RoundedInputs
    chi242InputQChi innerPair71Input
    leaf4006InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4006LowerChecked :
    lowerCheck 24 leaf4006Box leaf4006Inputs = true := by
  rfl'

private theorem leaf4006CoversExact : CoversExact 8
    leaf4006Box leaf4006Certificate leaf4006InnerLog leaf4006Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk116RoundedFacts chi242RoundedFacts
    innerPair71RoundedFacts leaf4006RoundedFacts (by rfl)

private theorem leaf4006FlatSound : Sound leaf4006Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4006CertificateValid
    leaf4006InnerLogValid leaf4006CoversExact leaf4006LowerChecked

private noncomputable def leaf4007Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (191/64), chiLo := (1/4), chiHi := (33/128) }

private noncomputable def leaf4007Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871359/536870912) }, vSqrt := { lower := (32765/32768), upper := (27487384371/27486499840) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (935272259/536870912) }, upper := { exponent := 0, mantissa := (14495/8192) } }, logOuter := sk117LogOuterCertificate, logK := sk117LogKCertificate, logChi := chi241LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (54973884211/54972999680) } }, logDArg := sk117LogDArgCertificate }

private noncomputable def leaf4007InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf4007LocalValidity :
    LeafFacts leaf4007Box leaf4007Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4007Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (27487384371/27486499840) }) = true
      norm_num [leaf4007Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4007CertificateValid :
    WideCertificateValid leaf4007Box leaf4007Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk117ValidityFacts chi241ValidityFacts
    leaf4007LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4007CoverageChecked :
    coverageCheck (innerAD leaf4007Box) leaf4007InnerLog = true := by
  rfl'

private theorem leaf4007InnerLogValid :
    leaf4007InnerLog.Valid 8 (innerAD leaf4007Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf4007CoverageChecked

private noncomputable def leaf4007InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629351/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4007InputLogOnePlusV_eq :
    leaf4007InputLogOnePlusV = outerEnclosure 24
      (leaf4007Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4007RoundedFacts : LeafRoundedFacts 8
    leaf4007Certificate.logOnePlusV leaf4007InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4007InputLogOnePlusV_eq }

private noncomputable def leaf4007Inputs : Inputs :=
  inputsOfCaches globalInput sk117RoundedInputs
    chi241InputQChi innerPair66Input
    leaf4007InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4007LowerChecked :
    lowerCheck 24 leaf4007Box leaf4007Inputs = true := by
  rfl'

private theorem leaf4007CoversExact : CoversExact 8
    leaf4007Box leaf4007Certificate leaf4007InnerLog leaf4007Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk117RoundedFacts chi241RoundedFacts
    innerPair66RoundedFacts leaf4007RoundedFacts (by rfl)

private theorem leaf4007FlatSound : Sound leaf4007Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4007CertificateValid
    leaf4007InnerLogValid leaf4007CoversExact leaf4007LowerChecked

private noncomputable def leaf4008Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (191/64), kHi := (3), chiLo := (1/4), chiHi := (33/128) }

private noncomputable def leaf4008Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871361/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432465408) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (937369281/536870912) }, upper := { exponent := 0, mantissa := (227/128) } }, logOuter := sk118LogOuterCertificate, logK := sk118LogKCertificate, logChi := chi241LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869387263/274864930816) } }, logDArg := sk118LogDArgCertificate }

private noncomputable def leaf4008InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf4008LocalValidity :
    LeafFacts leaf4008Box leaf4008Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4008Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432465408) }) = true
      norm_num [leaf4008Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4008CertificateValid :
    WideCertificateValid leaf4008Box leaf4008Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk118ValidityFacts chi241ValidityFacts
    leaf4008LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4008CoverageChecked :
    coverageCheck (innerAD leaf4008Box) leaf4008InnerLog = true := by
  rfl'

private theorem leaf4008InnerLogValid :
    leaf4008InnerLog.Valid 8 (innerAD leaf4008Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf4008CoverageChecked

private noncomputable def leaf4008InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629353/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4008InputLogOnePlusV_eq :
    leaf4008InputLogOnePlusV = outerEnclosure 24
      (leaf4008Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4008RoundedFacts : LeafRoundedFacts 8
    leaf4008Certificate.logOnePlusV leaf4008InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4008InputLogOnePlusV_eq }

private noncomputable def leaf4008Inputs : Inputs :=
  inputsOfCaches globalInput sk118RoundedInputs
    chi241InputQChi innerPair66Input
    leaf4008InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4008LowerChecked :
    lowerCheck 24 leaf4008Box leaf4008Inputs = true := by
  rfl'

private theorem leaf4008CoversExact : CoversExact 8
    leaf4008Box leaf4008Certificate leaf4008InnerLog leaf4008Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk118RoundedFacts chi241RoundedFacts
    innerPair66RoundedFacts leaf4008RoundedFacts (by rfl)

private theorem leaf4008FlatSound : Sound leaf4008Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4008CertificateValid
    leaf4008InnerLogValid leaf4008CoversExact leaf4008LowerChecked

private noncomputable def leaf4009Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (191/64), chiLo := (33/128), chiHi := (17/64) }

private noncomputable def leaf4009Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871361/536870912) }, vSqrt := { lower := (32765/32768), upper := (45812307285/45810767872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (947723337/536870912) }, upper := { exponent := 0, mantissa := (7343/4096) } }, logOuter := sk117LogOuterCertificate, logK := sk117LogKCertificate, logChi := chi242LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (91623075157/91621535744) } }, logDArg := sk117LogDArgCertificate }

private noncomputable def leaf4009InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf4009LocalValidity :
    LeafFacts leaf4009Box leaf4009Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4009Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (45812307285/45810767872) }) = true
      norm_num [leaf4009Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4009CertificateValid :
    WideCertificateValid leaf4009Box leaf4009Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk117ValidityFacts chi242ValidityFacts
    leaf4009LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4009CoverageChecked :
    coverageCheck (innerAD leaf4009Box) leaf4009InnerLog = true := by
  rfl'

private theorem leaf4009InnerLogValid :
    leaf4009InnerLog.Valid 8 (innerAD leaf4009Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf4009CoverageChecked

private noncomputable def leaf4009InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629363/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4009InputLogOnePlusV_eq :
    leaf4009InputLogOnePlusV = outerEnclosure 24
      (leaf4009Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4009RoundedFacts : LeafRoundedFacts 8
    leaf4009Certificate.logOnePlusV leaf4009InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4009InputLogOnePlusV_eq }

private noncomputable def leaf4009Inputs : Inputs :=
  inputsOfCaches globalInput sk117RoundedInputs
    chi242InputQChi innerPair71Input
    leaf4009InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4009LowerChecked :
    lowerCheck 24 leaf4009Box leaf4009Inputs = true := by
  rfl'

private theorem leaf4009CoversExact : CoversExact 8
    leaf4009Box leaf4009Certificate leaf4009InnerLog leaf4009Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk117RoundedFacts chi242RoundedFacts
    innerPair71RoundedFacts leaf4009RoundedFacts (by rfl)

private theorem leaf4009FlatSound : Sound leaf4009Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4009CertificateValid
    leaf4009InnerLogValid leaf4009CoversExact leaf4009LowerChecked

private noncomputable def leaf4010Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (191/64), kHi := (3), chiLo := (33/128), chiHi := (17/64) }

private noncomputable def leaf4010Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871363/536870912) }, vSqrt := { lower := (65529/65536), upper := (27487384371/27486453760) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (949885891/536870912) }, upper := { exponent := 0, mantissa := (115/64) } }, logOuter := sk118LogOuterCertificate, logK := sk118LogKCertificate, logChi := chi242LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (54973838131/54972907520) } }, logDArg := sk118LogDArgCertificate }

private noncomputable def leaf4010InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf4010LocalValidity :
    LeafFacts leaf4010Box leaf4010Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4010Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (27487384371/27486453760) }) = true
      norm_num [leaf4010Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4010CertificateValid :
    WideCertificateValid leaf4010Box leaf4010Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk118ValidityFacts chi242ValidityFacts
    leaf4010LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4010CoverageChecked :
    coverageCheck (innerAD leaf4010Box) leaf4010InnerLog = true := by
  rfl'

private theorem leaf4010InnerLogValid :
    leaf4010InnerLog.Valid 8 (innerAD leaf4010Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf4010CoverageChecked

private noncomputable def leaf4010InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629365/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4010InputLogOnePlusV_eq :
    leaf4010InputLogOnePlusV = outerEnclosure 24
      (leaf4010Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4010RoundedFacts : LeafRoundedFacts 8
    leaf4010Certificate.logOnePlusV leaf4010InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4010InputLogOnePlusV_eq }

private noncomputable def leaf4010Inputs : Inputs :=
  inputsOfCaches globalInput sk118RoundedInputs
    chi242InputQChi innerPair71Input
    leaf4010InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4010LowerChecked :
    lowerCheck 24 leaf4010Box leaf4010Inputs = true := by
  rfl'

private theorem leaf4010CoversExact : CoversExact 8
    leaf4010Box leaf4010Certificate leaf4010InnerLog leaf4010Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk118RoundedFacts chi242RoundedFacts
    innerPair71RoundedFacts leaf4010RoundedFacts (by rfl)

private theorem leaf4010FlatSound : Sound leaf4010Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4010CertificateValid
    leaf4010InnerLogValid leaf4010CoversExact leaf4010LowerChecked

private noncomputable def leaf4011Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (95/32), chiLo := (17/64), chiHi := (35/128) }

private noncomputable def leaf4011Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435715/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905357312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (477842703/268435456) }, upper := { exponent := 0, mantissa := (7421/4096) } }, logOuter := sk113LogOuterCertificate, logK := sk113LogKCertificate, logChi := chi243LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811521877/45810714624) } }, logDArg := sk113LogDArgCertificate }

private noncomputable def leaf4011InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf4011LocalValidity :
    LeafFacts leaf4011Box leaf4011Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4011Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905357312) }) = true
      norm_num [leaf4011Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4011CertificateValid :
    WideCertificateValid leaf4011Box leaf4011Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk113ValidityFacts chi243ValidityFacts
    leaf4011LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4011CoverageChecked :
    coverageCheck (innerAD leaf4011Box) leaf4011InnerLog = true := by
  rfl'

private theorem leaf4011InnerLogValid :
    leaf4011InnerLog.Valid 8 (innerAD leaf4011Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf4011CoverageChecked

private noncomputable def leaf4011InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (181709/262144) }

set_option maxRecDepth 1000000 in
private theorem leaf4011InputLogOnePlusV_eq :
    leaf4011InputLogOnePlusV = outerEnclosure 24
      (leaf4011Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4011RoundedFacts : LeafRoundedFacts 8
    leaf4011Certificate.logOnePlusV leaf4011InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4011InputLogOnePlusV_eq }

private noncomputable def leaf4011Inputs : Inputs :=
  inputsOfCaches globalInput sk113RoundedInputs
    chi243InputQChi innerPair71Input
    leaf4011InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4011LowerChecked :
    lowerCheck 24 leaf4011Box leaf4011Inputs = true := by
  rfl'

private theorem leaf4011CoversExact : CoversExact 8
    leaf4011Box leaf4011Certificate leaf4011InnerLog leaf4011Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk113RoundedFacts chi243RoundedFacts
    innerPair71RoundedFacts leaf4011RoundedFacts (by rfl)

private theorem leaf4011FlatSound : Sound leaf4011Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4011CertificateValid
    leaf4011InnerLogValid leaf4011CoversExact leaf4011LowerChecked

private noncomputable def leaf4012Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (17/64), chiHi := (69/256) }

private noncomputable def leaf4012Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871241/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68716085248) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (960174537/536870912) }, upper := { exponent := 0, mantissa := (463/256) } }, logOuter := sk114LogOuterCertificate, logK := sk114LogKCertificate, logChi := chi257LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434578943/137432170496) } }, logDArg := sk114LogDArgCertificate }

private noncomputable def leaf4012InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf4012LocalValidity :
    LeafFacts leaf4012Box leaf4012Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4012Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68716085248) }) = true
      norm_num [leaf4012Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4012CertificateValid :
    WideCertificateValid leaf4012Box leaf4012Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk114ValidityFacts chi257ValidityFacts
    leaf4012LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4012CoverageChecked :
    coverageCheck (innerAD leaf4012Box) leaf4012InnerLog = true := by
  rfl'

private theorem leaf4012InnerLogValid :
    leaf4012InnerLog.Valid 8 (innerAD leaf4012Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf4012CoverageChecked

private noncomputable def leaf4012InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629375/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4012InputLogOnePlusV_eq :
    leaf4012InputLogOnePlusV = outerEnclosure 24
      (leaf4012Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4012RoundedFacts : LeafRoundedFacts 8
    leaf4012Certificate.logOnePlusV leaf4012InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4012InputLogOnePlusV_eq }

private noncomputable def leaf4012Inputs : Inputs :=
  inputsOfCaches globalInput sk114RoundedInputs
    chi257InputQChi innerPair71Input
    leaf4012InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4012LowerChecked :
    lowerCheck 24 leaf4012Box leaf4012Inputs = true := by
  rfl'

private theorem leaf4012CoversExact : CoversExact 8
    leaf4012Box leaf4012Certificate leaf4012InnerLog leaf4012Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk114RoundedFacts chi257RoundedFacts
    innerPair71RoundedFacts leaf4012RoundedFacts (by rfl)

private theorem leaf4012FlatSound : Sound leaf4012Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4012CertificateValid
    leaf4012InnerLogValid leaf4012CoversExact leaf4012LowerChecked

private noncomputable def leaf4013Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (69/256), chiHi := (35/128) }

private noncomputable def leaf4013Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871243/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68716036096) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (966400075/536870912) }, upper := { exponent := 0, mantissa := (233/128) } }, logOuter := sk114LogOuterCertificate, logK := sk114LogKCertificate, logChi := chi258LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434529791/137432072192) } }, logDArg := sk114LogDArgCertificate }

private noncomputable def leaf4013InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf4013LocalValidity :
    LeafFacts leaf4013Box leaf4013Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4013Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68716036096) }) = true
      norm_num [leaf4013Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4013CertificateValid :
    WideCertificateValid leaf4013Box leaf4013Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk114ValidityFacts chi258ValidityFacts
    leaf4013LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4013CoverageChecked :
    coverageCheck (innerAD leaf4013Box) leaf4013InnerLog = true := by
  rfl'

private theorem leaf4013InnerLogValid :
    leaf4013InnerLog.Valid 8 (innerAD leaf4013Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf4013CoverageChecked

private noncomputable def leaf4013InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629381/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4013InputLogOnePlusV_eq :
    leaf4013InputLogOnePlusV = outerEnclosure 24
      (leaf4013Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4013RoundedFacts : LeafRoundedFacts 8
    leaf4013Certificate.logOnePlusV leaf4013InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4013InputLogOnePlusV_eq }

private noncomputable def leaf4013Inputs : Inputs :=
  inputsOfCaches globalInput sk114RoundedInputs
    chi258InputQChi innerPair72Input
    leaf4013InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4013LowerChecked :
    lowerCheck 24 leaf4013Box leaf4013Inputs = true := by
  rfl'

private theorem leaf4013CoversExact : CoversExact 8
    leaf4013Box leaf4013Certificate leaf4013InnerLog leaf4013Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk114RoundedFacts chi258RoundedFacts
    innerPair72RoundedFacts leaf4013RoundedFacts (by rfl)

private theorem leaf4013FlatSound : Sound leaf4013Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4013CertificateValid
    leaf4013InnerLogValid leaf4013CoversExact leaf4013LowerChecked

private noncomputable def leaf4014Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (95/32), chiLo := (35/128), chiHi := (9/32) }

private noncomputable def leaf4014Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435717/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715974656) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (484002709/268435456) }, upper := { exponent := 0, mantissa := (1879/1024) } }, logOuter := sk113LogOuterCertificate, logK := sk113LogKCertificate, logChi := chi244LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434468351/137431949312) } }, logDArg := sk113LogDArgCertificate }

private noncomputable def leaf4014InnerLog : WideLogData :=
  innerPair469Data

set_option maxRecDepth 1000000 in
private theorem leaf4014LocalValidity :
    LeafFacts leaf4014Box leaf4014Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4014Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715974656) }) = true
      norm_num [leaf4014Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4014CertificateValid :
    WideCertificateValid leaf4014Box leaf4014Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk113ValidityFacts chi244ValidityFacts
    leaf4014LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4014CoverageChecked :
    coverageCheck (innerAD leaf4014Box) leaf4014InnerLog = true := by
  rfl'

private theorem leaf4014InnerLogValid :
    leaf4014InnerLog.Valid 8 (innerAD leaf4014Box) :=
  wideLogDataValid_of_cachedCheck endpoint187PositiveFacts
    endpoint189PositiveFacts.valid leaf4014CoverageChecked

private noncomputable def leaf4014InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907347/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4014InputLogOnePlusV_eq :
    leaf4014InputLogOnePlusV = outerEnclosure 24
      (leaf4014Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4014RoundedFacts : LeafRoundedFacts 8
    leaf4014Certificate.logOnePlusV leaf4014InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4014InputLogOnePlusV_eq }

private noncomputable def leaf4014Inputs : Inputs :=
  inputsOfCaches globalInput sk113RoundedInputs
    chi244InputQChi innerPair469Input
    leaf4014InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4014LowerChecked :
    lowerCheck 24 leaf4014Box leaf4014Inputs = true := by
  rfl'

private theorem leaf4014CoversExact : CoversExact 8
    leaf4014Box leaf4014Certificate leaf4014InnerLog leaf4014Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk113RoundedFacts chi244RoundedFacts
    innerPair469RoundedFacts leaf4014RoundedFacts (by rfl)

private theorem leaf4014FlatSound : Sound leaf4014Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4014CertificateValid
    leaf4014InnerLogValid leaf4014CoversExact leaf4014LowerChecked

private noncomputable def leaf4015Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (35/128), chiHi := (9/32) }

private noncomputable def leaf4015Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435719/268435456) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715937792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (486296327/268435456) }, upper := { exponent := 0, mantissa := (59/32) } }, logOuter := sk114LogOuterCertificate, logK := sk114LogKCertificate, logChi := chi244LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434431487/137431875584) } }, logDArg := sk114LogDArgCertificate }

private noncomputable def leaf4015InnerLog : WideLogData :=
  innerPair220Data

set_option maxRecDepth 1000000 in
private theorem leaf4015LocalValidity :
    LeafFacts leaf4015Box leaf4015Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4015Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715937792) }) = true
      norm_num [leaf4015Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4015CertificateValid :
    WideCertificateValid leaf4015Box leaf4015Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk114ValidityFacts chi244ValidityFacts
    leaf4015LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4015CoverageChecked :
    coverageCheck (innerAD leaf4015Box) leaf4015InnerLog = true := by
  rfl'

private theorem leaf4015InnerLogValid :
    leaf4015InnerLog.Valid 8 (innerAD leaf4015Box) :=
  wideLogDataValid_of_cachedCheck endpoint67PositiveFacts
    endpoint61PositiveFacts.valid leaf4015CoverageChecked

private noncomputable def leaf4015InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629393/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4015InputLogOnePlusV_eq :
    leaf4015InputLogOnePlusV = outerEnclosure 24
      (leaf4015Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4015RoundedFacts : LeafRoundedFacts 8
    leaf4015Certificate.logOnePlusV leaf4015InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4015InputLogOnePlusV_eq }

private noncomputable def leaf4015Inputs : Inputs :=
  inputsOfCaches globalInput sk114RoundedInputs
    chi244InputQChi innerPair220Input
    leaf4015InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4015LowerChecked :
    lowerCheck 24 leaf4015Box leaf4015Inputs = true := by
  rfl'

private theorem leaf4015CoversExact : CoversExact 8
    leaf4015Box leaf4015Certificate leaf4015InnerLog leaf4015Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk114RoundedFacts chi244RoundedFacts
    innerPair220RoundedFacts leaf4015RoundedFacts (by rfl)

private theorem leaf4015FlatSound : Sound leaf4015Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4015CertificateValid
    leaf4015InnerLogValid leaf4015CoversExact leaf4015LowerChecked

private noncomputable def leaf4016Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32), chiLo := (9/32), chiHi := (37/128) }

private noncomputable def leaf4016Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435715/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715953152) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (485444415/268435456) }, upper := { exponent := 0, mantissa := (7537/4096) } }, logOuter := sk111LogOuterCertificate, logK := sk111LogKCertificate, logChi := chi245LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434446847/137431906304) } }, logDArg := sk111LogDArgCertificate }

private noncomputable def leaf4016InnerLog : WideLogData :=
  innerPair220Data

set_option maxRecDepth 1000000 in
private theorem leaf4016LocalValidity :
    LeafFacts leaf4016Box leaf4016Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4016Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715953152) }) = true
      norm_num [leaf4016Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4016CertificateValid :
    WideCertificateValid leaf4016Box leaf4016Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk111ValidityFacts chi245ValidityFacts
    leaf4016LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4016CoverageChecked :
    coverageCheck (innerAD leaf4016Box) leaf4016InnerLog = true := by
  rfl'

private theorem leaf4016InnerLogValid :
    leaf4016InnerLog.Valid 8 (innerAD leaf4016Box) :=
  wideLogDataValid_of_cachedCheck endpoint67PositiveFacts
    endpoint61PositiveFacts.valid leaf4016CoverageChecked

private noncomputable def leaf4016InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629391/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4016InputLogOnePlusV_eq :
    leaf4016InputLogOnePlusV = outerEnclosure 24
      (leaf4016Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4016RoundedFacts : LeafRoundedFacts 8
    leaf4016Certificate.logOnePlusV leaf4016InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4016InputLogOnePlusV_eq }

private noncomputable def leaf4016Inputs : Inputs :=
  inputsOfCaches globalInput sk111RoundedInputs
    chi245InputQChi innerPair220Input
    leaf4016InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4016LowerChecked :
    lowerCheck 24 leaf4016Box leaf4016Inputs = true := by
  rfl'

private theorem leaf4016CoversExact : CoversExact 8
    leaf4016Box leaf4016Certificate leaf4016InnerLog leaf4016Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk111RoundedFacts chi245RoundedFacts
    innerPair220RoundedFacts leaf4016RoundedFacts (by rfl)

private theorem leaf4016FlatSound : Sound leaf4016Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4016CertificateValid
    leaf4016InnerLogValid leaf4016CoversExact leaf4016LowerChecked

private noncomputable def leaf4017Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32), chiLo := (37/128), chiHi := (19/64) }

private noncomputable def leaf4017Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435717/268435456) }, vSqrt := { lower := (32765/32768), upper := (13743698739/13743171584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (491473357/268435456) }, upper := { exponent := 0, mantissa := (3815/2048) } }, logOuter := sk111LogOuterCertificate, logK := sk111LogKCertificate, logChi := chi246LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (27486870323/27486343168) } }, logDArg := sk111LogDArgCertificate }

private noncomputable def leaf4017InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf4017LocalValidity :
    LeafFacts leaf4017Box leaf4017Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4017Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (13743698739/13743171584) }) = true
      norm_num [leaf4017Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4017CertificateValid :
    WideCertificateValid leaf4017Box leaf4017Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk111ValidityFacts chi246ValidityFacts
    leaf4017LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4017CoverageChecked :
    coverageCheck (innerAD leaf4017Box) leaf4017InnerLog = true := by
  rfl'

private theorem leaf4017InnerLogValid :
    leaf4017InnerLog.Valid 8 (innerAD leaf4017Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf4017CoverageChecked

private noncomputable def leaf4017InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629403/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4017InputLogOnePlusV_eq :
    leaf4017InputLogOnePlusV = outerEnclosure 24
      (leaf4017Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4017RoundedFacts : LeafRoundedFacts 8
    leaf4017Certificate.logOnePlusV leaf4017InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4017InputLogOnePlusV_eq }

private noncomputable def leaf4017Inputs : Inputs :=
  inputsOfCaches globalInput sk111RoundedInputs
    chi246InputQChi innerPair91Input
    leaf4017InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4017LowerChecked :
    lowerCheck 24 leaf4017Box leaf4017Inputs = true := by
  rfl'

private theorem leaf4017CoversExact : CoversExact 8
    leaf4017Box leaf4017Certificate leaf4017InnerLog leaf4017Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk111RoundedFacts chi246RoundedFacts
    innerPair91RoundedFacts leaf4017RoundedFacts (by rfl)

private theorem leaf4017FlatSound : Sound leaf4017Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4017CertificateValid
    leaf4017InnerLogValid leaf4017CoversExact leaf4017LowerChecked

private noncomputable def leaf4018Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16), chiLo := (9/32), chiHi := (37/128) }

private noncomputable def leaf4018Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435717/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905305088) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (487803565/268435456) }, upper := { exponent := 0, mantissa := (3787/2048) } }, logOuter := sk112LogOuterCertificate, logK := sk112LogKCertificate, logChi := chi245LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811469653/45810610176) } }, logDArg := sk112LogDArgCertificate }

private noncomputable def leaf4018InnerLog : WideLogData :=
  innerPair99Data

set_option maxRecDepth 1000000 in
private theorem leaf4018LocalValidity :
    LeafFacts leaf4018Box leaf4018Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4018Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905305088) }) = true
      norm_num [leaf4018Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4018CertificateValid :
    WideCertificateValid leaf4018Box leaf4018Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk112ValidityFacts chi245ValidityFacts
    leaf4018LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4018CoverageChecked :
    coverageCheck (innerAD leaf4018Box) leaf4018InnerLog = true := by
  rfl'

private theorem leaf4018InnerLogValid :
    leaf4018InnerLog.Valid 8 (innerAD leaf4018Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint211PositiveFacts.valid leaf4018CoverageChecked

private noncomputable def leaf4018InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907349/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4018InputLogOnePlusV_eq :
    leaf4018InputLogOnePlusV = outerEnclosure 24
      (leaf4018Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4018RoundedFacts : LeafRoundedFacts 8
    leaf4018Certificate.logOnePlusV leaf4018InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4018InputLogOnePlusV_eq }

private noncomputable def leaf4018Inputs : Inputs :=
  inputsOfCaches globalInput sk112RoundedInputs
    chi245InputQChi innerPair99Input
    leaf4018InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4018LowerChecked :
    lowerCheck 24 leaf4018Box leaf4018Inputs = true := by
  rfl'

private theorem leaf4018CoversExact : CoversExact 8
    leaf4018Box leaf4018Certificate leaf4018InnerLog leaf4018Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk112RoundedFacts chi245RoundedFacts
    innerPair99RoundedFacts leaf4018RoundedFacts (by rfl)

private theorem leaf4018FlatSound : Sound leaf4018Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4018CertificateValid
    leaf4018InnerLogValid leaf4018CoversExact leaf4018LowerChecked

private noncomputable def leaf4019Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16), chiLo := (37/128), chiHi := (19/64) }

private noncomputable def leaf4019Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435719/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715819008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (493898039/268435456) }, upper := { exponent := 0, mantissa := (1917/1024) } }, logOuter := sk112LogOuterCertificate, logK := sk112LogKCertificate, logChi := chi246LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434312703/137431638016) } }, logDArg := sk112LogDArgCertificate }

private noncomputable def leaf4019InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf4019LocalValidity :
    LeafFacts leaf4019Box leaf4019Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4019Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715819008) }) = true
      norm_num [leaf4019Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4019CertificateValid :
    WideCertificateValid leaf4019Box leaf4019Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk112ValidityFacts chi246ValidityFacts
    leaf4019LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4019CoverageChecked :
    coverageCheck (innerAD leaf4019Box) leaf4019InnerLog = true := by
  rfl'

private theorem leaf4019InnerLogValid :
    leaf4019InnerLog.Valid 8 (innerAD leaf4019Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf4019CoverageChecked

private noncomputable def leaf4019InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629407/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4019InputLogOnePlusV_eq :
    leaf4019InputLogOnePlusV = outerEnclosure 24
      (leaf4019Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4019RoundedFacts : LeafRoundedFacts 8
    leaf4019Certificate.logOnePlusV leaf4019InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4019InputLogOnePlusV_eq }

private noncomputable def leaf4019Inputs : Inputs :=
  inputsOfCaches globalInput sk112RoundedInputs
    chi246InputQChi innerPair91Input
    leaf4019InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4019LowerChecked :
    lowerCheck 24 leaf4019Box leaf4019Inputs = true := by
  rfl'

private theorem leaf4019CoversExact : CoversExact 8
    leaf4019Box leaf4019Certificate leaf4019InnerLog leaf4019Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk112RoundedFacts chi246RoundedFacts
    innerPair91RoundedFacts leaf4019RoundedFacts (by rfl)

private theorem leaf4019FlatSound : Sound leaf4019Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4019CertificateValid
    leaf4019InnerLogValid leaf4019CoversExact leaf4019LowerChecked

private noncomputable def leaf4020Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32), chiLo := (19/64), chiHi := (39/128) }

private noncomputable def leaf4020Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435719/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715762688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (497502299/268435456) }, upper := { exponent := 0, mantissa := (7723/4096) } }, logOuter := sk111LogOuterCertificate, logK := sk111LogKCertificate, logChi := chi247LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434256383/137431525376) } }, logDArg := sk111LogDArgCertificate }

private noncomputable def leaf4020InnerLog : WideLogData :=
  innerPair199Data

set_option maxRecDepth 1000000 in
private theorem leaf4020LocalValidity :
    LeafFacts leaf4020Box leaf4020Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4020Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715762688) }) = true
      norm_num [leaf4020Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4020CertificateValid :
    WideCertificateValid leaf4020Box leaf4020Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk111ValidityFacts chi247ValidityFacts
    leaf4020LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4020CoverageChecked :
    coverageCheck (innerAD leaf4020Box) leaf4020InnerLog = true := by
  rfl'

private theorem leaf4020InnerLogValid :
    leaf4020InnerLog.Valid 8 (innerAD leaf4020Box) :=
  wideLogDataValid_of_cachedCheck endpoint61PositiveFacts
    endpoint69PositiveFacts.valid leaf4020CoverageChecked

private noncomputable def leaf4020InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814707/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4020InputLogOnePlusV_eq :
    leaf4020InputLogOnePlusV = outerEnclosure 24
      (leaf4020Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4020RoundedFacts : LeafRoundedFacts 8
    leaf4020Certificate.logOnePlusV leaf4020InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4020InputLogOnePlusV_eq }

private noncomputable def leaf4020Inputs : Inputs :=
  inputsOfCaches globalInput sk111RoundedInputs
    chi247InputQChi innerPair199Input
    leaf4020InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4020LowerChecked :
    lowerCheck 24 leaf4020Box leaf4020Inputs = true := by
  rfl'

private theorem leaf4020CoversExact : CoversExact 8
    leaf4020Box leaf4020Certificate leaf4020InnerLog leaf4020Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk111RoundedFacts chi247RoundedFacts
    innerPair199RoundedFacts leaf4020RoundedFacts (by rfl)

private theorem leaf4020FlatSound : Sound leaf4020Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4020CertificateValid
    leaf4020InnerLogValid leaf4020CoversExact leaf4020LowerChecked

private noncomputable def leaf4021Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16), chiLo := (19/64), chiHi := (39/128) }

private noncomputable def leaf4021Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435721/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715722752) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (499992513/268435456) }, upper := { exponent := 0, mantissa := (3881/2048) } }, logOuter := sk112LogOuterCertificate, logK := sk112LogKCertificate, logChi := chi247LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434216447/137431445504) } }, logDArg := sk112LogDArgCertificate }

private noncomputable def leaf4021InnerLog : WideLogData :=
  innerPair483Data

set_option maxRecDepth 1000000 in
private theorem leaf4021LocalValidity :
    LeafFacts leaf4021Box leaf4021Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4021Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715722752) }) = true
      norm_num [leaf4021Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4021CertificateValid :
    WideCertificateValid leaf4021Box leaf4021Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk112ValidityFacts chi247ValidityFacts
    leaf4021LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4021CoverageChecked :
    coverageCheck (innerAD leaf4021Box) leaf4021InnerLog = true := by
  rfl'

private theorem leaf4021InnerLogValid :
    leaf4021InnerLog.Valid 8 (innerAD leaf4021Box) :=
  wideLogDataValid_of_cachedCheck endpoint211PositiveFacts
    endpoint70PositiveFacts.valid leaf4021CoverageChecked

private noncomputable def leaf4021InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629419/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4021InputLogOnePlusV_eq :
    leaf4021InputLogOnePlusV = outerEnclosure 24
      (leaf4021Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4021RoundedFacts : LeafRoundedFacts 8
    leaf4021Certificate.logOnePlusV leaf4021InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4021InputLogOnePlusV_eq }

private noncomputable def leaf4021Inputs : Inputs :=
  inputsOfCaches globalInput sk112RoundedInputs
    chi247InputQChi innerPair483Input
    leaf4021InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4021LowerChecked :
    lowerCheck 24 leaf4021Box leaf4021Inputs = true := by
  rfl'

private theorem leaf4021CoversExact : CoversExact 8
    leaf4021Box leaf4021Certificate leaf4021InnerLog leaf4021Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk112RoundedFacts chi247RoundedFacts
    innerPair483RoundedFacts leaf4021RoundedFacts (by rfl)

private theorem leaf4021FlatSound : Sound leaf4021Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4021CertificateValid
    leaf4021InnerLogValid leaf4021CoversExact leaf4021LowerChecked

private noncomputable def leaf4022Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32), chiLo := (39/128), chiHi := (5/16) }

private noncomputable def leaf4022Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435721/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715667456) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (503531241/268435456) }, upper := { exponent := 0, mantissa := (977/512) } }, logOuter := sk111LogOuterCertificate, logK := sk111LogKCertificate, logChi := chi248LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434161151/137431334912) } }, logDArg := sk111LogDArgCertificate }

private noncomputable def leaf4022InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4022LocalValidity :
    LeafFacts leaf4022Box leaf4022Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4022Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715667456) }) = true
      norm_num [leaf4022Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4022CertificateValid :
    WideCertificateValid leaf4022Box leaf4022Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk111ValidityFacts chi248ValidityFacts
    leaf4022LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4022CoverageChecked :
    coverageCheck (innerAD leaf4022Box) leaf4022InnerLog = true := by
  rfl'

private theorem leaf4022InnerLogValid :
    leaf4022InnerLog.Valid 8 (innerAD leaf4022Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4022CoverageChecked

private noncomputable def leaf4022InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814713/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4022InputLogOnePlusV_eq :
    leaf4022InputLogOnePlusV = outerEnclosure 24
      (leaf4022Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4022RoundedFacts : LeafRoundedFacts 8
    leaf4022Certificate.logOnePlusV leaf4022InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4022InputLogOnePlusV_eq }

private noncomputable def leaf4022Inputs : Inputs :=
  inputsOfCaches globalInput sk111RoundedInputs
    chi248InputQChi innerPair100Input
    leaf4022InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4022LowerChecked :
    lowerCheck 24 leaf4022Box leaf4022Inputs = true := by
  rfl'

private theorem leaf4022CoversExact : CoversExact 8
    leaf4022Box leaf4022Certificate leaf4022InnerLog leaf4022Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk111RoundedFacts chi248RoundedFacts
    innerPair100RoundedFacts leaf4022RoundedFacts (by rfl)

private theorem leaf4022FlatSound : Sound leaf4022Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4022CertificateValid
    leaf4022InnerLogValid leaf4022CoversExact leaf4022LowerChecked

private noncomputable def leaf4023Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16), chiLo := (39/128), chiHi := (5/16) }

private noncomputable def leaf4023Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435723/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905208832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (506086987/268435456) }, upper := { exponent := 0, mantissa := (491/256) } }, logOuter := sk112LogOuterCertificate, logK := sk112LogKCertificate, logChi := chi248LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811373397/45810417664) } }, logDArg := sk112LogDArgCertificate }

private noncomputable def leaf4023InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4023LocalValidity :
    LeafFacts leaf4023Box leaf4023Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4023Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905208832) }) = true
      norm_num [leaf4023Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4023CertificateValid :
    WideCertificateValid leaf4023Box leaf4023Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk112ValidityFacts chi248ValidityFacts
    leaf4023LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4023CoverageChecked :
    coverageCheck (innerAD leaf4023Box) leaf4023InnerLog = true := by
  rfl'

private theorem leaf4023InnerLogValid :
    leaf4023InnerLog.Valid 8 (innerAD leaf4023Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4023CoverageChecked

private noncomputable def leaf4023InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629431/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4023InputLogOnePlusV_eq :
    leaf4023InputLogOnePlusV = outerEnclosure 24
      (leaf4023Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4023RoundedFacts : LeafRoundedFacts 8
    leaf4023Certificate.logOnePlusV leaf4023InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4023InputLogOnePlusV_eq }

private noncomputable def leaf4023Inputs : Inputs :=
  inputsOfCaches globalInput sk112RoundedInputs
    chi248InputQChi innerPair100Input
    leaf4023InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4023LowerChecked :
    lowerCheck 24 leaf4023Box leaf4023Inputs = true := by
  rfl'

private theorem leaf4023CoversExact : CoversExact 8
    leaf4023Box leaf4023Certificate leaf4023InnerLog leaf4023Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk112RoundedFacts chi248RoundedFacts
    innerPair100RoundedFacts leaf4023RoundedFacts (by rfl)

private theorem leaf4023FlatSound : Sound leaf4023Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4023CertificateValid
    leaf4023InnerLogValid leaf4023CoversExact leaf4023LowerChecked

private noncomputable def leaf4024Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (95/32), chiLo := (9/32), chiHi := (37/128) }

private noncomputable def leaf4024Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435719/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715877376) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (490162715/268435456) }, upper := { exponent := 0, mantissa := (7611/4096) } }, logOuter := sk113LogOuterCertificate, logK := sk113LogKCertificate, logChi := chi245LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434371071/137431754752) } }, logDArg := sk113LogDArgCertificate }

private noncomputable def leaf4024InnerLog : WideLogData :=
  innerPair99Data

set_option maxRecDepth 1000000 in
private theorem leaf4024LocalValidity :
    LeafFacts leaf4024Box leaf4024Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4024Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715877376) }) = true
      norm_num [leaf4024Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4024CertificateValid :
    WideCertificateValid leaf4024Box leaf4024Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk113ValidityFacts chi245ValidityFacts
    leaf4024LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4024CoverageChecked :
    coverageCheck (innerAD leaf4024Box) leaf4024InnerLog = true := by
  rfl'

private theorem leaf4024InnerLogValid :
    leaf4024InnerLog.Valid 8 (innerAD leaf4024Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint211PositiveFacts.valid leaf4024CoverageChecked

private noncomputable def leaf4024InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453675/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf4024InputLogOnePlusV_eq :
    leaf4024InputLogOnePlusV = outerEnclosure 24
      (leaf4024Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4024RoundedFacts : LeafRoundedFacts 8
    leaf4024Certificate.logOnePlusV leaf4024InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4024InputLogOnePlusV_eq }

private noncomputable def leaf4024Inputs : Inputs :=
  inputsOfCaches globalInput sk113RoundedInputs
    chi245InputQChi innerPair99Input
    leaf4024InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4024LowerChecked :
    lowerCheck 24 leaf4024Box leaf4024Inputs = true := by
  rfl'

private theorem leaf4024CoversExact : CoversExact 8
    leaf4024Box leaf4024Certificate leaf4024InnerLog leaf4024Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk113RoundedFacts chi245RoundedFacts
    innerPair99RoundedFacts leaf4024RoundedFacts (by rfl)

private theorem leaf4024FlatSound : Sound leaf4024Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4024CertificateValid
    leaf4024InnerLogValid leaf4024CoversExact leaf4024LowerChecked

private noncomputable def leaf4025Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (9/32), chiHi := (37/128) }

private noncomputable def leaf4025Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435721/268435456) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715839488) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (492521865/268435456) }, upper := { exponent := 0, mantissa := (239/128) } }, logOuter := sk114LogOuterCertificate, logK := sk114LogKCertificate, logChi := chi245LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434333183/137431678976) } }, logDArg := sk114LogDArgCertificate }

private noncomputable def leaf4025InnerLog : WideLogData :=
  innerPair499Data

set_option maxRecDepth 1000000 in
private theorem leaf4025LocalValidity :
    LeafFacts leaf4025Box leaf4025Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4025Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715839488) }) = true
      norm_num [leaf4025Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4025CertificateValid :
    WideCertificateValid leaf4025Box leaf4025Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk114ValidityFacts chi245ValidityFacts
    leaf4025LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4025CoverageChecked :
    coverageCheck (innerAD leaf4025Box) leaf4025InnerLog = true := by
  rfl'

private theorem leaf4025InnerLogValid :
    leaf4025InnerLog.Valid 8 (innerAD leaf4025Box) :=
  wideLogDataValid_of_cachedCheck endpoint222PositiveFacts
    endpoint251PositiveFacts.valid leaf4025CoverageChecked

private noncomputable def leaf4025InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629405/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4025InputLogOnePlusV_eq :
    leaf4025InputLogOnePlusV = outerEnclosure 24
      (leaf4025Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4025RoundedFacts : LeafRoundedFacts 8
    leaf4025Certificate.logOnePlusV leaf4025InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4025InputLogOnePlusV_eq }

private noncomputable def leaf4025Inputs : Inputs :=
  inputsOfCaches globalInput sk114RoundedInputs
    chi245InputQChi innerPair499Input
    leaf4025InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4025LowerChecked :
    lowerCheck 24 leaf4025Box leaf4025Inputs = true := by
  rfl'

private theorem leaf4025CoversExact : CoversExact 8
    leaf4025Box leaf4025Certificate leaf4025InnerLog leaf4025Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk114RoundedFacts chi245RoundedFacts
    innerPair499RoundedFacts leaf4025RoundedFacts (by rfl)

private theorem leaf4025FlatSound : Sound leaf4025Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4025CertificateValid
    leaf4025InnerLogValid leaf4025CoversExact leaf4025LowerChecked

private noncomputable def leaf4026Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (95/32), chiLo := (37/128), chiHi := (19/64) }

private noncomputable def leaf4026Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435721/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905260032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (496322721/268435456) }, upper := { exponent := 0, mantissa := (3853/2048) } }, logOuter := sk113LogOuterCertificate, logK := sk113LogKCertificate, logChi := chi246LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811424597/45810520064) } }, logDArg := sk113LogDArgCertificate }

private noncomputable def leaf4026InnerLog : WideLogData :=
  innerPair199Data

set_option maxRecDepth 1000000 in
private theorem leaf4026LocalValidity :
    LeafFacts leaf4026Box leaf4026Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4026Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905260032) }) = true
      norm_num [leaf4026Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4026CertificateValid :
    WideCertificateValid leaf4026Box leaf4026Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk113ValidityFacts chi246ValidityFacts
    leaf4026LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4026CoverageChecked :
    coverageCheck (innerAD leaf4026Box) leaf4026InnerLog = true := by
  rfl'

private theorem leaf4026InnerLogValid :
    leaf4026InnerLog.Valid 8 (innerAD leaf4026Box) :=
  wideLogDataValid_of_cachedCheck endpoint61PositiveFacts
    endpoint69PositiveFacts.valid leaf4026CoverageChecked

private noncomputable def leaf4026InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907353/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4026InputLogOnePlusV_eq :
    leaf4026InputLogOnePlusV = outerEnclosure 24
      (leaf4026Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4026RoundedFacts : LeafRoundedFacts 8
    leaf4026Certificate.logOnePlusV leaf4026InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4026InputLogOnePlusV_eq }

private noncomputable def leaf4026Inputs : Inputs :=
  inputsOfCaches globalInput sk113RoundedInputs
    chi246InputQChi innerPair199Input
    leaf4026InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4026LowerChecked :
    lowerCheck 24 leaf4026Box leaf4026Inputs = true := by
  rfl'

private theorem leaf4026CoversExact : CoversExact 8
    leaf4026Box leaf4026Certificate leaf4026InnerLog leaf4026Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk113RoundedFacts chi246RoundedFacts
    innerPair199RoundedFacts leaf4026RoundedFacts (by rfl)

private theorem leaf4026FlatSound : Sound leaf4026Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4026CertificateValid
    leaf4026InnerLogValid leaf4026CoversExact leaf4026LowerChecked

private noncomputable def leaf4027Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (37/128), chiHi := (19/64) }

private noncomputable def leaf4027Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435723/268435456) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715741184) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (498747403/268435456) }, upper := { exponent := 0, mantissa := (121/64) } }, logOuter := sk114LogOuterCertificate, logK := sk114LogKCertificate, logChi := chi246LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434234879/137431482368) } }, logDArg := sk114LogDArgCertificate }

private noncomputable def leaf4027InnerLog : WideLogData :=
  innerPair199Data

set_option maxRecDepth 1000000 in
private theorem leaf4027LocalValidity :
    LeafFacts leaf4027Box leaf4027Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4027Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715741184) }) = true
      norm_num [leaf4027Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4027CertificateValid :
    WideCertificateValid leaf4027Box leaf4027Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk114ValidityFacts chi246ValidityFacts
    leaf4027LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4027CoverageChecked :
    coverageCheck (innerAD leaf4027Box) leaf4027InnerLog = true := by
  rfl'

private theorem leaf4027InnerLogValid :
    leaf4027InnerLog.Valid 8 (innerAD leaf4027Box) :=
  wideLogDataValid_of_cachedCheck endpoint61PositiveFacts
    endpoint69PositiveFacts.valid leaf4027CoverageChecked

private noncomputable def leaf4027InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629417/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4027InputLogOnePlusV_eq :
    leaf4027InputLogOnePlusV = outerEnclosure 24
      (leaf4027Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4027RoundedFacts : LeafRoundedFacts 8
    leaf4027Certificate.logOnePlusV leaf4027InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4027InputLogOnePlusV_eq }

private noncomputable def leaf4027Inputs : Inputs :=
  inputsOfCaches globalInput sk114RoundedInputs
    chi246InputQChi innerPair199Input
    leaf4027InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4027LowerChecked :
    lowerCheck 24 leaf4027Box leaf4027Inputs = true := by
  rfl'

private theorem leaf4027CoversExact : CoversExact 8
    leaf4027Box leaf4027Certificate leaf4027InnerLog leaf4027Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk114RoundedFacts chi246RoundedFacts
    innerPair199RoundedFacts leaf4027RoundedFacts (by rfl)

private theorem leaf4027FlatSound : Sound leaf4027Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4027CertificateValid
    leaf4027InnerLogValid leaf4027CoversExact leaf4027LowerChecked

private noncomputable def leaf4028Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (95/32), chiLo := (19/64), chiHi := (39/128) }

private noncomputable def leaf4028Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435723/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715682816) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (502482727/268435456) }, upper := { exponent := 0, mantissa := (7801/4096) } }, logOuter := sk113LogOuterCertificate, logK := sk113LogKCertificate, logChi := chi247LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434176511/137431365632) } }, logDArg := sk113LogDArgCertificate }

private noncomputable def leaf4028InnerLog : WideLogData :=
  innerPair483Data

set_option maxRecDepth 1000000 in
private theorem leaf4028LocalValidity :
    LeafFacts leaf4028Box leaf4028Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4028Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715682816) }) = true
      norm_num [leaf4028Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4028CertificateValid :
    WideCertificateValid leaf4028Box leaf4028Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk113ValidityFacts chi247ValidityFacts
    leaf4028LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4028CoverageChecked :
    coverageCheck (innerAD leaf4028Box) leaf4028InnerLog = true := by
  rfl'

private theorem leaf4028InnerLogValid :
    leaf4028InnerLog.Valid 8 (innerAD leaf4028Box) :=
  wideLogDataValid_of_cachedCheck endpoint211PositiveFacts
    endpoint70PositiveFacts.valid leaf4028CoverageChecked

private noncomputable def leaf4028InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (726839/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf4028InputLogOnePlusV_eq :
    leaf4028InputLogOnePlusV = outerEnclosure 24
      (leaf4028Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4028RoundedFacts : LeafRoundedFacts 8
    leaf4028Certificate.logOnePlusV leaf4028InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4028InputLogOnePlusV_eq }

private noncomputable def leaf4028Inputs : Inputs :=
  inputsOfCaches globalInput sk113RoundedInputs
    chi247InputQChi innerPair483Input
    leaf4028InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4028LowerChecked :
    lowerCheck 24 leaf4028Box leaf4028Inputs = true := by
  rfl'

private theorem leaf4028CoversExact : CoversExact 8
    leaf4028Box leaf4028Certificate leaf4028InnerLog leaf4028Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk113RoundedFacts chi247RoundedFacts
    innerPair483RoundedFacts leaf4028RoundedFacts (by rfl)

private theorem leaf4028FlatSound : Sound leaf4028Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4028CertificateValid
    leaf4028InnerLogValid leaf4028CoversExact leaf4028LowerChecked

private noncomputable def leaf4029Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (19/64), chiHi := (39/128) }

private noncomputable def leaf4029Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435725/268435456) }, vSqrt := { lower := (65529/65536), upper := (808452867/808419328) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (504972941/268435456) }, upper := { exponent := 0, mantissa := (245/128) } }, logOuter := sk114LogOuterCertificate, logK := sk114LogKCertificate, logChi := chi247LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (1616872195/1616838656) } }, logDArg := sk114LogDArgCertificate }

private noncomputable def leaf4029InnerLog : WideLogData :=
  innerPair106Data

set_option maxRecDepth 1000000 in
private theorem leaf4029LocalValidity :
    LeafFacts leaf4029Box leaf4029Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4029Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (808452867/808419328) }) = true
      norm_num [leaf4029Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4029CertificateValid :
    WideCertificateValid leaf4029Box leaf4029Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk114ValidityFacts chi247ValidityFacts
    leaf4029LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4029CoverageChecked :
    coverageCheck (innerAD leaf4029Box) leaf4029InnerLog = true := by
  rfl'

private theorem leaf4029InnerLogValid :
    leaf4029InnerLog.Valid 8 (innerAD leaf4029Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint81PositiveFacts.valid leaf4029CoverageChecked

private noncomputable def leaf4029InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629429/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4029InputLogOnePlusV_eq :
    leaf4029InputLogOnePlusV = outerEnclosure 24
      (leaf4029Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4029RoundedFacts : LeafRoundedFacts 8
    leaf4029Certificate.logOnePlusV leaf4029InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4029InputLogOnePlusV_eq }

private noncomputable def leaf4029Inputs : Inputs :=
  inputsOfCaches globalInput sk114RoundedInputs
    chi247InputQChi innerPair106Input
    leaf4029InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4029LowerChecked :
    lowerCheck 24 leaf4029Box leaf4029Inputs = true := by
  rfl'

private theorem leaf4029CoversExact : CoversExact 8
    leaf4029Box leaf4029Certificate leaf4029InnerLog leaf4029Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk114RoundedFacts chi247RoundedFacts
    innerPair106RoundedFacts leaf4029RoundedFacts (by rfl)

private theorem leaf4029FlatSound : Sound leaf4029Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4029CertificateValid
    leaf4029InnerLogValid leaf4029CoversExact leaf4029LowerChecked

private noncomputable def leaf4030Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (95/32), chiLo := (39/128), chiHi := (5/16) }

private noncomputable def leaf4030Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435725/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715585536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (508642733/268435456) }, upper := { exponent := 0, mantissa := (987/512) } }, logOuter := sk113LogOuterCertificate, logK := sk113LogKCertificate, logChi := chi248LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434079231/137431171072) } }, logDArg := sk113LogDArgCertificate }

private noncomputable def leaf4030InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4030LocalValidity :
    LeafFacts leaf4030Box leaf4030Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4030Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715585536) }) = true
      norm_num [leaf4030Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4030CertificateValid :
    WideCertificateValid leaf4030Box leaf4030Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk113ValidityFacts chi248ValidityFacts
    leaf4030LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4030CoverageChecked :
    coverageCheck (innerAD leaf4030Box) leaf4030InnerLog = true := by
  rfl'

private theorem leaf4030InnerLogValid :
    leaf4030InnerLog.Valid 8 (innerAD leaf4030Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4030CoverageChecked

private noncomputable def leaf4030InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907359/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4030InputLogOnePlusV_eq :
    leaf4030InputLogOnePlusV = outerEnclosure 24
      (leaf4030Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4030RoundedFacts : LeafRoundedFacts 8
    leaf4030Certificate.logOnePlusV leaf4030InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4030InputLogOnePlusV_eq }

private noncomputable def leaf4030Inputs : Inputs :=
  inputsOfCaches globalInput sk113RoundedInputs
    chi248InputQChi innerPair100Input
    leaf4030InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4030LowerChecked :
    lowerCheck 24 leaf4030Box leaf4030Inputs = true := by
  rfl'

private theorem leaf4030CoversExact : CoversExact 8
    leaf4030Box leaf4030Certificate leaf4030InnerLog leaf4030Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk113RoundedFacts chi248RoundedFacts
    innerPair100RoundedFacts leaf4030RoundedFacts (by rfl)

private theorem leaf4030FlatSound : Sound leaf4030Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4030CertificateValid
    leaf4030InnerLogValid leaf4030CoversExact leaf4030LowerChecked

private noncomputable def leaf4031Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (39/128), chiHi := (5/16) }

private noncomputable def leaf4031Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435727/268435456) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715544576) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (511198479/268435456) }, upper := { exponent := 0, mantissa := (31/16) } }, logOuter := sk114LogOuterCertificate, logK := sk114LogKCertificate, logChi := chi248LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434038271/137431089152) } }, logDArg := sk114LogDArgCertificate }

private noncomputable def leaf4031InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4031LocalValidity :
    LeafFacts leaf4031Box leaf4031Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4031Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715544576) }) = true
      norm_num [leaf4031Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4031CertificateValid :
    WideCertificateValid leaf4031Box leaf4031Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk114ValidityFacts chi248ValidityFacts
    leaf4031LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4031CoverageChecked :
    coverageCheck (innerAD leaf4031Box) leaf4031InnerLog = true := by
  rfl'

private theorem leaf4031InnerLogValid :
    leaf4031InnerLog.Valid 8 (innerAD leaf4031Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4031CoverageChecked

private noncomputable def leaf4031InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629441/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4031InputLogOnePlusV_eq :
    leaf4031InputLogOnePlusV = outerEnclosure 24
      (leaf4031Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4031RoundedFacts : LeafRoundedFacts 8
    leaf4031Certificate.logOnePlusV leaf4031InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4031InputLogOnePlusV_eq }

private noncomputable def leaf4031Inputs : Inputs :=
  inputsOfCaches globalInput sk114RoundedInputs
    chi248InputQChi innerPair100Input
    leaf4031InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4031LowerChecked :
    lowerCheck 24 leaf4031Box leaf4031Inputs = true := by
  rfl'

private theorem leaf4031CoversExact : CoversExact 8
    leaf4031Box leaf4031Certificate leaf4031InnerLog leaf4031Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk114RoundedFacts chi248RoundedFacts
    innerPair100RoundedFacts leaf4031RoundedFacts (by rfl)

private theorem leaf4031FlatSound : Sound leaf4031Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4031CertificateValid
    leaf4031InnerLogValid leaf4031CoversExact leaf4031LowerChecked

private noncomputable def component82Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component82Node0_sound : Sound component82Node0Box :=
  sound_of_literal_split component82Node0Box leaf3995Box leaf3996Box
    .chi (33/128) (by rfl) (by rfl)
    leaf3995FlatSound leaf3996FlatSound

private noncomputable def component82Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component82Node1_sound : Sound component82Node1Box :=
  sound_of_literal_split component82Node1Box leaf3997Box leaf3998Box
    .chi (33/128) (by rfl) (by rfl)
    leaf3997FlatSound leaf3998FlatSound

private noncomputable def component82Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component82Node2_sound : Sound component82Node2Box :=
  sound_of_literal_split component82Node2Box component82Node0Box component82Node1Box
    .k (93/32) (by rfl) (by rfl)
    component82Node0_sound component82Node1_sound

private noncomputable def component82Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component82Node3_sound : Sound component82Node3Box :=
  sound_of_literal_split component82Node3Box leaf3999Box leaf4000Box
    .chi (35/128) (by rfl) (by rfl)
    leaf3999FlatSound leaf4000FlatSound

private noncomputable def component82Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component82Node4_sound : Sound component82Node4Box :=
  sound_of_literal_split component82Node4Box leaf4001Box leaf4002Box
    .chi (35/128) (by rfl) (by rfl)
    leaf4001FlatSound leaf4002FlatSound

private noncomputable def component82Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component82Node5_sound : Sound component82Node5Box :=
  sound_of_literal_split component82Node5Box component82Node3Box component82Node4Box
    .k (93/32) (by rfl) (by rfl)
    component82Node3_sound component82Node4_sound

private noncomputable def component82Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (1/4), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component82Node6_sound : Sound component82Node6Box :=
  sound_of_literal_split component82Node6Box component82Node2Box component82Node5Box
    .chi (17/64) (by rfl) (by rfl)
    component82Node2_sound component82Node5_sound

private noncomputable def component82Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (95/32), chiLo := (1/4), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component82Node7_sound : Sound component82Node7Box :=
  sound_of_literal_split component82Node7Box leaf4003Box leaf4004Box
    .k (189/64) (by rfl) (by rfl)
    leaf4003FlatSound leaf4004FlatSound

private noncomputable def component82Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (95/32), chiLo := (33/128), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component82Node8_sound : Sound component82Node8Box :=
  sound_of_literal_split component82Node8Box leaf4005Box leaf4006Box
    .k (189/64) (by rfl) (by rfl)
    leaf4005FlatSound leaf4006FlatSound

private noncomputable def component82Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (95/32), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component82Node9_sound : Sound component82Node9Box :=
  sound_of_literal_split component82Node9Box component82Node7Box component82Node8Box
    .chi (33/128) (by rfl) (by rfl)
    component82Node7_sound component82Node8_sound

private noncomputable def component82Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (1/4), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component82Node10_sound : Sound component82Node10Box :=
  sound_of_literal_split component82Node10Box leaf4007Box leaf4008Box
    .k (191/64) (by rfl) (by rfl)
    leaf4007FlatSound leaf4008FlatSound

private noncomputable def component82Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (33/128), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component82Node11_sound : Sound component82Node11Box :=
  sound_of_literal_split component82Node11Box leaf4009Box leaf4010Box
    .k (191/64) (by rfl) (by rfl)
    leaf4009FlatSound leaf4010FlatSound

private noncomputable def component82Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component82Node12_sound : Sound component82Node12Box :=
  sound_of_literal_split component82Node12Box component82Node10Box component82Node11Box
    .chi (33/128) (by rfl) (by rfl)
    component82Node10_sound component82Node11_sound

private noncomputable def component82Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component82Node13_sound : Sound component82Node13Box :=
  sound_of_literal_split component82Node13Box component82Node9Box component82Node12Box
    .k (95/32) (by rfl) (by rfl)
    component82Node9_sound component82Node12_sound

private noncomputable def component82Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (17/64), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component82Node14_sound : Sound component82Node14Box :=
  sound_of_literal_split component82Node14Box leaf4012Box leaf4013Box
    .chi (69/256) (by rfl) (by rfl)
    leaf4012FlatSound leaf4013FlatSound

private noncomputable def component82Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (17/64), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component82Node15_sound : Sound component82Node15Box :=
  sound_of_literal_split component82Node15Box leaf4011Box component82Node14Box
    .k (95/32) (by rfl) (by rfl)
    leaf4011FlatSound component82Node14_sound

private noncomputable def component82Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (35/128), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component82Node16_sound : Sound component82Node16Box :=
  sound_of_literal_split component82Node16Box leaf4014Box leaf4015Box
    .k (95/32) (by rfl) (by rfl)
    leaf4014FlatSound leaf4015FlatSound

private noncomputable def component82Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component82Node17_sound : Sound component82Node17Box :=
  sound_of_literal_split component82Node17Box component82Node15Box component82Node16Box
    .chi (35/128) (by rfl) (by rfl)
    component82Node15_sound component82Node16_sound

private noncomputable def component82Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (1/4), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component82Node18_sound : Sound component82Node18Box :=
  sound_of_literal_split component82Node18Box component82Node13Box component82Node17Box
    .chi (17/64) (by rfl) (by rfl)
    component82Node13_sound component82Node17_sound

private noncomputable def component82Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (1/4), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component82Node19_sound : Sound component82Node19Box :=
  sound_of_literal_split component82Node19Box component82Node6Box component82Node18Box
    .k (47/16) (by rfl) (by rfl)
    component82Node6_sound component82Node18_sound

private noncomputable def component82Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component82Node20_sound : Sound component82Node20Box :=
  sound_of_literal_split component82Node20Box leaf4016Box leaf4017Box
    .chi (37/128) (by rfl) (by rfl)
    leaf4016FlatSound leaf4017FlatSound

private noncomputable def component82Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component82Node21_sound : Sound component82Node21Box :=
  sound_of_literal_split component82Node21Box leaf4018Box leaf4019Box
    .chi (37/128) (by rfl) (by rfl)
    leaf4018FlatSound leaf4019FlatSound

private noncomputable def component82Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component82Node22_sound : Sound component82Node22Box :=
  sound_of_literal_split component82Node22Box component82Node20Box component82Node21Box
    .k (93/32) (by rfl) (by rfl)
    component82Node20_sound component82Node21_sound

private noncomputable def component82Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (19/64), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component82Node23_sound : Sound component82Node23Box :=
  sound_of_literal_split component82Node23Box leaf4020Box leaf4021Box
    .k (93/32) (by rfl) (by rfl)
    leaf4020FlatSound leaf4021FlatSound

private noncomputable def component82Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (39/128), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component82Node24_sound : Sound component82Node24Box :=
  sound_of_literal_split component82Node24Box leaf4022Box leaf4023Box
    .k (93/32) (by rfl) (by rfl)
    leaf4022FlatSound leaf4023FlatSound

private noncomputable def component82Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (19/64), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component82Node25_sound : Sound component82Node25Box :=
  sound_of_literal_split component82Node25Box component82Node23Box component82Node24Box
    .chi (39/128) (by rfl) (by rfl)
    component82Node23_sound component82Node24_sound

private noncomputable def component82Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (9/32), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component82Node26_sound : Sound component82Node26Box :=
  sound_of_literal_split component82Node26Box component82Node22Box component82Node25Box
    .chi (19/64) (by rfl) (by rfl)
    component82Node22_sound component82Node25_sound

private noncomputable def component82Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (9/32), chiHi := (37/128) }

set_option maxRecDepth 1000000 in
private theorem component82Node27_sound : Sound component82Node27Box :=
  sound_of_literal_split component82Node27Box leaf4024Box leaf4025Box
    .k (95/32) (by rfl) (by rfl)
    leaf4024FlatSound leaf4025FlatSound

private noncomputable def component82Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (37/128), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component82Node28_sound : Sound component82Node28Box :=
  sound_of_literal_split component82Node28Box leaf4026Box leaf4027Box
    .k (95/32) (by rfl) (by rfl)
    leaf4026FlatSound leaf4027FlatSound

private noncomputable def component82Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component82Node29_sound : Sound component82Node29Box :=
  sound_of_literal_split component82Node29Box component82Node27Box component82Node28Box
    .chi (37/128) (by rfl) (by rfl)
    component82Node27_sound component82Node28_sound

private noncomputable def component82Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (19/64), chiHi := (39/128) }

set_option maxRecDepth 1000000 in
private theorem component82Node30_sound : Sound component82Node30Box :=
  sound_of_literal_split component82Node30Box leaf4028Box leaf4029Box
    .k (95/32) (by rfl) (by rfl)
    leaf4028FlatSound leaf4029FlatSound

private noncomputable def component82Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (39/128), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component82Node31_sound : Sound component82Node31Box :=
  sound_of_literal_split component82Node31Box leaf4030Box leaf4031Box
    .k (95/32) (by rfl) (by rfl)
    leaf4030FlatSound leaf4031FlatSound

private noncomputable def component82Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (19/64), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component82Node32_sound : Sound component82Node32Box :=
  sound_of_literal_split component82Node32Box component82Node30Box component82Node31Box
    .chi (39/128) (by rfl) (by rfl)
    component82Node30_sound component82Node31_sound

private noncomputable def component82Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (9/32), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component82Node33_sound : Sound component82Node33Box :=
  sound_of_literal_split component82Node33Box component82Node29Box component82Node32Box
    .chi (19/64) (by rfl) (by rfl)
    component82Node29_sound component82Node32_sound

private noncomputable def component82Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (9/32), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component82Node34_sound : Sound component82Node34Box :=
  sound_of_literal_split component82Node34Box component82Node26Box component82Node33Box
    .k (47/16) (by rfl) (by rfl)
    component82Node26_sound component82Node33_sound

noncomputable def component82Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (1/4), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
theorem component82_sound : Sound component82Box :=
  sound_of_literal_split component82Box component82Node19Box component82Node34Box
    .chi (9/32) (by rfl) (by rfl)
    component82Node19_sound component82Node34_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
