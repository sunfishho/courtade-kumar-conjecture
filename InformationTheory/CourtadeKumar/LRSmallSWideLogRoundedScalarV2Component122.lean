import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch6
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch7
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch10
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch11
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch5
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

private noncomputable def leaf6087Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (7/16), chiHi := (57/128) }

private noncomputable def leaf6087Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435811/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712414208) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (708777375/536870912) }, upper := { exponent := 1, mantissa := (10993/8192) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi267LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428810749/137424828416) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf6087InnerLog : WideLogData :=
  innerPair345Data

set_option maxRecDepth 1000000 in
private theorem leaf6087LocalValidity :
    LeafFacts leaf6087Box leaf6087Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6087Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712414208) }) = true
      norm_num [leaf6087Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6087CertificateValid :
    WideCertificateValid leaf6087Box leaf6087Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi267ValidityFacts
    leaf6087LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6087CoverageChecked :
    coverageCheck (innerAD leaf6087Box) leaf6087InnerLog = true := by
  rfl'

private theorem leaf6087InnerLogValid :
    leaf6087InnerLog.Valid 8 (innerAD leaf6087Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint92PositiveFacts.valid leaf6087CoverageChecked

private noncomputable def leaf6087InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629567/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6087InputLogOnePlusV_eq :
    leaf6087InputLogOnePlusV = outerEnclosure 24
      (leaf6087Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6087RoundedFacts : LeafRoundedFacts 8
    leaf6087Certificate.logOnePlusV leaf6087InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6087InputLogOnePlusV_eq }

private noncomputable def leaf6087Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi267InputQChi innerPair345Input
    leaf6087InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6087LowerChecked :
    lowerCheck 24 leaf6087Box leaf6087Inputs = true := by
  rfl'

private theorem leaf6087CoversExact : CoversExact 8
    leaf6087Box leaf6087Certificate leaf6087InnerLog leaf6087Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi267RoundedFacts
    innerPair345RoundedFacts leaf6087RoundedFacts (by rfl)

private theorem leaf6087FlatSound : Sound leaf6087Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6087CertificateValid
    leaf6087InnerLogValid leaf6087CoversExact leaf6087LowerChecked

private noncomputable def leaf6088Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (7/16), chiHi := (57/128) }

private noncomputable def leaf6088Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435813/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712355840) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (712447165/536870912) }, upper := { exponent := 1, mantissa := (5525/4096) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi267LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428752381/137424711680) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf6088InnerLog : WideLogData :=
  innerPair365Data

set_option maxRecDepth 1000000 in
private theorem leaf6088LocalValidity :
    LeafFacts leaf6088Box leaf6088Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6088Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712355840) }) = true
      norm_num [leaf6088Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6088CertificateValid :
    WideCertificateValid leaf6088Box leaf6088Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi267ValidityFacts
    leaf6088LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6088CoverageChecked :
    coverageCheck (innerAD leaf6088Box) leaf6088InnerLog = true := by
  rfl'

private theorem leaf6088InnerLogValid :
    leaf6088InnerLog.Valid 8 (innerAD leaf6088Box) :=
  wideLogDataValid_of_cachedCheck endpoint95PositiveFacts
    endpoint451PositiveFacts.valid leaf6088CoverageChecked

private noncomputable def leaf6088InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814787/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6088InputLogOnePlusV_eq :
    leaf6088InputLogOnePlusV = outerEnclosure 24
      (leaf6088Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6088RoundedFacts : LeafRoundedFacts 8
    leaf6088Certificate.logOnePlusV leaf6088InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6088InputLogOnePlusV_eq }

private noncomputable def leaf6088Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi267InputQChi innerPair365Input
    leaf6088InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6088LowerChecked :
    lowerCheck 24 leaf6088Box leaf6088Inputs = true := by
  rfl'

private theorem leaf6088CoversExact : CoversExact 8
    leaf6088Box leaf6088Certificate leaf6088InnerLog leaf6088Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi267RoundedFacts
    innerPair365RoundedFacts leaf6088RoundedFacts (by rfl)

private theorem leaf6088FlatSound : Sound leaf6088Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6088CertificateValid
    leaf6088InnerLogValid leaf6088CoversExact leaf6088LowerChecked

private noncomputable def leaf6089Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (57/128), chiHi := (29/64) }

private noncomputable def leaf6089Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435813/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712290304) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (716641213/536870912) }, upper := { exponent := 1, mantissa := (5557/4096) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi268LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428686845/137424580608) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf6089InnerLog : WideLogData :=
  innerPair703Data

set_option maxRecDepth 1000000 in
private theorem leaf6089LocalValidity :
    LeafFacts leaf6089Box leaf6089Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6089Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712290304) }) = true
      norm_num [leaf6089Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6089CertificateValid :
    WideCertificateValid leaf6089Box leaf6089Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi268ValidityFacts
    leaf6089LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6089CoverageChecked :
    coverageCheck (innerAD leaf6089Box) leaf6089InnerLog = true := by
  rfl'

private theorem leaf6089InnerLogValid :
    leaf6089InnerLog.Valid 8 (innerAD leaf6089Box) :=
  wideLogDataValid_of_cachedCheck endpoint447PositiveFacts
    endpoint461PositiveFacts.valid leaf6089CoverageChecked

private noncomputable def leaf6089InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814791/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6089InputLogOnePlusV_eq :
    leaf6089InputLogOnePlusV = outerEnclosure 24
      (leaf6089Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6089RoundedFacts : LeafRoundedFacts 8
    leaf6089Certificate.logOnePlusV leaf6089InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6089InputLogOnePlusV_eq }

private noncomputable def leaf6089Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi268InputQChi innerPair703Input
    leaf6089InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6089LowerChecked :
    lowerCheck 24 leaf6089Box leaf6089Inputs = true := by
  rfl'

private theorem leaf6089CoversExact : CoversExact 8
    leaf6089Box leaf6089Certificate leaf6089InnerLog leaf6089Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi268RoundedFacts
    innerPair703RoundedFacts leaf6089RoundedFacts (by rfl)

private theorem leaf6089FlatSound : Sound leaf6089Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6089CertificateValid
    leaf6089InnerLogValid leaf6089CoversExact leaf6089LowerChecked

private noncomputable def leaf6090Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (57/128), chiHi := (29/64) }

private noncomputable def leaf6090Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435815/268435456) }, vSqrt := { lower := (8191/8192), upper := (310933921/310915072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (720376535/536870912) }, upper := { exponent := 1, mantissa := (2793/2048) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi268LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (621848993/621830144) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf6090InnerLog : WideLogData :=
  innerPair346Data

set_option maxRecDepth 1000000 in
private theorem leaf6090LocalValidity :
    LeafFacts leaf6090Box leaf6090Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6090Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (310933921/310915072) }) = true
      norm_num [leaf6090Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6090CertificateValid :
    WideCertificateValid leaf6090Box leaf6090Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi268ValidityFacts
    leaf6090LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6090CoverageChecked :
    coverageCheck (innerAD leaf6090Box) leaf6090InnerLog = true := by
  rfl'

private theorem leaf6090InnerLogValid :
    leaf6090InnerLog.Valid 8 (innerAD leaf6090Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint93PositiveFacts.valid leaf6090CoverageChecked

private noncomputable def leaf6090InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629589/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6090InputLogOnePlusV_eq :
    leaf6090InputLogOnePlusV = outerEnclosure 24
      (leaf6090Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6090RoundedFacts : LeafRoundedFacts 8
    leaf6090Certificate.logOnePlusV leaf6090InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6090InputLogOnePlusV_eq }

private noncomputable def leaf6090Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi268InputQChi innerPair346Input
    leaf6090InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6090LowerChecked :
    lowerCheck 24 leaf6090Box leaf6090Inputs = true := by
  rfl'

private theorem leaf6090CoversExact : CoversExact 8
    leaf6090Box leaf6090Certificate leaf6090InnerLog leaf6090Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi268RoundedFacts
    innerPair346RoundedFacts leaf6090RoundedFacts (by rfl)

private theorem leaf6090FlatSound : Sound leaf6090Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6090CertificateValid
    leaf6090InnerLogValid leaf6090CoversExact leaf6090LowerChecked

private noncomputable def leaf6091Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (7/16), chiHi := (57/128) }

private noncomputable def leaf6091Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435815/268435456) }, vSqrt := { lower := (8191/8192), upper := (5285876657/5285561344) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (716116955/536870912) }, upper := { exponent := 1, mantissa := (11107/8192) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi267LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (10571438001/10571122688) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf6091InnerLog : WideLogData :=
  innerPair703Data

set_option maxRecDepth 1000000 in
private theorem leaf6091LocalValidity :
    LeafFacts leaf6091Box leaf6091Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6091Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5285876657/5285561344) }) = true
      norm_num [leaf6091Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6091CertificateValid :
    WideCertificateValid leaf6091Box leaf6091Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi267ValidityFacts
    leaf6091LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6091CoverageChecked :
    coverageCheck (innerAD leaf6091Box) leaf6091InnerLog = true := by
  rfl'

private theorem leaf6091InnerLogValid :
    leaf6091InnerLog.Valid 8 (innerAD leaf6091Box) :=
  wideLogDataValid_of_cachedCheck endpoint447PositiveFacts
    endpoint461PositiveFacts.valid leaf6091CoverageChecked

private noncomputable def leaf6091InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629581/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6091InputLogOnePlusV_eq :
    leaf6091InputLogOnePlusV = outerEnclosure 24
      (leaf6091Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6091RoundedFacts : LeafRoundedFacts 8
    leaf6091Certificate.logOnePlusV leaf6091InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6091InputLogOnePlusV_eq }

private noncomputable def leaf6091Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi267InputQChi innerPair703Input
    leaf6091InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6091LowerChecked :
    lowerCheck 24 leaf6091Box leaf6091Inputs = true := by
  rfl'

private theorem leaf6091CoversExact : CoversExact 8
    leaf6091Box leaf6091Certificate leaf6091InnerLog leaf6091Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi267RoundedFacts
    innerPair703RoundedFacts leaf6091RoundedFacts (by rfl)

private theorem leaf6091FlatSound : Sound leaf6091Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6091CertificateValid
    leaf6091InnerLogValid leaf6091CoversExact leaf6091LowerChecked

private noncomputable def leaf6092Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (7/16), chiHi := (57/128) }

private noncomputable def leaf6092Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435817/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712239104) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (719786745/536870912) }, upper := { exponent := 1, mantissa := (2791/2048) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi267LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428635645/137424478208) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf6092InnerLog : WideLogData :=
  innerPair705Data

set_option maxRecDepth 1000000 in
private theorem leaf6092LocalValidity :
    LeafFacts leaf6092Box leaf6092Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6092Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712239104) }) = true
      norm_num [leaf6092Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6092CertificateValid :
    WideCertificateValid leaf6092Box leaf6092Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi267ValidityFacts
    leaf6092LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6092CoverageChecked :
    coverageCheck (innerAD leaf6092Box) leaf6092InnerLog = true := by
  rfl'

private theorem leaf6092InnerLogValid :
    leaf6092InnerLog.Valid 8 (innerAD leaf6092Box) :=
  wideLogDataValid_of_cachedCheck endpoint448PositiveFacts
    endpoint462PositiveFacts.valid leaf6092CoverageChecked

private noncomputable def leaf6092InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907397/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6092InputLogOnePlusV_eq :
    leaf6092InputLogOnePlusV = outerEnclosure 24
      (leaf6092Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6092RoundedFacts : LeafRoundedFacts 8
    leaf6092Certificate.logOnePlusV leaf6092InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6092InputLogOnePlusV_eq }

private noncomputable def leaf6092Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi267InputQChi innerPair705Input
    leaf6092InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6092LowerChecked :
    lowerCheck 24 leaf6092Box leaf6092Inputs = true := by
  rfl'

private theorem leaf6092CoversExact : CoversExact 8
    leaf6092Box leaf6092Certificate leaf6092InnerLog leaf6092Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi267RoundedFacts
    innerPair705RoundedFacts leaf6092RoundedFacts (by rfl)

private theorem leaf6092FlatSound : Sound leaf6092Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6092CertificateValid
    leaf6092InnerLogValid leaf6092CoversExact leaf6092LowerChecked

private noncomputable def leaf6093Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (57/128), chiHi := (29/64) }

private noncomputable def leaf6093Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435817/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712171520) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (724111857/536870912) }, upper := { exponent := 1, mantissa := (5615/4096) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi268LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428568061/137424343040) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf6093InnerLog : WideLogData :=
  innerPair352Data

set_option maxRecDepth 1000000 in
private theorem leaf6093LocalValidity :
    LeafFacts leaf6093Box leaf6093Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6093Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712171520) }) = true
      norm_num [leaf6093Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6093CertificateValid :
    WideCertificateValid leaf6093Box leaf6093Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi268ValidityFacts
    leaf6093LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6093CoverageChecked :
    coverageCheck (innerAD leaf6093Box) leaf6093InnerLog = true := by
  rfl'

private theorem leaf6093InnerLogValid :
    leaf6093InnerLog.Valid 8 (innerAD leaf6093Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint93PositiveFacts.valid leaf6093CoverageChecked

private noncomputable def leaf6093InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629597/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6093InputLogOnePlusV_eq :
    leaf6093InputLogOnePlusV = outerEnclosure 24
      (leaf6093Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6093RoundedFacts : LeafRoundedFacts 8
    leaf6093Certificate.logOnePlusV leaf6093InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6093InputLogOnePlusV_eq }

private noncomputable def leaf6093Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi268InputQChi innerPair352Input
    leaf6093InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6093LowerChecked :
    lowerCheck 24 leaf6093Box leaf6093Inputs = true := by
  rfl'

private theorem leaf6093CoversExact : CoversExact 8
    leaf6093Box leaf6093Certificate leaf6093InnerLog leaf6093Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi268RoundedFacts
    innerPair352RoundedFacts leaf6093RoundedFacts (by rfl)

private theorem leaf6093FlatSound : Sound leaf6093Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6093CertificateValid
    leaf6093InnerLogValid leaf6093CoversExact leaf6093LowerChecked

private noncomputable def leaf6094Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (57/128), chiHi := (29/64) }

private noncomputable def leaf6094Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435819/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712112128) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (727847179/536870912) }, upper := { exponent := 1, mantissa := (1411/1024) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi268LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428508669/137424224256) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf6094InnerLog : WideLogData :=
  innerPair708Data

set_option maxRecDepth 1000000 in
private theorem leaf6094LocalValidity :
    LeafFacts leaf6094Box leaf6094Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6094Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712112128) }) = true
      norm_num [leaf6094Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6094CertificateValid :
    WideCertificateValid leaf6094Box leaf6094Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi268ValidityFacts
    leaf6094LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6094CoverageChecked :
    coverageCheck (innerAD leaf6094Box) leaf6094InnerLog = true := by
  rfl'

private theorem leaf6094InnerLogValid :
    leaf6094InnerLog.Valid 8 (innerAD leaf6094Box) :=
  wideLogDataValid_of_cachedCheck endpoint451PositiveFacts
    endpoint460PositiveFacts.valid leaf6094CoverageChecked

private noncomputable def leaf6094InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907401/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6094InputLogOnePlusV_eq :
    leaf6094InputLogOnePlusV = outerEnclosure 24
      (leaf6094Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6094RoundedFacts : LeafRoundedFacts 8
    leaf6094Certificate.logOnePlusV leaf6094InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6094InputLogOnePlusV_eq }

private noncomputable def leaf6094Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi268InputQChi innerPair708Input
    leaf6094InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6094LowerChecked :
    lowerCheck 24 leaf6094Box leaf6094Inputs = true := by
  rfl'

private theorem leaf6094CoversExact : CoversExact 8
    leaf6094Box leaf6094Certificate leaf6094InnerLog leaf6094Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi268RoundedFacts
    innerPair708RoundedFacts leaf6094RoundedFacts (by rfl)

private theorem leaf6094FlatSound : Sound leaf6094Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6094CertificateValid
    leaf6094InnerLogValid leaf6094CoversExact leaf6094LowerChecked

private noncomputable def leaf6095Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (29/64), chiHi := (59/128) }

private noncomputable def leaf6095Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435815/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712166400) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (724505051/536870912) }, upper := { exponent := 1, mantissa := (11235/8192) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi269LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428562941/137424332800) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf6095InnerLog : WideLogData :=
  innerPair352Data

set_option maxRecDepth 1000000 in
private theorem leaf6095LocalValidity :
    LeafFacts leaf6095Box leaf6095Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6095Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712166400) }) = true
      norm_num [leaf6095Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6095CertificateValid :
    WideCertificateValid leaf6095Box leaf6095Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi269ValidityFacts
    leaf6095LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6095CoverageChecked :
    coverageCheck (innerAD leaf6095Box) leaf6095InnerLog = true := by
  rfl'

private theorem leaf6095InnerLogValid :
    leaf6095InnerLog.Valid 8 (innerAD leaf6095Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint93PositiveFacts.valid leaf6095CoverageChecked

private noncomputable def leaf6095InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629597/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6095InputLogOnePlusV_eq :
    leaf6095InputLogOnePlusV = outerEnclosure 24
      (leaf6095Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6095RoundedFacts : LeafRoundedFacts 8
    leaf6095Certificate.logOnePlusV leaf6095InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6095InputLogOnePlusV_eq }

private noncomputable def leaf6095Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi269InputQChi innerPair352Input
    leaf6095InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6095LowerChecked :
    lowerCheck 24 leaf6095Box leaf6095Inputs = true := by
  rfl'

private theorem leaf6095CoversExact : CoversExact 8
    leaf6095Box leaf6095Certificate leaf6095InnerLog leaf6095Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi269RoundedFacts
    innerPair352RoundedFacts leaf6095RoundedFacts (by rfl)

private theorem leaf6095FlatSound : Sound leaf6095Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6095CertificateValid
    leaf6095InnerLogValid leaf6095CoversExact leaf6095LowerChecked

private noncomputable def leaf6096Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (29/64), chiHi := (59/128) }

private noncomputable def leaf6096Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435817/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712105984) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (728305905/536870912) }, upper := { exponent := 1, mantissa := (5647/4096) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi269LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428502525/137424211968) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf6096InnerLog : WideLogData :=
  innerPair708Data

set_option maxRecDepth 1000000 in
private theorem leaf6096LocalValidity :
    LeafFacts leaf6096Box leaf6096Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6096Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712105984) }) = true
      norm_num [leaf6096Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6096CertificateValid :
    WideCertificateValid leaf6096Box leaf6096Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi269ValidityFacts
    leaf6096LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6096CoverageChecked :
    coverageCheck (innerAD leaf6096Box) leaf6096InnerLog = true := by
  rfl'

private theorem leaf6096InnerLogValid :
    leaf6096InnerLog.Valid 8 (innerAD leaf6096Box) :=
  wideLogDataValid_of_cachedCheck endpoint451PositiveFacts
    endpoint460PositiveFacts.valid leaf6096CoverageChecked

private noncomputable def leaf6096InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629605/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6096InputLogOnePlusV_eq :
    leaf6096InputLogOnePlusV = outerEnclosure 24
      (leaf6096Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6096RoundedFacts : LeafRoundedFacts 8
    leaf6096Certificate.logOnePlusV leaf6096InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6096InputLogOnePlusV_eq }

private noncomputable def leaf6096Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi269InputQChi innerPair708Input
    leaf6096InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6096LowerChecked :
    lowerCheck 24 leaf6096Box leaf6096Inputs = true := by
  rfl'

private theorem leaf6096CoversExact : CoversExact 8
    leaf6096Box leaf6096Certificate leaf6096InnerLog leaf6096Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi269RoundedFacts
    innerPair708RoundedFacts leaf6096RoundedFacts (by rfl)

private theorem leaf6096FlatSound : Sound leaf6096Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6096CertificateValid
    leaf6096InnerLogValid leaf6096CoversExact leaf6096LowerChecked

private noncomputable def leaf6097Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (59/128), chiHi := (15/32) }

private noncomputable def leaf6097Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435817/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712042496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (732368889/536870912) }, upper := { exponent := 1, mantissa := (2839/2048) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi270LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428439037/137424084992) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf6097InnerLog : WideLogData :=
  innerPair353Data

set_option maxRecDepth 1000000 in
private theorem leaf6097LocalValidity :
    LeafFacts leaf6097Box leaf6097Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6097Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712042496) }) = true
      norm_num [leaf6097Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6097CertificateValid :
    WideCertificateValid leaf6097Box leaf6097Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi270ValidityFacts
    leaf6097LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6097CoverageChecked :
    coverageCheck (innerAD leaf6097Box) leaf6097InnerLog = true := by
  rfl'

private theorem leaf6097InnerLogValid :
    leaf6097InnerLog.Valid 8 (innerAD leaf6097Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint96PositiveFacts.valid leaf6097CoverageChecked

private noncomputable def leaf6097InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907403/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6097InputLogOnePlusV_eq :
    leaf6097InputLogOnePlusV = outerEnclosure 24
      (leaf6097Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6097RoundedFacts : LeafRoundedFacts 8
    leaf6097Certificate.logOnePlusV leaf6097InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6097InputLogOnePlusV_eq }

private noncomputable def leaf6097Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi270InputQChi innerPair353Input
    leaf6097InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6097LowerChecked :
    lowerCheck 24 leaf6097Box leaf6097Inputs = true := by
  rfl'

private theorem leaf6097CoversExact : CoversExact 8
    leaf6097Box leaf6097Certificate leaf6097InnerLog leaf6097Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi270RoundedFacts
    innerPair353RoundedFacts leaf6097RoundedFacts (by rfl)

private theorem leaf6097FlatSound : Sound leaf6097Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6097CertificateValid
    leaf6097InnerLogValid leaf6097CoversExact leaf6097LowerChecked

private noncomputable def leaf6098Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (59/128), chiHi := (15/32) }

private noncomputable def leaf6098Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435819/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711981056) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (736235275/536870912) }, upper := { exponent := 1, mantissa := (1427/1024) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi270LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428377597/137423962112) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf6098InnerLog : WideLogData :=
  innerPair353Data

set_option maxRecDepth 1000000 in
private theorem leaf6098LocalValidity :
    LeafFacts leaf6098Box leaf6098Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6098Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711981056) }) = true
      norm_num [leaf6098Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6098CertificateValid :
    WideCertificateValid leaf6098Box leaf6098Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi270ValidityFacts
    leaf6098LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6098CoverageChecked :
    coverageCheck (innerAD leaf6098Box) leaf6098InnerLog = true := by
  rfl'

private theorem leaf6098InnerLogValid :
    leaf6098InnerLog.Valid 8 (innerAD leaf6098Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint96PositiveFacts.valid leaf6098CoverageChecked

private noncomputable def leaf6098InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907405/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6098InputLogOnePlusV_eq :
    leaf6098InputLogOnePlusV = outerEnclosure 24
      (leaf6098Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6098RoundedFacts : LeafRoundedFacts 8
    leaf6098Certificate.logOnePlusV leaf6098InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6098InputLogOnePlusV_eq }

private noncomputable def leaf6098Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi270InputQChi innerPair353Input
    leaf6098InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6098LowerChecked :
    lowerCheck 24 leaf6098Box leaf6098Inputs = true := by
  rfl'

private theorem leaf6098CoversExact : CoversExact 8
    leaf6098Box leaf6098Certificate leaf6098InnerLog leaf6098Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi270RoundedFacts
    innerPair353RoundedFacts leaf6098RoundedFacts (by rfl)

private theorem leaf6098FlatSound : Sound leaf6098Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6098CertificateValid
    leaf6098InnerLogValid leaf6098CoversExact leaf6098LowerChecked

private noncomputable def leaf6099Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (29/64), chiHi := (59/128) }

private noncomputable def leaf6099Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435819/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712045568) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (732106759/536870912) }, upper := { exponent := 1, mantissa := (11353/8192) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi269LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428442109/137424091136) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf6099InnerLog : WideLogData :=
  innerPair720Data

set_option maxRecDepth 1000000 in
private theorem leaf6099LocalValidity :
    LeafFacts leaf6099Box leaf6099Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6099Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712045568) }) = true
      norm_num [leaf6099Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6099CertificateValid :
    WideCertificateValid leaf6099Box leaf6099Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi269ValidityFacts
    leaf6099LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6099CoverageChecked :
    coverageCheck (innerAD leaf6099Box) leaf6099InnerLog = true := by
  rfl'

private theorem leaf6099InnerLogValid :
    leaf6099InnerLog.Valid 8 (innerAD leaf6099Box) :=
  wideLogDataValid_of_cachedCheck endpoint461PositiveFacts
    endpoint463PositiveFacts.valid leaf6099CoverageChecked

private noncomputable def leaf6099InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907403/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6099InputLogOnePlusV_eq :
    leaf6099InputLogOnePlusV = outerEnclosure 24
      (leaf6099Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6099RoundedFacts : LeafRoundedFacts 8
    leaf6099Certificate.logOnePlusV leaf6099InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6099InputLogOnePlusV_eq }

private noncomputable def leaf6099Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi269InputQChi innerPair720Input
    leaf6099InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6099LowerChecked :
    lowerCheck 24 leaf6099Box leaf6099Inputs = true := by
  rfl'

private theorem leaf6099CoversExact : CoversExact 8
    leaf6099Box leaf6099Certificate leaf6099InnerLog leaf6099Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi269RoundedFacts
    innerPair720RoundedFacts leaf6099RoundedFacts (by rfl)

private theorem leaf6099FlatSound : Sound leaf6099Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6099CertificateValid
    leaf6099InnerLogValid leaf6099CoversExact leaf6099LowerChecked

private noncomputable def leaf6100Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (29/64), chiHi := (59/128) }

private noncomputable def leaf6100Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435821/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711985152) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (735907613/536870912) }, upper := { exponent := 1, mantissa := (2853/2048) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi269LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428381693/137423970304) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf6100InnerLog : WideLogData :=
  innerPair353Data

set_option maxRecDepth 1000000 in
private theorem leaf6100LocalValidity :
    LeafFacts leaf6100Box leaf6100Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6100Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711985152) }) = true
      norm_num [leaf6100Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6100CertificateValid :
    WideCertificateValid leaf6100Box leaf6100Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi269ValidityFacts
    leaf6100LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6100CoverageChecked :
    coverageCheck (innerAD leaf6100Box) leaf6100InnerLog = true := by
  rfl'

private theorem leaf6100InnerLogValid :
    leaf6100InnerLog.Valid 8 (innerAD leaf6100Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint96PositiveFacts.valid leaf6100CoverageChecked

private noncomputable def leaf6100InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629619/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6100InputLogOnePlusV_eq :
    leaf6100InputLogOnePlusV = outerEnclosure 24
      (leaf6100Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6100RoundedFacts : LeafRoundedFacts 8
    leaf6100Certificate.logOnePlusV leaf6100InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6100InputLogOnePlusV_eq }

private noncomputable def leaf6100Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi269InputQChi innerPair353Input
    leaf6100InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6100LowerChecked :
    lowerCheck 24 leaf6100Box leaf6100Inputs = true := by
  rfl'

private theorem leaf6100CoversExact : CoversExact 8
    leaf6100Box leaf6100Certificate leaf6100InnerLog leaf6100Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi269RoundedFacts
    innerPair353RoundedFacts leaf6100RoundedFacts (by rfl)

private theorem leaf6100FlatSound : Sound leaf6100Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6100CertificateValid
    leaf6100InnerLogValid leaf6100CoversExact leaf6100LowerChecked

private noncomputable def leaf6101Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (59/128), chiHi := (15/32) }

private noncomputable def leaf6101Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435821/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711919616) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (740101661/536870912) }, upper := { exponent := 1, mantissa := (2869/2048) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi270LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428316157/137423839232) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf6101InnerLog : WideLogData :=
  innerPair356Data

set_option maxRecDepth 1000000 in
private theorem leaf6101LocalValidity :
    LeafFacts leaf6101Box leaf6101Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6101Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711919616) }) = true
      norm_num [leaf6101Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6101CertificateValid :
    WideCertificateValid leaf6101Box leaf6101Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi270ValidityFacts
    leaf6101LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6101CoverageChecked :
    coverageCheck (innerAD leaf6101Box) leaf6101InnerLog = true := by
  rfl'

private theorem leaf6101InnerLogValid :
    leaf6101InnerLog.Valid 8 (innerAD leaf6101Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint96PositiveFacts.valid leaf6101CoverageChecked

private noncomputable def leaf6101InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629627/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6101InputLogOnePlusV_eq :
    leaf6101InputLogOnePlusV = outerEnclosure 24
      (leaf6101Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6101RoundedFacts : LeafRoundedFacts 8
    leaf6101Certificate.logOnePlusV leaf6101InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6101InputLogOnePlusV_eq }

private noncomputable def leaf6101Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi270InputQChi innerPair356Input
    leaf6101InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6101LowerChecked :
    lowerCheck 24 leaf6101Box leaf6101Inputs = true := by
  rfl'

private theorem leaf6101CoversExact : CoversExact 8
    leaf6101Box leaf6101Certificate leaf6101InnerLog leaf6101Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi270RoundedFacts
    innerPair356RoundedFacts leaf6101RoundedFacts (by rfl)

private theorem leaf6101FlatSound : Sound leaf6101Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6101CertificateValid
    leaf6101InnerLogValid leaf6101CoversExact leaf6101LowerChecked

private noncomputable def leaf6102Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (59/128), chiHi := (15/32) }

private noncomputable def leaf6102Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435823/268435456) }, vSqrt := { lower := (8191/8192), upper := (5285876657/5285527552) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (743968047/536870912) }, upper := { exponent := 1, mantissa := (721/512) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi270LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (10571404209/10571055104) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf6102InnerLog : WideLogData :=
  innerPair718Data

set_option maxRecDepth 1000000 in
private theorem leaf6102LocalValidity :
    LeafFacts leaf6102Box leaf6102Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6102Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5285876657/5285527552) }) = true
      norm_num [leaf6102Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6102CertificateValid :
    WideCertificateValid leaf6102Box leaf6102Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi270ValidityFacts
    leaf6102LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6102CoverageChecked :
    coverageCheck (innerAD leaf6102Box) leaf6102InnerLog = true := by
  rfl'

private theorem leaf6102InnerLogValid :
    leaf6102InnerLog.Valid 8 (innerAD leaf6102Box) :=
  wideLogDataValid_of_cachedCheck endpoint460PositiveFacts
    endpoint464PositiveFacts.valid leaf6102CoverageChecked

private noncomputable def leaf6102InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629635/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6102InputLogOnePlusV_eq :
    leaf6102InputLogOnePlusV = outerEnclosure 24
      (leaf6102Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6102RoundedFacts : LeafRoundedFacts 8
    leaf6102Certificate.logOnePlusV leaf6102InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6102InputLogOnePlusV_eq }

private noncomputable def leaf6102Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi270InputQChi innerPair718Input
    leaf6102InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6102LowerChecked :
    lowerCheck 24 leaf6102Box leaf6102Inputs = true := by
  rfl'

private theorem leaf6102CoversExact : CoversExact 8
    leaf6102Box leaf6102Certificate leaf6102InnerLog leaf6102Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi270RoundedFacts
    innerPair718RoundedFacts leaf6102RoundedFacts (by rfl)

private theorem leaf6102FlatSound : Sound leaf6102Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6102CertificateValid
    leaf6102InnerLogValid leaf6102CoversExact leaf6102LowerChecked

private noncomputable def leaf6103Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (7/16), chiHi := (57/128) }

private noncomputable def leaf6103Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435819/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712180736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (723456535/536870912) }, upper := { exponent := 1, mantissa := (11221/8192) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi267LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428577277/137424361472) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf6103InnerLog : WideLogData :=
  innerPair352Data

set_option maxRecDepth 1000000 in
private theorem leaf6103LocalValidity :
    LeafFacts leaf6103Box leaf6103Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6103Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712180736) }) = true
      norm_num [leaf6103Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6103CertificateValid :
    WideCertificateValid leaf6103Box leaf6103Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi267ValidityFacts
    leaf6103LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6103CoverageChecked :
    coverageCheck (innerAD leaf6103Box) leaf6103InnerLog = true := by
  rfl'

private theorem leaf6103InnerLogValid :
    leaf6103InnerLog.Valid 8 (innerAD leaf6103Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint93PositiveFacts.valid leaf6103CoverageChecked

private noncomputable def leaf6103InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629595/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6103InputLogOnePlusV_eq :
    leaf6103InputLogOnePlusV = outerEnclosure 24
      (leaf6103Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6103RoundedFacts : LeafRoundedFacts 8
    leaf6103Certificate.logOnePlusV leaf6103InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6103InputLogOnePlusV_eq }

private noncomputable def leaf6103Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi267InputQChi innerPair352Input
    leaf6103InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6103LowerChecked :
    lowerCheck 24 leaf6103Box leaf6103Inputs = true := by
  rfl'

private theorem leaf6103CoversExact : CoversExact 8
    leaf6103Box leaf6103Certificate leaf6103InnerLog leaf6103Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi267RoundedFacts
    innerPair352RoundedFacts leaf6103RoundedFacts (by rfl)

private theorem leaf6103FlatSound : Sound leaf6103Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6103CertificateValid
    leaf6103InnerLogValid leaf6103CoversExact leaf6103LowerChecked

private noncomputable def leaf6104Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (7/16), chiHi := (57/128) }

private noncomputable def leaf6104Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435821/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712122368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (727126325/536870912) }, upper := { exponent := 1, mantissa := (5639/4096) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi267LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428518909/137424244736) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf6104InnerLog : WideLogData :=
  innerPair729Data

set_option maxRecDepth 1000000 in
private theorem leaf6104LocalValidity :
    LeafFacts leaf6104Box leaf6104Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6104Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712122368) }) = true
      norm_num [leaf6104Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6104CertificateValid :
    WideCertificateValid leaf6104Box leaf6104Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi267ValidityFacts
    leaf6104LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6104CoverageChecked :
    coverageCheck (innerAD leaf6104Box) leaf6104InnerLog = true := by
  rfl'

private theorem leaf6104InnerLogValid :
    leaf6104InnerLog.Valid 8 (innerAD leaf6104Box) :=
  wideLogDataValid_of_cachedCheck endpoint465PositiveFacts
    endpoint466PositiveFacts.valid leaf6104CoverageChecked

private noncomputable def leaf6104InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629603/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6104InputLogOnePlusV_eq :
    leaf6104InputLogOnePlusV = outerEnclosure 24
      (leaf6104Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6104RoundedFacts : LeafRoundedFacts 8
    leaf6104Certificate.logOnePlusV leaf6104InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6104InputLogOnePlusV_eq }

private noncomputable def leaf6104Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi267InputQChi innerPair729Input
    leaf6104InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6104LowerChecked :
    lowerCheck 24 leaf6104Box leaf6104Inputs = true := by
  rfl'

private theorem leaf6104CoversExact : CoversExact 8
    leaf6104Box leaf6104Certificate leaf6104InnerLog leaf6104Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi267RoundedFacts
    innerPair729RoundedFacts leaf6104RoundedFacts (by rfl)

private theorem leaf6104FlatSound : Sound leaf6104Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6104CertificateValid
    leaf6104InnerLogValid leaf6104CoversExact leaf6104LowerChecked

private noncomputable def leaf6105Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (57/128), chiHi := (29/64) }

private noncomputable def leaf6105Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435821/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712052736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (731582501/536870912) }, upper := { exponent := 1, mantissa := (5673/4096) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi268LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428449277/137424105472) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf6105InnerLog : WideLogData :=
  innerPair720Data

set_option maxRecDepth 1000000 in
private theorem leaf6105LocalValidity :
    LeafFacts leaf6105Box leaf6105Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6105Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712052736) }) = true
      norm_num [leaf6105Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6105CertificateValid :
    WideCertificateValid leaf6105Box leaf6105Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi268ValidityFacts
    leaf6105LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6105CoverageChecked :
    coverageCheck (innerAD leaf6105Box) leaf6105InnerLog = true := by
  rfl'

private theorem leaf6105InnerLogValid :
    leaf6105InnerLog.Valid 8 (innerAD leaf6105Box) :=
  wideLogDataValid_of_cachedCheck endpoint461PositiveFacts
    endpoint463PositiveFacts.valid leaf6105CoverageChecked

private noncomputable def leaf6105InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629611/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6105InputLogOnePlusV_eq :
    leaf6105InputLogOnePlusV = outerEnclosure 24
      (leaf6105Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6105RoundedFacts : LeafRoundedFacts 8
    leaf6105Certificate.logOnePlusV leaf6105InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6105InputLogOnePlusV_eq }

private noncomputable def leaf6105Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi268InputQChi innerPair720Input
    leaf6105InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6105LowerChecked :
    lowerCheck 24 leaf6105Box leaf6105Inputs = true := by
  rfl'

private theorem leaf6105CoversExact : CoversExact 8
    leaf6105Box leaf6105Certificate leaf6105InnerLog leaf6105Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi268RoundedFacts
    innerPair720RoundedFacts leaf6105RoundedFacts (by rfl)

private theorem leaf6105FlatSound : Sound leaf6105Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6105CertificateValid
    leaf6105InnerLogValid leaf6105CoversExact leaf6105LowerChecked

private noncomputable def leaf6106Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (57/128), chiHi := (29/64) }

private noncomputable def leaf6106Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435823/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711993344) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (735317823/536870912) }, upper := { exponent := 1, mantissa := (2851/2048) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi268LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428389885/137423986688) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf6106InnerLog : WideLogData :=
  innerPair723Data

set_option maxRecDepth 1000000 in
private theorem leaf6106LocalValidity :
    LeafFacts leaf6106Box leaf6106Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6106Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711993344) }) = true
      norm_num [leaf6106Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6106CertificateValid :
    WideCertificateValid leaf6106Box leaf6106Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi268ValidityFacts
    leaf6106LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6106CoverageChecked :
    coverageCheck (innerAD leaf6106Box) leaf6106InnerLog = true := by
  rfl'

private theorem leaf6106InnerLogValid :
    leaf6106InnerLog.Valid 8 (innerAD leaf6106Box) :=
  wideLogDataValid_of_cachedCheck endpoint462PositiveFacts
    endpoint467PositiveFacts.valid leaf6106CoverageChecked

private noncomputable def leaf6106InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814809/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6106InputLogOnePlusV_eq :
    leaf6106InputLogOnePlusV = outerEnclosure 24
      (leaf6106Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6106RoundedFacts : LeafRoundedFacts 8
    leaf6106Certificate.logOnePlusV leaf6106InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6106InputLogOnePlusV_eq }

private noncomputable def leaf6106Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi268InputQChi innerPair723Input
    leaf6106InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6106LowerChecked :
    lowerCheck 24 leaf6106Box leaf6106Inputs = true := by
  rfl'

private theorem leaf6106CoversExact : CoversExact 8
    leaf6106Box leaf6106Certificate leaf6106InnerLog leaf6106Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi268RoundedFacts
    innerPair723RoundedFacts leaf6106RoundedFacts (by rfl)

private theorem leaf6106FlatSound : Sound leaf6106Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6106CertificateValid
    leaf6106InnerLogValid leaf6106CoversExact leaf6106LowerChecked

private noncomputable def leaf6107Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (7/16), chiHi := (57/128) }

private noncomputable def leaf6107Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435823/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712064000) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (730796115/536870912) }, upper := { exponent := 1, mantissa := (11335/8192) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi267LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428460541/137424128000) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf6107InnerLog : WideLogData :=
  innerPair721Data

set_option maxRecDepth 1000000 in
private theorem leaf6107LocalValidity :
    LeafFacts leaf6107Box leaf6107Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6107Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712064000) }) = true
      norm_num [leaf6107Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6107CertificateValid :
    WideCertificateValid leaf6107Box leaf6107Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi267ValidityFacts
    leaf6107LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6107CoverageChecked :
    coverageCheck (innerAD leaf6107Box) leaf6107InnerLog = true := by
  rfl'

private theorem leaf6107InnerLogValid :
    leaf6107InnerLog.Valid 8 (innerAD leaf6107Box) :=
  wideLogDataValid_of_cachedCheck endpoint461PositiveFacts
    endpoint468PositiveFacts.valid leaf6107CoverageChecked

private noncomputable def leaf6107InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814805/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6107InputLogOnePlusV_eq :
    leaf6107InputLogOnePlusV = outerEnclosure 24
      (leaf6107Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6107RoundedFacts : LeafRoundedFacts 8
    leaf6107Certificate.logOnePlusV leaf6107InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6107InputLogOnePlusV_eq }

private noncomputable def leaf6107Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi267InputQChi innerPair721Input
    leaf6107InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6107LowerChecked :
    lowerCheck 24 leaf6107Box leaf6107Inputs = true := by
  rfl'

private theorem leaf6107CoversExact : CoversExact 8
    leaf6107Box leaf6107Certificate leaf6107InnerLog leaf6107Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi267RoundedFacts
    innerPair721RoundedFacts leaf6107RoundedFacts (by rfl)

private theorem leaf6107FlatSound : Sound leaf6107Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6107CertificateValid
    leaf6107InnerLogValid leaf6107CoversExact leaf6107LowerChecked

private noncomputable def leaf6108Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (7/16), chiHi := (57/128) }

private noncomputable def leaf6108Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435825/268435456) }, vSqrt := { lower := (65527/65536), upper := (68716396541/68712005632) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (734465905/536870912) }, upper := { exponent := 1, mantissa := (89/64) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi267LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (137428402173/137424011264) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf6108InnerLog : WideLogData :=
  innerPair722Data

set_option maxRecDepth 1000000 in
private theorem leaf6108LocalValidity :
    LeafFacts leaf6108Box leaf6108Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6108Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (68716396541/68712005632) }) = true
      norm_num [leaf6108Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6108CertificateValid :
    WideCertificateValid leaf6108Box leaf6108Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi267ValidityFacts
    leaf6108LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6108CoverageChecked :
    coverageCheck (innerAD leaf6108Box) leaf6108InnerLog = true := by
  rfl'

private theorem leaf6108InnerLogValid :
    leaf6108InnerLog.Valid 8 (innerAD leaf6108Box) :=
  wideLogDataValid_of_cachedCheck endpoint462PositiveFacts
    endpoint463PositiveFacts.valid leaf6108CoverageChecked

private noncomputable def leaf6108InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629617/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6108InputLogOnePlusV_eq :
    leaf6108InputLogOnePlusV = outerEnclosure 24
      (leaf6108Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6108RoundedFacts : LeafRoundedFacts 8
    leaf6108Certificate.logOnePlusV leaf6108InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6108InputLogOnePlusV_eq }

private noncomputable def leaf6108Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi267InputQChi innerPair722Input
    leaf6108InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6108LowerChecked :
    lowerCheck 24 leaf6108Box leaf6108Inputs = true := by
  rfl'

private theorem leaf6108CoversExact : CoversExact 8
    leaf6108Box leaf6108Certificate leaf6108InnerLog leaf6108Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi267RoundedFacts
    innerPair722RoundedFacts leaf6108RoundedFacts (by rfl)

private theorem leaf6108FlatSound : Sound leaf6108Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6108CertificateValid
    leaf6108InnerLogValid leaf6108CoversExact leaf6108LowerChecked

private noncomputable def leaf6109Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (57/128), chiHi := (29/64) }

private noncomputable def leaf6109Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435825/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711933952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (739053145/536870912) }, upper := { exponent := 1, mantissa := (5731/4096) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi268LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428330493/137423867904) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf6109InnerLog : WideLogData :=
  innerPair356Data

set_option maxRecDepth 1000000 in
private theorem leaf6109LocalValidity :
    LeafFacts leaf6109Box leaf6109Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6109Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711933952) }) = true
      norm_num [leaf6109Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6109CertificateValid :
    WideCertificateValid leaf6109Box leaf6109Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi268ValidityFacts
    leaf6109LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6109CoverageChecked :
    coverageCheck (innerAD leaf6109Box) leaf6109InnerLog = true := by
  rfl'

private theorem leaf6109InnerLogValid :
    leaf6109InnerLog.Valid 8 (innerAD leaf6109Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint96PositiveFacts.valid leaf6109CoverageChecked

private noncomputable def leaf6109InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814813/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6109InputLogOnePlusV_eq :
    leaf6109InputLogOnePlusV = outerEnclosure 24
      (leaf6109Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6109RoundedFacts : LeafRoundedFacts 8
    leaf6109Certificate.logOnePlusV leaf6109InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6109InputLogOnePlusV_eq }

private noncomputable def leaf6109Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi268InputQChi innerPair356Input
    leaf6109InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6109LowerChecked :
    lowerCheck 24 leaf6109Box leaf6109Inputs = true := by
  rfl'

private theorem leaf6109CoversExact : CoversExact 8
    leaf6109Box leaf6109Certificate leaf6109InnerLog leaf6109Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi268RoundedFacts
    innerPair356RoundedFacts leaf6109RoundedFacts (by rfl)

private theorem leaf6109FlatSound : Sound leaf6109Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6109CertificateValid
    leaf6109InnerLogValid leaf6109CoversExact leaf6109LowerChecked

private noncomputable def leaf6110Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (57/128), chiHi := (29/64) }

private noncomputable def leaf6110Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435827/268435456) }, vSqrt := { lower := (65527/65536), upper := (68716396541/68711874560) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (742788467/536870912) }, upper := { exponent := 1, mantissa := (45/32) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi268LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (137428271101/137423749120) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf6110InnerLog : WideLogData :=
  innerPair356Data

set_option maxRecDepth 1000000 in
private theorem leaf6110LocalValidity :
    LeafFacts leaf6110Box leaf6110Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6110Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (68716396541/68711874560) }) = true
      norm_num [leaf6110Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6110CertificateValid :
    WideCertificateValid leaf6110Box leaf6110Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi268ValidityFacts
    leaf6110LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6110CoverageChecked :
    coverageCheck (innerAD leaf6110Box) leaf6110InnerLog = true := by
  rfl'

private theorem leaf6110InnerLogValid :
    leaf6110InnerLog.Valid 8 (innerAD leaf6110Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint96PositiveFacts.valid leaf6110CoverageChecked

private noncomputable def leaf6110InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629633/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6110InputLogOnePlusV_eq :
    leaf6110InputLogOnePlusV = outerEnclosure 24
      (leaf6110Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6110RoundedFacts : LeafRoundedFacts 8
    leaf6110Certificate.logOnePlusV leaf6110InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6110InputLogOnePlusV_eq }

private noncomputable def leaf6110Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi268InputQChi innerPair356Input
    leaf6110InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6110LowerChecked :
    lowerCheck 24 leaf6110Box leaf6110Inputs = true := by
  rfl'

private theorem leaf6110CoversExact : CoversExact 8
    leaf6110Box leaf6110Certificate leaf6110InnerLog leaf6110Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi268RoundedFacts
    innerPair356RoundedFacts leaf6110RoundedFacts (by rfl)

private theorem leaf6110FlatSound : Sound leaf6110Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6110CertificateValid
    leaf6110InnerLogValid leaf6110CoversExact leaf6110LowerChecked

private noncomputable def leaf6111Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (29/64), chiHi := (59/128) }

private noncomputable def leaf6111Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435823/268435456) }, vSqrt := { lower := (8191/8192), upper := (5285876657/5285532672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (739708467/536870912) }, upper := { exponent := 1, mantissa := (11471/8192) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi269LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (10571409329/10571065344) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf6111InnerLog : WideLogData :=
  innerPair356Data

set_option maxRecDepth 1000000 in
private theorem leaf6111LocalValidity :
    LeafFacts leaf6111Box leaf6111Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6111Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5285876657/5285532672) }) = true
      norm_num [leaf6111Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6111CertificateValid :
    WideCertificateValid leaf6111Box leaf6111Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi269ValidityFacts
    leaf6111LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6111CoverageChecked :
    coverageCheck (innerAD leaf6111Box) leaf6111InnerLog = true := by
  rfl'

private theorem leaf6111InnerLogValid :
    leaf6111InnerLog.Valid 8 (innerAD leaf6111Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint96PositiveFacts.valid leaf6111CoverageChecked

private noncomputable def leaf6111InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629627/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6111InputLogOnePlusV_eq :
    leaf6111InputLogOnePlusV = outerEnclosure 24
      (leaf6111Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6111RoundedFacts : LeafRoundedFacts 8
    leaf6111Certificate.logOnePlusV leaf6111InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6111InputLogOnePlusV_eq }

private noncomputable def leaf6111Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi269InputQChi innerPair356Input
    leaf6111InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6111LowerChecked :
    lowerCheck 24 leaf6111Box leaf6111Inputs = true := by
  rfl'

private theorem leaf6111CoversExact : CoversExact 8
    leaf6111Box leaf6111Certificate leaf6111InnerLog leaf6111Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi269RoundedFacts
    innerPair356RoundedFacts leaf6111RoundedFacts (by rfl)

private theorem leaf6111FlatSound : Sound leaf6111Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6111CertificateValid
    leaf6111InnerLogValid leaf6111CoversExact leaf6111LowerChecked

private noncomputable def leaf6112Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (29/64), chiHi := (59/128) }

private noncomputable def leaf6112Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435825/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711864320) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (743509321/536870912) }, upper := { exponent := 1, mantissa := (5765/4096) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi269LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428260861/137423728640) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf6112InnerLog : WideLogData :=
  innerPair718Data

set_option maxRecDepth 1000000 in
private theorem leaf6112LocalValidity :
    LeafFacts leaf6112Box leaf6112Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6112Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711864320) }) = true
      norm_num [leaf6112Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6112CertificateValid :
    WideCertificateValid leaf6112Box leaf6112Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi269ValidityFacts
    leaf6112LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6112CoverageChecked :
    coverageCheck (innerAD leaf6112Box) leaf6112InnerLog = true := by
  rfl'

private theorem leaf6112InnerLogValid :
    leaf6112InnerLog.Valid 8 (innerAD leaf6112Box) :=
  wideLogDataValid_of_cachedCheck endpoint460PositiveFacts
    endpoint464PositiveFacts.valid leaf6112CoverageChecked

private noncomputable def leaf6112InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814817/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6112InputLogOnePlusV_eq :
    leaf6112InputLogOnePlusV = outerEnclosure 24
      (leaf6112Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6112RoundedFacts : LeafRoundedFacts 8
    leaf6112Certificate.logOnePlusV leaf6112InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6112InputLogOnePlusV_eq }

private noncomputable def leaf6112Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi269InputQChi innerPair718Input
    leaf6112InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6112LowerChecked :
    lowerCheck 24 leaf6112Box leaf6112Inputs = true := by
  rfl'

private theorem leaf6112CoversExact : CoversExact 8
    leaf6112Box leaf6112Certificate leaf6112InnerLog leaf6112Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi269RoundedFacts
    innerPair718RoundedFacts leaf6112RoundedFacts (by rfl)

private theorem leaf6112FlatSound : Sound leaf6112Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6112CertificateValid
    leaf6112InnerLogValid leaf6112CoversExact leaf6112LowerChecked

private noncomputable def leaf6113Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (59/128), chiHi := (15/32) }

private noncomputable def leaf6113Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435825/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711796736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (747834433/536870912) }, upper := { exponent := 1, mantissa := (2899/2048) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi270LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428193277/137423593472) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf6113InnerLog : WideLogData :=
  innerPair724Data

set_option maxRecDepth 1000000 in
private theorem leaf6113LocalValidity :
    LeafFacts leaf6113Box leaf6113Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6113Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711796736) }) = true
      norm_num [leaf6113Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6113CertificateValid :
    WideCertificateValid leaf6113Box leaf6113Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi270ValidityFacts
    leaf6113LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6113CoverageChecked :
    coverageCheck (innerAD leaf6113Box) leaf6113InnerLog = true := by
  rfl'

private theorem leaf6113InnerLogValid :
    leaf6113InnerLog.Valid 8 (innerAD leaf6113Box) :=
  wideLogDataValid_of_cachedCheck endpoint463PositiveFacts
    endpoint469PositiveFacts.valid leaf6113CoverageChecked

private noncomputable def leaf6113InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814821/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6113InputLogOnePlusV_eq :
    leaf6113InputLogOnePlusV = outerEnclosure 24
      (leaf6113Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6113RoundedFacts : LeafRoundedFacts 8
    leaf6113Certificate.logOnePlusV leaf6113InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6113InputLogOnePlusV_eq }

private noncomputable def leaf6113Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi270InputQChi innerPair724Input
    leaf6113InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6113LowerChecked :
    lowerCheck 24 leaf6113Box leaf6113Inputs = true := by
  rfl'

private theorem leaf6113CoversExact : CoversExact 8
    leaf6113Box leaf6113Certificate leaf6113InnerLog leaf6113Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi270RoundedFacts
    innerPair724RoundedFacts leaf6113RoundedFacts (by rfl)

private theorem leaf6113FlatSound : Sound leaf6113Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6113CertificateValid
    leaf6113InnerLogValid leaf6113CoversExact leaf6113LowerChecked

private noncomputable def leaf6114Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (59/128), chiHi := (15/32) }

private noncomputable def leaf6114Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435827/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711735296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (751700819/536870912) }, upper := { exponent := 1, mantissa := (1457/1024) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi270LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428131837/137423470592) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf6114InnerLog : WideLogData :=
  innerPair357Data

set_option maxRecDepth 1000000 in
private theorem leaf6114LocalValidity :
    LeafFacts leaf6114Box leaf6114Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6114Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711735296) }) = true
      norm_num [leaf6114Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6114CertificateValid :
    WideCertificateValid leaf6114Box leaf6114Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi270ValidityFacts
    leaf6114LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6114CoverageChecked :
    coverageCheck (innerAD leaf6114Box) leaf6114InnerLog = true := by
  rfl'

private theorem leaf6114InnerLogValid :
    leaf6114InnerLog.Valid 8 (innerAD leaf6114Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint97PositiveFacts.valid leaf6114CoverageChecked

private noncomputable def leaf6114InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814825/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6114InputLogOnePlusV_eq :
    leaf6114InputLogOnePlusV = outerEnclosure 24
      (leaf6114Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6114RoundedFacts : LeafRoundedFacts 8
    leaf6114Certificate.logOnePlusV leaf6114InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6114InputLogOnePlusV_eq }

private noncomputable def leaf6114Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi270InputQChi innerPair357Input
    leaf6114InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6114LowerChecked :
    lowerCheck 24 leaf6114Box leaf6114Inputs = true := by
  rfl'

private theorem leaf6114CoversExact : CoversExact 8
    leaf6114Box leaf6114Certificate leaf6114InnerLog leaf6114Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi270RoundedFacts
    innerPair357RoundedFacts leaf6114RoundedFacts (by rfl)

private theorem leaf6114FlatSound : Sound leaf6114Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6114CertificateValid
    leaf6114InnerLogValid leaf6114CoversExact leaf6114LowerChecked

private noncomputable def leaf6115Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (29/64), chiHi := (59/128) }

private noncomputable def leaf6115Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435827/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711803904) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (747310175/536870912) }, upper := { exponent := 1, mantissa := (11589/8192) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi269LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428200445/137423607808) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf6115InnerLog : WideLogData :=
  innerPair724Data

set_option maxRecDepth 1000000 in
private theorem leaf6115LocalValidity :
    LeafFacts leaf6115Box leaf6115Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6115Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711803904) }) = true
      norm_num [leaf6115Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6115CertificateValid :
    WideCertificateValid leaf6115Box leaf6115Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi269ValidityFacts
    leaf6115LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6115CoverageChecked :
    coverageCheck (innerAD leaf6115Box) leaf6115InnerLog = true := by
  rfl'

private theorem leaf6115InnerLogValid :
    leaf6115InnerLog.Valid 8 (innerAD leaf6115Box) :=
  wideLogDataValid_of_cachedCheck endpoint463PositiveFacts
    endpoint469PositiveFacts.valid leaf6115CoverageChecked

private noncomputable def leaf6115InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629641/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6115InputLogOnePlusV_eq :
    leaf6115InputLogOnePlusV = outerEnclosure 24
      (leaf6115Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6115RoundedFacts : LeafRoundedFacts 8
    leaf6115Certificate.logOnePlusV leaf6115InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6115InputLogOnePlusV_eq }

private noncomputable def leaf6115Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi269InputQChi innerPair724Input
    leaf6115InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6115LowerChecked :
    lowerCheck 24 leaf6115Box leaf6115Inputs = true := by
  rfl'

private theorem leaf6115CoversExact : CoversExact 8
    leaf6115Box leaf6115Certificate leaf6115InnerLog leaf6115Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi269RoundedFacts
    innerPair724RoundedFacts leaf6115RoundedFacts (by rfl)

private theorem leaf6115FlatSound : Sound leaf6115Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6115CertificateValid
    leaf6115InnerLogValid leaf6115CoversExact leaf6115LowerChecked

private noncomputable def leaf6116Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (29/64), chiHi := (59/128) }

private noncomputable def leaf6116Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435829/268435456) }, vSqrt := { lower := (65527/65536), upper := (4042140973/4041867264) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (751111029/536870912) }, upper := { exponent := 1, mantissa := (91/64) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi269LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (8084008237/8083734528) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf6116InnerLog : WideLogData :=
  innerPair730Data

set_option maxRecDepth 1000000 in
private theorem leaf6116LocalValidity :
    LeafFacts leaf6116Box leaf6116Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6116Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (4042140973/4041867264) }) = true
      norm_num [leaf6116Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6116CertificateValid :
    WideCertificateValid leaf6116Box leaf6116Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi269ValidityFacts
    leaf6116LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6116CoverageChecked :
    coverageCheck (innerAD leaf6116Box) leaf6116InnerLog = true := by
  rfl'

private theorem leaf6116InnerLogValid :
    leaf6116InnerLog.Valid 8 (innerAD leaf6116Box) :=
  wideLogDataValid_of_cachedCheck endpoint467PositiveFacts
    endpoint469PositiveFacts.valid leaf6116CoverageChecked

private noncomputable def leaf6116InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629649/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6116InputLogOnePlusV_eq :
    leaf6116InputLogOnePlusV = outerEnclosure 24
      (leaf6116Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6116RoundedFacts : LeafRoundedFacts 8
    leaf6116Certificate.logOnePlusV leaf6116InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6116InputLogOnePlusV_eq }

private noncomputable def leaf6116Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi269InputQChi innerPair730Input
    leaf6116InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6116LowerChecked :
    lowerCheck 24 leaf6116Box leaf6116Inputs = true := by
  rfl'

private theorem leaf6116CoversExact : CoversExact 8
    leaf6116Box leaf6116Certificate leaf6116InnerLog leaf6116Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi269RoundedFacts
    innerPair730RoundedFacts leaf6116RoundedFacts (by rfl)

private theorem leaf6116FlatSound : Sound leaf6116Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6116CertificateValid
    leaf6116InnerLogValid leaf6116CoversExact leaf6116LowerChecked

private noncomputable def leaf6117Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (59/128), chiHi := (15/32) }

private noncomputable def leaf6117Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435829/268435456) }, vSqrt := { lower := (8191/8192), upper := (4042140973/4041863168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (755567205/536870912) }, upper := { exponent := 1, mantissa := (2929/2048) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi270LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (8084004141/8083726336) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf6117InnerLog : WideLogData :=
  innerPair367Data

set_option maxRecDepth 1000000 in
private theorem leaf6117LocalValidity :
    LeafFacts leaf6117Box leaf6117Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6117Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4042140973/4041863168) }) = true
      norm_num [leaf6117Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6117CertificateValid :
    WideCertificateValid leaf6117Box leaf6117Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi270ValidityFacts
    leaf6117LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6117CoverageChecked :
    coverageCheck (innerAD leaf6117Box) leaf6117InnerLog = true := by
  rfl'

private theorem leaf6117InnerLogValid :
    leaf6117InnerLog.Valid 8 (innerAD leaf6117Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint97PositiveFacts.valid leaf6117CoverageChecked

private noncomputable def leaf6117InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629657/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6117InputLogOnePlusV_eq :
    leaf6117InputLogOnePlusV = outerEnclosure 24
      (leaf6117Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6117RoundedFacts : LeafRoundedFacts 8
    leaf6117Certificate.logOnePlusV leaf6117InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6117InputLogOnePlusV_eq }

private noncomputable def leaf6117Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi270InputQChi innerPair367Input
    leaf6117InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6117LowerChecked :
    lowerCheck 24 leaf6117Box leaf6117Inputs = true := by
  rfl'

private theorem leaf6117CoversExact : CoversExact 8
    leaf6117Box leaf6117Certificate leaf6117InnerLog leaf6117Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi270RoundedFacts
    innerPair367RoundedFacts leaf6117RoundedFacts (by rfl)

private theorem leaf6117FlatSound : Sound leaf6117Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6117CertificateValid
    leaf6117InnerLogValid leaf6117CoversExact leaf6117LowerChecked

private noncomputable def leaf6118Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (59/128), chiHi := (15/32) }

private noncomputable def leaf6118Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435831/268435456) }, vSqrt := { lower := (65527/65536), upper := (68716396541/68711612416) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (759433591/536870912) }, upper := { exponent := 1, mantissa := (23/16) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi270LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (137428008957/137423224832) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf6118InnerLog : WideLogData :=
  innerPair367Data

set_option maxRecDepth 1000000 in
private theorem leaf6118LocalValidity :
    LeafFacts leaf6118Box leaf6118Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6118Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (68716396541/68711612416) }) = true
      norm_num [leaf6118Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6118CertificateValid :
    WideCertificateValid leaf6118Box leaf6118Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi270ValidityFacts
    leaf6118LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6118CoverageChecked :
    coverageCheck (innerAD leaf6118Box) leaf6118InnerLog = true := by
  rfl'

private theorem leaf6118InnerLogValid :
    leaf6118InnerLog.Valid 8 (innerAD leaf6118Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint97PositiveFacts.valid leaf6118CoverageChecked

private noncomputable def leaf6118InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629665/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6118InputLogOnePlusV_eq :
    leaf6118InputLogOnePlusV = outerEnclosure 24
      (leaf6118Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6118RoundedFacts : LeafRoundedFacts 8
    leaf6118Certificate.logOnePlusV leaf6118InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6118InputLogOnePlusV_eq }

private noncomputable def leaf6118Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi270InputQChi innerPair367Input
    leaf6118InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6118LowerChecked :
    lowerCheck 24 leaf6118Box leaf6118Inputs = true := by
  rfl'

private theorem leaf6118CoversExact : CoversExact 8
    leaf6118Box leaf6118Certificate leaf6118InnerLog leaf6118Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi270RoundedFacts
    innerPair367RoundedFacts leaf6118RoundedFacts (by rfl)

private theorem leaf6118FlatSound : Sound leaf6118Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6118CertificateValid
    leaf6118InnerLogValid leaf6118CoversExact leaf6118LowerChecked

private noncomputable def leaf6119Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (15/32), chiHi := (61/128) }

private noncomputable def leaf6119Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435819/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711918592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (740232727/536870912) }, upper := { exponent := 1, mantissa := (11477/8192) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi271LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428315133/137423837184) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf6119InnerLog : WideLogData :=
  innerPair356Data

set_option maxRecDepth 1000000 in
private theorem leaf6119LocalValidity :
    LeafFacts leaf6119Box leaf6119Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6119Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711918592) }) = true
      norm_num [leaf6119Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6119CertificateValid :
    WideCertificateValid leaf6119Box leaf6119Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi271ValidityFacts
    leaf6119LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6119CoverageChecked :
    coverageCheck (innerAD leaf6119Box) leaf6119InnerLog = true := by
  rfl'

private theorem leaf6119InnerLogValid :
    leaf6119InnerLog.Valid 8 (innerAD leaf6119Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint96PositiveFacts.valid leaf6119CoverageChecked

private noncomputable def leaf6119InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629627/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6119InputLogOnePlusV_eq :
    leaf6119InputLogOnePlusV = outerEnclosure 24
      (leaf6119Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6119RoundedFacts : LeafRoundedFacts 8
    leaf6119Certificate.logOnePlusV leaf6119InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6119InputLogOnePlusV_eq }

private noncomputable def leaf6119Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi271InputQChi innerPair356Input
    leaf6119InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6119LowerChecked :
    lowerCheck 24 leaf6119Box leaf6119Inputs = true := by
  rfl'

private theorem leaf6119CoversExact : CoversExact 8
    leaf6119Box leaf6119Certificate leaf6119InnerLog leaf6119Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi271RoundedFacts
    innerPair356RoundedFacts leaf6119RoundedFacts (by rfl)

private theorem leaf6119FlatSound : Sound leaf6119Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6119CertificateValid
    leaf6119InnerLogValid leaf6119CoversExact leaf6119LowerChecked

private noncomputable def leaf6120Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (15/32), chiHi := (61/128) }

private noncomputable def leaf6120Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435821/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711856128) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (744164645/536870912) }, upper := { exponent := 1, mantissa := (5769/4096) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi271LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428252669/137423712256) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf6120InnerLog : WideLogData :=
  innerPair718Data

set_option maxRecDepth 1000000 in
private theorem leaf6120LocalValidity :
    LeafFacts leaf6120Box leaf6120Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6120Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711856128) }) = true
      norm_num [leaf6120Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6120CertificateValid :
    WideCertificateValid leaf6120Box leaf6120Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi271ValidityFacts
    leaf6120LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6120CoverageChecked :
    coverageCheck (innerAD leaf6120Box) leaf6120InnerLog = true := by
  rfl'

private theorem leaf6120InnerLogValid :
    leaf6120InnerLog.Valid 8 (innerAD leaf6120Box) :=
  wideLogDataValid_of_cachedCheck endpoint460PositiveFacts
    endpoint464PositiveFacts.valid leaf6120CoverageChecked

private noncomputable def leaf6120InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629635/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6120InputLogOnePlusV_eq :
    leaf6120InputLogOnePlusV = outerEnclosure 24
      (leaf6120Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6120RoundedFacts : LeafRoundedFacts 8
    leaf6120Certificate.logOnePlusV leaf6120InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6120InputLogOnePlusV_eq }

private noncomputable def leaf6120Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi271InputQChi innerPair718Input
    leaf6120InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6120LowerChecked :
    lowerCheck 24 leaf6120Box leaf6120Inputs = true := by
  rfl'

private theorem leaf6120CoversExact : CoversExact 8
    leaf6120Box leaf6120Certificate leaf6120InnerLog leaf6120Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi271RoundedFacts
    innerPair718RoundedFacts leaf6120RoundedFacts (by rfl)

private theorem leaf6120FlatSound : Sound leaf6120Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6120CertificateValid
    leaf6120InnerLogValid leaf6120CoversExact leaf6120LowerChecked

private noncomputable def leaf6121Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (61/128), chiHi := (31/64) }

private noncomputable def leaf6121Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435821/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711794688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (748096565/536870912) }, upper := { exponent := 1, mantissa := (5799/4096) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi272LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428191229/137423589376) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf6121InnerLog : WideLogData :=
  innerPair357Data

set_option maxRecDepth 1000000 in
private theorem leaf6121LocalValidity :
    LeafFacts leaf6121Box leaf6121Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6121Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711794688) }) = true
      norm_num [leaf6121Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6121CertificateValid :
    WideCertificateValid leaf6121Box leaf6121Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi272ValidityFacts
    leaf6121LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6121CoverageChecked :
    coverageCheck (innerAD leaf6121Box) leaf6121InnerLog = true := by
  rfl'

private theorem leaf6121InnerLogValid :
    leaf6121InnerLog.Valid 8 (innerAD leaf6121Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint97PositiveFacts.valid leaf6121CoverageChecked

private noncomputable def leaf6121InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629643/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6121InputLogOnePlusV_eq :
    leaf6121InputLogOnePlusV = outerEnclosure 24
      (leaf6121Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6121RoundedFacts : LeafRoundedFacts 8
    leaf6121Certificate.logOnePlusV leaf6121InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6121InputLogOnePlusV_eq }

private noncomputable def leaf6121Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi272InputQChi innerPair357Input
    leaf6121InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6121LowerChecked :
    lowerCheck 24 leaf6121Box leaf6121Inputs = true := by
  rfl'

private theorem leaf6121CoversExact : CoversExact 8
    leaf6121Box leaf6121Certificate leaf6121InnerLog leaf6121Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi272RoundedFacts
    innerPair357RoundedFacts leaf6121RoundedFacts (by rfl)

private theorem leaf6121FlatSound : Sound leaf6121Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6121CertificateValid
    leaf6121InnerLogValid leaf6121CoversExact leaf6121LowerChecked

private noncomputable def leaf6122Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (61/128), chiHi := (31/64) }

private noncomputable def leaf6122Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435823/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711731200) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (752094015/536870912) }, upper := { exponent := 1, mantissa := (2915/2048) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi272LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428127741/137423462400) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf6122InnerLog : WideLogData :=
  innerPair357Data

set_option maxRecDepth 1000000 in
private theorem leaf6122LocalValidity :
    LeafFacts leaf6122Box leaf6122Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6122Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711731200) }) = true
      norm_num [leaf6122Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6122CertificateValid :
    WideCertificateValid leaf6122Box leaf6122Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi272ValidityFacts
    leaf6122LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6122CoverageChecked :
    coverageCheck (innerAD leaf6122Box) leaf6122InnerLog = true := by
  rfl'

private theorem leaf6122InnerLogValid :
    leaf6122InnerLog.Valid 8 (innerAD leaf6122Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint97PositiveFacts.valid leaf6122CoverageChecked

private noncomputable def leaf6122InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814825/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6122InputLogOnePlusV_eq :
    leaf6122InputLogOnePlusV = outerEnclosure 24
      (leaf6122Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6122RoundedFacts : LeafRoundedFacts 8
    leaf6122Certificate.logOnePlusV leaf6122InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6122InputLogOnePlusV_eq }

private noncomputable def leaf6122Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi272InputQChi innerPair357Input
    leaf6122InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6122LowerChecked :
    lowerCheck 24 leaf6122Box leaf6122Inputs = true := by
  rfl'

private theorem leaf6122CoversExact : CoversExact 8
    leaf6122Box leaf6122Certificate leaf6122InnerLog leaf6122Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi272RoundedFacts
    innerPair357RoundedFacts leaf6122RoundedFacts (by rfl)

private theorem leaf6122FlatSound : Sound leaf6122Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6122CertificateValid
    leaf6122InnerLogValid leaf6122CoversExact leaf6122LowerChecked

private noncomputable def leaf6123Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (15/32), chiHi := (61/128) }

private noncomputable def leaf6123Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435823/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711793664) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (748096563/536870912) }, upper := { exponent := 1, mantissa := (11599/8192) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi271LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428190205/137423587328) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf6123InnerLog : WideLogData :=
  innerPair357Data

set_option maxRecDepth 1000000 in
private theorem leaf6123LocalValidity :
    LeafFacts leaf6123Box leaf6123Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6123Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711793664) }) = true
      norm_num [leaf6123Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6123CertificateValid :
    WideCertificateValid leaf6123Box leaf6123Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi271ValidityFacts
    leaf6123LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6123CoverageChecked :
    coverageCheck (innerAD leaf6123Box) leaf6123InnerLog = true := by
  rfl'

private theorem leaf6123InnerLogValid :
    leaf6123InnerLog.Valid 8 (innerAD leaf6123Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint97PositiveFacts.valid leaf6123CoverageChecked

private noncomputable def leaf6123InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629643/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6123InputLogOnePlusV_eq :
    leaf6123InputLogOnePlusV = outerEnclosure 24
      (leaf6123Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6123RoundedFacts : LeafRoundedFacts 8
    leaf6123Certificate.logOnePlusV leaf6123InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6123InputLogOnePlusV_eq }

private noncomputable def leaf6123Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi271InputQChi innerPair357Input
    leaf6123InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6123LowerChecked :
    lowerCheck 24 leaf6123Box leaf6123Inputs = true := by
  rfl'

private theorem leaf6123CoversExact : CoversExact 8
    leaf6123Box leaf6123Certificate leaf6123InnerLog leaf6123Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi271RoundedFacts
    innerPair357RoundedFacts leaf6123RoundedFacts (by rfl)

private theorem leaf6123FlatSound : Sound leaf6123Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6123CertificateValid
    leaf6123InnerLogValid leaf6123CoversExact leaf6123LowerChecked

private noncomputable def leaf6124Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (15/32), chiHi := (61/128) }

private noncomputable def leaf6124Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435825/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711731200) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (752028481/536870912) }, upper := { exponent := 1, mantissa := (2915/2048) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi271LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428127741/137423462400) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf6124InnerLog : WideLogData :=
  innerPair357Data

set_option maxRecDepth 1000000 in
private theorem leaf6124LocalValidity :
    LeafFacts leaf6124Box leaf6124Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6124Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711731200) }) = true
      norm_num [leaf6124Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6124CertificateValid :
    WideCertificateValid leaf6124Box leaf6124Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi271ValidityFacts
    leaf6124LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6124CoverageChecked :
    coverageCheck (innerAD leaf6124Box) leaf6124InnerLog = true := by
  rfl'

private theorem leaf6124InnerLogValid :
    leaf6124InnerLog.Valid 8 (innerAD leaf6124Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint97PositiveFacts.valid leaf6124CoverageChecked

private noncomputable def leaf6124InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814825/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6124InputLogOnePlusV_eq :
    leaf6124InputLogOnePlusV = outerEnclosure 24
      (leaf6124Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6124RoundedFacts : LeafRoundedFacts 8
    leaf6124Certificate.logOnePlusV leaf6124InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6124InputLogOnePlusV_eq }

private noncomputable def leaf6124Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi271InputQChi innerPair357Input
    leaf6124InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6124LowerChecked :
    lowerCheck 24 leaf6124Box leaf6124Inputs = true := by
  rfl'

private theorem leaf6124CoversExact : CoversExact 8
    leaf6124Box leaf6124Certificate leaf6124InnerLog leaf6124Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi271RoundedFacts
    innerPair357RoundedFacts leaf6124RoundedFacts (by rfl)

private theorem leaf6124FlatSound : Sound leaf6124Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6124CertificateValid
    leaf6124InnerLogValid leaf6124CoversExact leaf6124LowerChecked

private noncomputable def leaf6125Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (61/128), chiHi := (31/64) }

private noncomputable def leaf6125Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435825/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711667712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (756091465/536870912) }, upper := { exponent := 1, mantissa := (5861/4096) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi272LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428064253/137423335424) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf6125InnerLog : WideLogData :=
  innerPair367Data

set_option maxRecDepth 1000000 in
private theorem leaf6125LocalValidity :
    LeafFacts leaf6125Box leaf6125Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6125Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711667712) }) = true
      norm_num [leaf6125Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6125CertificateValid :
    WideCertificateValid leaf6125Box leaf6125Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi272ValidityFacts
    leaf6125LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6125CoverageChecked :
    coverageCheck (innerAD leaf6125Box) leaf6125InnerLog = true := by
  rfl'

private theorem leaf6125InnerLogValid :
    leaf6125InnerLog.Valid 8 (innerAD leaf6125Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint97PositiveFacts.valid leaf6125CoverageChecked

private noncomputable def leaf6125InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814829/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6125InputLogOnePlusV_eq :
    leaf6125InputLogOnePlusV = outerEnclosure 24
      (leaf6125Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6125RoundedFacts : LeafRoundedFacts 8
    leaf6125Certificate.logOnePlusV leaf6125InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6125InputLogOnePlusV_eq }

private noncomputable def leaf6125Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi272InputQChi innerPair367Input
    leaf6125InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6125LowerChecked :
    lowerCheck 24 leaf6125Box leaf6125Inputs = true := by
  rfl'

private theorem leaf6125CoversExact : CoversExact 8
    leaf6125Box leaf6125Certificate leaf6125InnerLog leaf6125Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi272RoundedFacts
    innerPair367RoundedFacts leaf6125RoundedFacts (by rfl)

private theorem leaf6125FlatSound : Sound leaf6125Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6125CertificateValid
    leaf6125InnerLogValid leaf6125CoversExact leaf6125LowerChecked

private noncomputable def leaf6126Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (61/128), chiHi := (31/64) }

private noncomputable def leaf6126Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435827/268435456) }, vSqrt := { lower := (8191/8192), upper := (4042140973/4041859072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (760088915/536870912) }, upper := { exponent := 1, mantissa := (1473/1024) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi272LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (8084000045/8083718144) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf6126InnerLog : WideLogData :=
  innerPair726Data

set_option maxRecDepth 1000000 in
private theorem leaf6126LocalValidity :
    LeafFacts leaf6126Box leaf6126Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6126Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4042140973/4041859072) }) = true
      norm_num [leaf6126Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6126CertificateValid :
    WideCertificateValid leaf6126Box leaf6126Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi272ValidityFacts
    leaf6126LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6126CoverageChecked :
    coverageCheck (innerAD leaf6126Box) leaf6126InnerLog = true := by
  rfl'

private theorem leaf6126InnerLogValid :
    leaf6126InnerLog.Valid 8 (innerAD leaf6126Box) :=
  wideLogDataValid_of_cachedCheck endpoint464PositiveFacts
    endpoint470PositiveFacts.valid leaf6126CoverageChecked

private noncomputable def leaf6126InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814833/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6126InputLogOnePlusV_eq :
    leaf6126InputLogOnePlusV = outerEnclosure 24
      (leaf6126Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6126RoundedFacts : LeafRoundedFacts 8
    leaf6126Certificate.logOnePlusV leaf6126InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6126InputLogOnePlusV_eq }

private noncomputable def leaf6126Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi272InputQChi innerPair726Input
    leaf6126InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6126LowerChecked :
    lowerCheck 24 leaf6126Box leaf6126Inputs = true := by
  rfl'

private theorem leaf6126CoversExact : CoversExact 8
    leaf6126Box leaf6126Certificate leaf6126InnerLog leaf6126Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi272RoundedFacts
    innerPair726RoundedFacts leaf6126RoundedFacts (by rfl)

private theorem leaf6126FlatSound : Sound leaf6126Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6126CertificateValid
    leaf6126InnerLogValid leaf6126CoversExact leaf6126LowerChecked

private noncomputable def leaf6127Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (31/64), chiHi := (63/128) }

private noncomputable def leaf6127Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435823/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711670784) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (755960403/536870912) }, upper := { exponent := 1, mantissa := (11719/8192) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi273LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428067325/137423341568) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf6127InnerLog : WideLogData :=
  innerPair367Data

set_option maxRecDepth 1000000 in
private theorem leaf6127LocalValidity :
    LeafFacts leaf6127Box leaf6127Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6127Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711670784) }) = true
      norm_num [leaf6127Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6127CertificateValid :
    WideCertificateValid leaf6127Box leaf6127Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi273ValidityFacts
    leaf6127LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6127CoverageChecked :
    coverageCheck (innerAD leaf6127Box) leaf6127InnerLog = true := by
  rfl'

private theorem leaf6127InnerLogValid :
    leaf6127InnerLog.Valid 8 (innerAD leaf6127Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint97PositiveFacts.valid leaf6127CoverageChecked

private noncomputable def leaf6127InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814829/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6127InputLogOnePlusV_eq :
    leaf6127InputLogOnePlusV = outerEnclosure 24
      (leaf6127Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6127RoundedFacts : LeafRoundedFacts 8
    leaf6127Certificate.logOnePlusV leaf6127InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6127InputLogOnePlusV_eq }

private noncomputable def leaf6127Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi273InputQChi innerPair367Input
    leaf6127InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6127LowerChecked :
    lowerCheck 24 leaf6127Box leaf6127Inputs = true := by
  rfl'

private theorem leaf6127CoversExact : CoversExact 8
    leaf6127Box leaf6127Certificate leaf6127InnerLog leaf6127Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi273RoundedFacts
    innerPair367RoundedFacts leaf6127RoundedFacts (by rfl)

private theorem leaf6127FlatSound : Sound leaf6127Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6127CertificateValid
    leaf6127InnerLogValid leaf6127CoversExact leaf6127LowerChecked

private noncomputable def leaf6128Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (31/64), chiHi := (63/128) }

private noncomputable def leaf6128Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435825/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711606272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (760023385/536870912) }, upper := { exponent := 1, mantissa := (5891/4096) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi273LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428002813/137423212544) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf6128InnerLog : WideLogData :=
  innerPair368Data

set_option maxRecDepth 1000000 in
private theorem leaf6128LocalValidity :
    LeafFacts leaf6128Box leaf6128Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6128Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711606272) }) = true
      norm_num [leaf6128Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6128CertificateValid :
    WideCertificateValid leaf6128Box leaf6128Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi273ValidityFacts
    leaf6128LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6128CoverageChecked :
    coverageCheck (innerAD leaf6128Box) leaf6128InnerLog = true := by
  rfl'

private theorem leaf6128InnerLogValid :
    leaf6128InnerLog.Valid 8 (innerAD leaf6128Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint98PositiveFacts.valid leaf6128CoverageChecked

private noncomputable def leaf6128InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814833/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6128InputLogOnePlusV_eq :
    leaf6128InputLogOnePlusV = outerEnclosure 24
      (leaf6128Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6128RoundedFacts : LeafRoundedFacts 8
    leaf6128Certificate.logOnePlusV leaf6128InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6128InputLogOnePlusV_eq }

private noncomputable def leaf6128Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi273InputQChi innerPair368Input
    leaf6128InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6128LowerChecked :
    lowerCheck 24 leaf6128Box leaf6128Inputs = true := by
  rfl'

private theorem leaf6128CoversExact : CoversExact 8
    leaf6128Box leaf6128Certificate leaf6128InnerLog leaf6128Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi273RoundedFacts
    innerPair368RoundedFacts leaf6128RoundedFacts (by rfl)

private theorem leaf6128FlatSound : Sound leaf6128Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6128CertificateValid
    leaf6128InnerLogValid leaf6128CoversExact leaf6128LowerChecked

private noncomputable def leaf6129Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (63/128), chiHi := (1/2) }

private noncomputable def leaf6129Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435825/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711546880) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (763824241/536870912) }, upper := { exponent := 1, mantissa := (185/128) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi274LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137427943421/137423093760) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf6129InnerLog : WideLogData :=
  innerPair368Data

set_option maxRecDepth 1000000 in
private theorem leaf6129LocalValidity :
    LeafFacts leaf6129Box leaf6129Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6129Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711546880) }) = true
      norm_num [leaf6129Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6129CertificateValid :
    WideCertificateValid leaf6129Box leaf6129Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi274ValidityFacts
    leaf6129LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6129CoverageChecked :
    coverageCheck (innerAD leaf6129Box) leaf6129InnerLog = true := by
  rfl'

private theorem leaf6129InnerLogValid :
    leaf6129InnerLog.Valid 8 (innerAD leaf6129Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint98PositiveFacts.valid leaf6129CoverageChecked

private noncomputable def leaf6129InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629673/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6129InputLogOnePlusV_eq :
    leaf6129InputLogOnePlusV = outerEnclosure 24
      (leaf6129Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6129RoundedFacts : LeafRoundedFacts 8
    leaf6129Certificate.logOnePlusV leaf6129InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6129InputLogOnePlusV_eq }

private noncomputable def leaf6129Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi274InputQChi innerPair368Input
    leaf6129InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6129LowerChecked :
    lowerCheck 24 leaf6129Box leaf6129Inputs = true := by
  rfl'

private theorem leaf6129CoversExact : CoversExact 8
    leaf6129Box leaf6129Certificate leaf6129InnerLog leaf6129Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi274RoundedFacts
    innerPair368RoundedFacts leaf6129RoundedFacts (by rfl)

private theorem leaf6129FlatSound : Sound leaf6129Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6129CertificateValid
    leaf6129InnerLogValid leaf6129CoversExact leaf6129LowerChecked

private noncomputable def leaf6130Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (63/128), chiHi := (1/2) }

private noncomputable def leaf6130Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435827/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711481344) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (767952755/536870912) }, upper := { exponent := 1, mantissa := (93/64) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi274LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137427877885/137422962688) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf6130InnerLog : WideLogData :=
  innerPair368Data

set_option maxRecDepth 1000000 in
private theorem leaf6130LocalValidity :
    LeafFacts leaf6130Box leaf6130Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6130Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711481344) }) = true
      norm_num [leaf6130Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6130CertificateValid :
    WideCertificateValid leaf6130Box leaf6130Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi274ValidityFacts
    leaf6130LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6130CoverageChecked :
    coverageCheck (innerAD leaf6130Box) leaf6130InnerLog = true := by
  rfl'

private theorem leaf6130InnerLogValid :
    leaf6130InnerLog.Valid 8 (innerAD leaf6130Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint98PositiveFacts.valid leaf6130CoverageChecked

private noncomputable def leaf6130InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629681/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6130InputLogOnePlusV_eq :
    leaf6130InputLogOnePlusV = outerEnclosure 24
      (leaf6130Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6130RoundedFacts : LeafRoundedFacts 8
    leaf6130Certificate.logOnePlusV leaf6130InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6130InputLogOnePlusV_eq }

private noncomputable def leaf6130Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi274InputQChi innerPair368Input
    leaf6130InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6130LowerChecked :
    lowerCheck 24 leaf6130Box leaf6130Inputs = true := by
  rfl'

private theorem leaf6130CoversExact : CoversExact 8
    leaf6130Box leaf6130Certificate leaf6130InnerLog leaf6130Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi274RoundedFacts
    innerPair368RoundedFacts leaf6130RoundedFacts (by rfl)

private theorem leaf6130FlatSound : Sound leaf6130Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6130CertificateValid
    leaf6130InnerLogValid leaf6130CoversExact leaf6130LowerChecked

private noncomputable def leaf6131Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (31/64), chiHi := (63/128) }

private noncomputable def leaf6131Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435827/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711541760) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (764086367/536870912) }, upper := { exponent := 1, mantissa := (11845/8192) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi273LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137427938301/137423083520) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf6131InnerLog : WideLogData :=
  innerPair368Data

set_option maxRecDepth 1000000 in
private theorem leaf6131LocalValidity :
    LeafFacts leaf6131Box leaf6131Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6131Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711541760) }) = true
      norm_num [leaf6131Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6131CertificateValid :
    WideCertificateValid leaf6131Box leaf6131Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi273ValidityFacts
    leaf6131LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6131CoverageChecked :
    coverageCheck (innerAD leaf6131Box) leaf6131InnerLog = true := by
  rfl'

private theorem leaf6131InnerLogValid :
    leaf6131InnerLog.Valid 8 (innerAD leaf6131Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint98PositiveFacts.valid leaf6131CoverageChecked

private noncomputable def leaf6131InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629673/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6131InputLogOnePlusV_eq :
    leaf6131InputLogOnePlusV = outerEnclosure 24
      (leaf6131Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6131RoundedFacts : LeafRoundedFacts 8
    leaf6131Certificate.logOnePlusV leaf6131InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6131InputLogOnePlusV_eq }

private noncomputable def leaf6131Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi273InputQChi innerPair368Input
    leaf6131InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6131LowerChecked :
    lowerCheck 24 leaf6131Box leaf6131Inputs = true := by
  rfl'

private theorem leaf6131CoversExact : CoversExact 8
    leaf6131Box leaf6131Certificate leaf6131InnerLog leaf6131Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi273RoundedFacts
    innerPair368RoundedFacts leaf6131RoundedFacts (by rfl)

private theorem leaf6131FlatSound : Sound leaf6131Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6131CertificateValid
    leaf6131InnerLogValid leaf6131CoversExact leaf6131LowerChecked

private noncomputable def leaf6132Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (31/64), chiHi := (63/128) }

private noncomputable def leaf6132Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435829/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711477248) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (768149349/536870912) }, upper := { exponent := 1, mantissa := (2977/2048) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi273LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137427873789/137422954496) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf6132InnerLog : WideLogData :=
  innerPair368Data

set_option maxRecDepth 1000000 in
private theorem leaf6132LocalValidity :
    LeafFacts leaf6132Box leaf6132Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6132Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711477248) }) = true
      norm_num [leaf6132Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6132CertificateValid :
    WideCertificateValid leaf6132Box leaf6132Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi273ValidityFacts
    leaf6132LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6132CoverageChecked :
    coverageCheck (innerAD leaf6132Box) leaf6132InnerLog = true := by
  rfl'

private theorem leaf6132InnerLogValid :
    leaf6132InnerLog.Valid 8 (innerAD leaf6132Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint98PositiveFacts.valid leaf6132CoverageChecked

private noncomputable def leaf6132InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629681/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6132InputLogOnePlusV_eq :
    leaf6132InputLogOnePlusV = outerEnclosure 24
      (leaf6132Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6132RoundedFacts : LeafRoundedFacts 8
    leaf6132Certificate.logOnePlusV leaf6132InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6132InputLogOnePlusV_eq }

private noncomputable def leaf6132Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi273InputQChi innerPair368Input
    leaf6132InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6132LowerChecked :
    lowerCheck 24 leaf6132Box leaf6132Inputs = true := by
  rfl'

private theorem leaf6132CoversExact : CoversExact 8
    leaf6132Box leaf6132Certificate leaf6132InnerLog leaf6132Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi273RoundedFacts
    innerPair368RoundedFacts leaf6132RoundedFacts (by rfl)

private theorem leaf6132FlatSound : Sound leaf6132Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6132CertificateValid
    leaf6132InnerLogValid leaf6132CoversExact leaf6132LowerChecked

private noncomputable def leaf6133Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (63/128), chiHi := (1/2) }

private noncomputable def leaf6133Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435829/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711415808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (772081269/536870912) }, upper := { exponent := 1, mantissa := (187/128) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi274LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137427812349/137422831616) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf6133InnerLog : WideLogData :=
  innerPair371Data

set_option maxRecDepth 1000000 in
private theorem leaf6133LocalValidity :
    LeafFacts leaf6133Box leaf6133Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6133Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711415808) }) = true
      norm_num [leaf6133Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6133CertificateValid :
    WideCertificateValid leaf6133Box leaf6133Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi274ValidityFacts
    leaf6133LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6133CoverageChecked :
    coverageCheck (innerAD leaf6133Box) leaf6133InnerLog = true := by
  rfl'

private theorem leaf6133InnerLogValid :
    leaf6133InnerLog.Valid 8 (innerAD leaf6133Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint98PositiveFacts.valid leaf6133CoverageChecked

private noncomputable def leaf6133InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629689/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6133InputLogOnePlusV_eq :
    leaf6133InputLogOnePlusV = outerEnclosure 24
      (leaf6133Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6133RoundedFacts : LeafRoundedFacts 8
    leaf6133Certificate.logOnePlusV leaf6133InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6133InputLogOnePlusV_eq }

private noncomputable def leaf6133Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi274InputQChi innerPair371Input
    leaf6133InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6133LowerChecked :
    lowerCheck 24 leaf6133Box leaf6133Inputs = true := by
  rfl'

private theorem leaf6133CoversExact : CoversExact 8
    leaf6133Box leaf6133Certificate leaf6133InnerLog leaf6133Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi274RoundedFacts
    innerPair371RoundedFacts leaf6133RoundedFacts (by rfl)

private theorem leaf6133FlatSound : Sound leaf6133Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6133CertificateValid
    leaf6133InnerLogValid leaf6133CoversExact leaf6133LowerChecked

private noncomputable def leaf6134Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (63/128), chiHi := (1/2) }

private noncomputable def leaf6134Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435831/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711350272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (776209783/536870912) }, upper := { exponent := 1, mantissa := (47/32) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi274LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137427746813/137422700544) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf6134InnerLog : WideLogData :=
  innerPair371Data

set_option maxRecDepth 1000000 in
private theorem leaf6134LocalValidity :
    LeafFacts leaf6134Box leaf6134Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6134Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711350272) }) = true
      norm_num [leaf6134Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6134CertificateValid :
    WideCertificateValid leaf6134Box leaf6134Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi274ValidityFacts
    leaf6134LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6134CoverageChecked :
    coverageCheck (innerAD leaf6134Box) leaf6134InnerLog = true := by
  rfl'

private theorem leaf6134InnerLogValid :
    leaf6134InnerLog.Valid 8 (innerAD leaf6134Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint98PositiveFacts.valid leaf6134CoverageChecked

private noncomputable def leaf6134InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629697/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6134InputLogOnePlusV_eq :
    leaf6134InputLogOnePlusV = outerEnclosure 24
      (leaf6134Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6134RoundedFacts : LeafRoundedFacts 8
    leaf6134Certificate.logOnePlusV leaf6134InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6134InputLogOnePlusV_eq }

private noncomputable def leaf6134Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi274InputQChi innerPair371Input
    leaf6134InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6134LowerChecked :
    lowerCheck 24 leaf6134Box leaf6134Inputs = true := by
  rfl'

private theorem leaf6134CoversExact : CoversExact 8
    leaf6134Box leaf6134Certificate leaf6134InnerLog leaf6134Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi274RoundedFacts
    innerPair371RoundedFacts leaf6134RoundedFacts (by rfl)

private theorem leaf6134FlatSound : Sound leaf6134Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6134CertificateValid
    leaf6134InnerLogValid leaf6134CoversExact leaf6134LowerChecked

private noncomputable def leaf6135Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (15/32), chiHi := (61/128) }

private noncomputable def leaf6135Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435827/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711668736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (755960399/536870912) }, upper := { exponent := 1, mantissa := (11721/8192) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi271LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428065277/137423337472) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf6135InnerLog : WideLogData :=
  innerPair367Data

set_option maxRecDepth 1000000 in
private theorem leaf6135LocalValidity :
    LeafFacts leaf6135Box leaf6135Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6135Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711668736) }) = true
      norm_num [leaf6135Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6135CertificateValid :
    WideCertificateValid leaf6135Box leaf6135Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi271ValidityFacts
    leaf6135LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6135CoverageChecked :
    coverageCheck (innerAD leaf6135Box) leaf6135InnerLog = true := by
  rfl'

private theorem leaf6135InnerLogValid :
    leaf6135InnerLog.Valid 8 (innerAD leaf6135Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint97PositiveFacts.valid leaf6135CoverageChecked

private noncomputable def leaf6135InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814829/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6135InputLogOnePlusV_eq :
    leaf6135InputLogOnePlusV = outerEnclosure 24
      (leaf6135Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6135RoundedFacts : LeafRoundedFacts 8
    leaf6135Certificate.logOnePlusV leaf6135InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6135InputLogOnePlusV_eq }

private noncomputable def leaf6135Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi271InputQChi innerPair367Input
    leaf6135InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6135LowerChecked :
    lowerCheck 24 leaf6135Box leaf6135Inputs = true := by
  rfl'

private theorem leaf6135CoversExact : CoversExact 8
    leaf6135Box leaf6135Certificate leaf6135InnerLog leaf6135Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi271RoundedFacts
    innerPair367RoundedFacts leaf6135RoundedFacts (by rfl)

private theorem leaf6135FlatSound : Sound leaf6135Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6135CertificateValid
    leaf6135InnerLogValid leaf6135CoversExact leaf6135LowerChecked

private noncomputable def leaf6136Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (15/32), chiHi := (61/128) }

private noncomputable def leaf6136Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435829/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711606272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (759892317/536870912) }, upper := { exponent := 1, mantissa := (5891/4096) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi271LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428002813/137423212544) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf6136InnerLog : WideLogData :=
  innerPair726Data

set_option maxRecDepth 1000000 in
private theorem leaf6136LocalValidity :
    LeafFacts leaf6136Box leaf6136Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6136Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711606272) }) = true
      norm_num [leaf6136Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6136CertificateValid :
    WideCertificateValid leaf6136Box leaf6136Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi271ValidityFacts
    leaf6136LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6136CoverageChecked :
    coverageCheck (innerAD leaf6136Box) leaf6136InnerLog = true := by
  rfl'

private theorem leaf6136InnerLogValid :
    leaf6136InnerLog.Valid 8 (innerAD leaf6136Box) :=
  wideLogDataValid_of_cachedCheck endpoint464PositiveFacts
    endpoint470PositiveFacts.valid leaf6136CoverageChecked

private noncomputable def leaf6136InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814833/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6136InputLogOnePlusV_eq :
    leaf6136InputLogOnePlusV = outerEnclosure 24
      (leaf6136Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6136RoundedFacts : LeafRoundedFacts 8
    leaf6136Certificate.logOnePlusV leaf6136InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6136InputLogOnePlusV_eq }

private noncomputable def leaf6136Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi271InputQChi innerPair726Input
    leaf6136InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6136LowerChecked :
    lowerCheck 24 leaf6136Box leaf6136Inputs = true := by
  rfl'

private theorem leaf6136CoversExact : CoversExact 8
    leaf6136Box leaf6136Certificate leaf6136InnerLog leaf6136Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi271RoundedFacts
    innerPair726RoundedFacts leaf6136RoundedFacts (by rfl)

private theorem leaf6136FlatSound : Sound leaf6136Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6136CertificateValid
    leaf6136InnerLogValid leaf6136CoversExact leaf6136LowerChecked

private noncomputable def leaf6137Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (61/128), chiHi := (31/64) }

private noncomputable def leaf6137Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435829/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711540736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (764086365/536870912) }, upper := { exponent := 1, mantissa := (5923/4096) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi272LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137427937277/137423081472) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf6137InnerLog : WideLogData :=
  innerPair368Data

set_option maxRecDepth 1000000 in
private theorem leaf6137LocalValidity :
    LeafFacts leaf6137Box leaf6137Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6137Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711540736) }) = true
      norm_num [leaf6137Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6137CertificateValid :
    WideCertificateValid leaf6137Box leaf6137Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi272ValidityFacts
    leaf6137LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6137CoverageChecked :
    coverageCheck (innerAD leaf6137Box) leaf6137InnerLog = true := by
  rfl'

private theorem leaf6137InnerLogValid :
    leaf6137InnerLog.Valid 8 (innerAD leaf6137Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint98PositiveFacts.valid leaf6137CoverageChecked

private noncomputable def leaf6137InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814837/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6137InputLogOnePlusV_eq :
    leaf6137InputLogOnePlusV = outerEnclosure 24
      (leaf6137Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6137RoundedFacts : LeafRoundedFacts 8
    leaf6137Certificate.logOnePlusV leaf6137InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6137InputLogOnePlusV_eq }

private noncomputable def leaf6137Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi272InputQChi innerPair368Input
    leaf6137InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6137LowerChecked :
    lowerCheck 24 leaf6137Box leaf6137Inputs = true := by
  rfl'

private theorem leaf6137CoversExact : CoversExact 8
    leaf6137Box leaf6137Certificate leaf6137InnerLog leaf6137Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi272RoundedFacts
    innerPair368RoundedFacts leaf6137RoundedFacts (by rfl)

private theorem leaf6137FlatSound : Sound leaf6137Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6137CertificateValid
    leaf6137InnerLogValid leaf6137CoversExact leaf6137LowerChecked

private noncomputable def leaf6138Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (61/128), chiHi := (31/64) }

private noncomputable def leaf6138Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435831/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711477248) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (768083815/536870912) }, upper := { exponent := 1, mantissa := (2977/2048) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi272LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137427873789/137422954496) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf6138InnerLog : WideLogData :=
  innerPair368Data

set_option maxRecDepth 1000000 in
private theorem leaf6138LocalValidity :
    LeafFacts leaf6138Box leaf6138Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6138Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711477248) }) = true
      norm_num [leaf6138Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6138CertificateValid :
    WideCertificateValid leaf6138Box leaf6138Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi272ValidityFacts
    leaf6138LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6138CoverageChecked :
    coverageCheck (innerAD leaf6138Box) leaf6138InnerLog = true := by
  rfl'

private theorem leaf6138InnerLogValid :
    leaf6138InnerLog.Valid 8 (innerAD leaf6138Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint98PositiveFacts.valid leaf6138CoverageChecked

private noncomputable def leaf6138InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629681/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6138InputLogOnePlusV_eq :
    leaf6138InputLogOnePlusV = outerEnclosure 24
      (leaf6138Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6138RoundedFacts : LeafRoundedFacts 8
    leaf6138Certificate.logOnePlusV leaf6138InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6138InputLogOnePlusV_eq }

private noncomputable def leaf6138Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi272InputQChi innerPair368Input
    leaf6138InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6138LowerChecked :
    lowerCheck 24 leaf6138Box leaf6138Inputs = true := by
  rfl'

private theorem leaf6138CoversExact : CoversExact 8
    leaf6138Box leaf6138Certificate leaf6138InnerLog leaf6138Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi272RoundedFacts
    innerPair368RoundedFacts leaf6138RoundedFacts (by rfl)

private theorem leaf6138FlatSound : Sound leaf6138Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6138CertificateValid
    leaf6138InnerLogValid leaf6138CoversExact leaf6138LowerChecked

private noncomputable def leaf6139Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (15/32), chiHi := (61/128) }

private noncomputable def leaf6139Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435831/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711543808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (763824235/536870912) }, upper := { exponent := 1, mantissa := (11843/8192) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi271LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137427940349/137423087616) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf6139InnerLog : WideLogData :=
  innerPair731Data

set_option maxRecDepth 1000000 in
private theorem leaf6139LocalValidity :
    LeafFacts leaf6139Box leaf6139Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6139Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711543808) }) = true
      norm_num [leaf6139Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6139CertificateValid :
    WideCertificateValid leaf6139Box leaf6139Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi271ValidityFacts
    leaf6139LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6139CoverageChecked :
    coverageCheck (innerAD leaf6139Box) leaf6139InnerLog = true := by
  rfl'

private theorem leaf6139InnerLogValid :
    leaf6139InnerLog.Valid 8 (innerAD leaf6139Box) :=
  wideLogDataValid_of_cachedCheck endpoint469PositiveFacts
    endpoint471PositiveFacts.valid leaf6139CoverageChecked

private noncomputable def leaf6139InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629673/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6139InputLogOnePlusV_eq :
    leaf6139InputLogOnePlusV = outerEnclosure 24
      (leaf6139Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6139RoundedFacts : LeafRoundedFacts 8
    leaf6139Certificate.logOnePlusV leaf6139InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6139InputLogOnePlusV_eq }

private noncomputable def leaf6139Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi271InputQChi innerPair731Input
    leaf6139InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6139LowerChecked :
    lowerCheck 24 leaf6139Box leaf6139Inputs = true := by
  rfl'

private theorem leaf6139CoversExact : CoversExact 8
    leaf6139Box leaf6139Certificate leaf6139InnerLog leaf6139Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi271RoundedFacts
    innerPair731RoundedFacts leaf6139RoundedFacts (by rfl)

private theorem leaf6139FlatSound : Sound leaf6139Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6139CertificateValid
    leaf6139InnerLogValid leaf6139CoversExact leaf6139LowerChecked

private noncomputable def leaf6140Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (15/32), chiHi := (61/128) }

private noncomputable def leaf6140Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435833/268435456) }, vSqrt := { lower := (65527/65536), upper := (68716396541/68711481344) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (767756153/536870912) }, upper := { exponent := 1, mantissa := (93/64) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi271LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (137427877885/137422962688) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf6140InnerLog : WideLogData :=
  innerPair368Data

set_option maxRecDepth 1000000 in
private theorem leaf6140LocalValidity :
    LeafFacts leaf6140Box leaf6140Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6140Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (68716396541/68711481344) }) = true
      norm_num [leaf6140Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6140CertificateValid :
    WideCertificateValid leaf6140Box leaf6140Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi271ValidityFacts
    leaf6140LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6140CoverageChecked :
    coverageCheck (innerAD leaf6140Box) leaf6140InnerLog = true := by
  rfl'

private theorem leaf6140InnerLogValid :
    leaf6140InnerLog.Valid 8 (innerAD leaf6140Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint98PositiveFacts.valid leaf6140CoverageChecked

private noncomputable def leaf6140InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629681/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6140InputLogOnePlusV_eq :
    leaf6140InputLogOnePlusV = outerEnclosure 24
      (leaf6140Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6140RoundedFacts : LeafRoundedFacts 8
    leaf6140Certificate.logOnePlusV leaf6140InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6140InputLogOnePlusV_eq }

private noncomputable def leaf6140Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi271InputQChi innerPair368Input
    leaf6140InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6140LowerChecked :
    lowerCheck 24 leaf6140Box leaf6140Inputs = true := by
  rfl'

private theorem leaf6140CoversExact : CoversExact 8
    leaf6140Box leaf6140Certificate leaf6140InnerLog leaf6140Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi271RoundedFacts
    innerPair368RoundedFacts leaf6140RoundedFacts (by rfl)

private theorem leaf6140FlatSound : Sound leaf6140Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6140CertificateValid
    leaf6140InnerLogValid leaf6140CoversExact leaf6140LowerChecked

private noncomputable def leaf6141Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (61/128), chiHi := (31/64) }

private noncomputable def leaf6141Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435833/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711413760) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (772081265/536870912) }, upper := { exponent := 1, mantissa := (5985/4096) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi272LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137427810301/137422827520) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf6141InnerLog : WideLogData :=
  innerPair371Data

set_option maxRecDepth 1000000 in
private theorem leaf6141LocalValidity :
    LeafFacts leaf6141Box leaf6141Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6141Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711413760) }) = true
      norm_num [leaf6141Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6141CertificateValid :
    WideCertificateValid leaf6141Box leaf6141Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi272ValidityFacts
    leaf6141LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6141CoverageChecked :
    coverageCheck (innerAD leaf6141Box) leaf6141InnerLog = true := by
  rfl'

private theorem leaf6141InnerLogValid :
    leaf6141InnerLog.Valid 8 (innerAD leaf6141Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint98PositiveFacts.valid leaf6141CoverageChecked

private noncomputable def leaf6141InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629689/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6141InputLogOnePlusV_eq :
    leaf6141InputLogOnePlusV = outerEnclosure 24
      (leaf6141Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6141RoundedFacts : LeafRoundedFacts 8
    leaf6141Certificate.logOnePlusV leaf6141InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6141InputLogOnePlusV_eq }

private noncomputable def leaf6141Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi272InputQChi innerPair371Input
    leaf6141InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6141LowerChecked :
    lowerCheck 24 leaf6141Box leaf6141Inputs = true := by
  rfl'

private theorem leaf6141CoversExact : CoversExact 8
    leaf6141Box leaf6141Certificate leaf6141InnerLog leaf6141Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi272RoundedFacts
    innerPair371RoundedFacts leaf6141RoundedFacts (by rfl)

private theorem leaf6141FlatSound : Sound leaf6141Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6141CertificateValid
    leaf6141InnerLogValid leaf6141CoversExact leaf6141LowerChecked

private noncomputable def leaf6142Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (61/128), chiHi := (31/64) }

private noncomputable def leaf6142Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435835/268435456) }, vSqrt := { lower := (65527/65536), upper := (68716396541/68711350272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (776078715/536870912) }, upper := { exponent := 1, mantissa := (47/32) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi272LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (137427746813/137422700544) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf6142InnerLog : WideLogData :=
  innerPair371Data

set_option maxRecDepth 1000000 in
private theorem leaf6142LocalValidity :
    LeafFacts leaf6142Box leaf6142Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6142Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (68716396541/68711350272) }) = true
      norm_num [leaf6142Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6142CertificateValid :
    WideCertificateValid leaf6142Box leaf6142Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi272ValidityFacts
    leaf6142LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6142CoverageChecked :
    coverageCheck (innerAD leaf6142Box) leaf6142InnerLog = true := by
  rfl'

private theorem leaf6142InnerLogValid :
    leaf6142InnerLog.Valid 8 (innerAD leaf6142Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint98PositiveFacts.valid leaf6142CoverageChecked

private noncomputable def leaf6142InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629697/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6142InputLogOnePlusV_eq :
    leaf6142InputLogOnePlusV = outerEnclosure 24
      (leaf6142Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6142RoundedFacts : LeafRoundedFacts 8
    leaf6142Certificate.logOnePlusV leaf6142InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6142InputLogOnePlusV_eq }

private noncomputable def leaf6142Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi272InputQChi innerPair371Input
    leaf6142InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6142LowerChecked :
    lowerCheck 24 leaf6142Box leaf6142Inputs = true := by
  rfl'

private theorem leaf6142CoversExact : CoversExact 8
    leaf6142Box leaf6142Certificate leaf6142InnerLog leaf6142Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi272RoundedFacts
    innerPair371RoundedFacts leaf6142RoundedFacts (by rfl)

private theorem leaf6142FlatSound : Sound leaf6142Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6142CertificateValid
    leaf6142InnerLogValid leaf6142CoversExact leaf6142LowerChecked

private noncomputable def leaf6143Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (31/64), chiHi := (63/128) }

private noncomputable def leaf6143Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435831/268435456) }, vSqrt := { lower := (8191/8192), upper := (4042140973/4041847808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (772212331/536870912) }, upper := { exponent := 1, mantissa := (11971/8192) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi273LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (8083988781/8083695616) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf6143InnerLog : WideLogData :=
  innerPair371Data

set_option maxRecDepth 1000000 in
private theorem leaf6143LocalValidity :
    LeafFacts leaf6143Box leaf6143Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6143Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4042140973/4041847808) }) = true
      norm_num [leaf6143Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6143CertificateValid :
    WideCertificateValid leaf6143Box leaf6143Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi273ValidityFacts
    leaf6143LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6143CoverageChecked :
    coverageCheck (innerAD leaf6143Box) leaf6143InnerLog = true := by
  rfl'

private theorem leaf6143InnerLogValid :
    leaf6143InnerLog.Valid 8 (innerAD leaf6143Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint98PositiveFacts.valid leaf6143CoverageChecked

private noncomputable def leaf6143InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629689/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6143InputLogOnePlusV_eq :
    leaf6143InputLogOnePlusV = outerEnclosure 24
      (leaf6143Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6143RoundedFacts : LeafRoundedFacts 8
    leaf6143Certificate.logOnePlusV leaf6143InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6143InputLogOnePlusV_eq }

private noncomputable def leaf6143Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi273InputQChi innerPair371Input
    leaf6143InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6143LowerChecked :
    lowerCheck 24 leaf6143Box leaf6143Inputs = true := by
  rfl'

private theorem leaf6143CoversExact : CoversExact 8
    leaf6143Box leaf6143Certificate leaf6143InnerLog leaf6143Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi273RoundedFacts
    innerPair371RoundedFacts leaf6143RoundedFacts (by rfl)

private theorem leaf6143FlatSound : Sound leaf6143Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6143CertificateValid
    leaf6143InnerLogValid leaf6143CoversExact leaf6143LowerChecked

private noncomputable def leaf6144Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (31/64), chiHi := (63/128) }

private noncomputable def leaf6144Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435833/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711348224) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (776275313/536870912) }, upper := { exponent := 1, mantissa := (6017/4096) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi273LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137427744765/137422696448) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf6144InnerLog : WideLogData :=
  innerPair733Data

set_option maxRecDepth 1000000 in
private theorem leaf6144LocalValidity :
    LeafFacts leaf6144Box leaf6144Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6144Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711348224) }) = true
      norm_num [leaf6144Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6144CertificateValid :
    WideCertificateValid leaf6144Box leaf6144Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi273ValidityFacts
    leaf6144LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6144CoverageChecked :
    coverageCheck (innerAD leaf6144Box) leaf6144InnerLog = true := by
  rfl'

private theorem leaf6144InnerLogValid :
    leaf6144InnerLog.Valid 8 (innerAD leaf6144Box) :=
  wideLogDataValid_of_cachedCheck endpoint470PositiveFacts
    endpoint472PositiveFacts.valid leaf6144CoverageChecked

private noncomputable def leaf6144InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629697/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6144InputLogOnePlusV_eq :
    leaf6144InputLogOnePlusV = outerEnclosure 24
      (leaf6144Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6144RoundedFacts : LeafRoundedFacts 8
    leaf6144Certificate.logOnePlusV leaf6144InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6144InputLogOnePlusV_eq }

private noncomputable def leaf6144Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi273InputQChi innerPair733Input
    leaf6144InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6144LowerChecked :
    lowerCheck 24 leaf6144Box leaf6144Inputs = true := by
  rfl'

private theorem leaf6144CoversExact : CoversExact 8
    leaf6144Box leaf6144Certificate leaf6144InnerLog leaf6144Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi273RoundedFacts
    innerPair733RoundedFacts leaf6144RoundedFacts (by rfl)

private theorem leaf6144FlatSound : Sound leaf6144Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6144CertificateValid
    leaf6144InnerLogValid leaf6144CoversExact leaf6144LowerChecked

private noncomputable def leaf6145Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (63/128), chiHi := (1/2) }

private noncomputable def leaf6145Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435833/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711284736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (780338297/536870912) }, upper := { exponent := 1, mantissa := (189/128) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi274LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137427681277/137422569472) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf6145InnerLog : WideLogData :=
  innerPair372Data

set_option maxRecDepth 1000000 in
private theorem leaf6145LocalValidity :
    LeafFacts leaf6145Box leaf6145Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6145Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711284736) }) = true
      norm_num [leaf6145Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6145CertificateValid :
    WideCertificateValid leaf6145Box leaf6145Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi274ValidityFacts
    leaf6145LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6145CoverageChecked :
    coverageCheck (innerAD leaf6145Box) leaf6145InnerLog = true := by
  rfl'

private theorem leaf6145InnerLogValid :
    leaf6145InnerLog.Valid 8 (innerAD leaf6145Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint99PositiveFacts.valid leaf6145CoverageChecked

private noncomputable def leaf6145InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629705/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6145InputLogOnePlusV_eq :
    leaf6145InputLogOnePlusV = outerEnclosure 24
      (leaf6145Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6145RoundedFacts : LeafRoundedFacts 8
    leaf6145Certificate.logOnePlusV leaf6145InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6145InputLogOnePlusV_eq }

private noncomputable def leaf6145Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi274InputQChi innerPair372Input
    leaf6145InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6145LowerChecked :
    lowerCheck 24 leaf6145Box leaf6145Inputs = true := by
  rfl'

private theorem leaf6145CoversExact : CoversExact 8
    leaf6145Box leaf6145Certificate leaf6145InnerLog leaf6145Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi274RoundedFacts
    innerPair372RoundedFacts leaf6145RoundedFacts (by rfl)

private theorem leaf6145FlatSound : Sound leaf6145Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6145CertificateValid
    leaf6145InnerLogValid leaf6145CoversExact leaf6145LowerChecked

private noncomputable def leaf6146Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (63/128), chiHi := (1/2) }

private noncomputable def leaf6146Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435835/268435456) }, vSqrt := { lower := (8191/8192), upper := (5285876657/5285478400) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (784466811/536870912) }, upper := { exponent := 1, mantissa := (95/64) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi274LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (10571355057/10570956800) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf6146InnerLog : WideLogData :=
  innerPair372Data

set_option maxRecDepth 1000000 in
private theorem leaf6146LocalValidity :
    LeafFacts leaf6146Box leaf6146Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6146Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5285876657/5285478400) }) = true
      norm_num [leaf6146Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6146CertificateValid :
    WideCertificateValid leaf6146Box leaf6146Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi274ValidityFacts
    leaf6146LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6146CoverageChecked :
    coverageCheck (innerAD leaf6146Box) leaf6146InnerLog = true := by
  rfl'

private theorem leaf6146InnerLogValid :
    leaf6146InnerLog.Valid 8 (innerAD leaf6146Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint99PositiveFacts.valid leaf6146CoverageChecked

private noncomputable def leaf6146InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629713/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6146InputLogOnePlusV_eq :
    leaf6146InputLogOnePlusV = outerEnclosure 24
      (leaf6146Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6146RoundedFacts : LeafRoundedFacts 8
    leaf6146Certificate.logOnePlusV leaf6146InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6146InputLogOnePlusV_eq }

private noncomputable def leaf6146Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi274InputQChi innerPair372Input
    leaf6146InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6146LowerChecked :
    lowerCheck 24 leaf6146Box leaf6146Inputs = true := by
  rfl'

private theorem leaf6146CoversExact : CoversExact 8
    leaf6146Box leaf6146Certificate leaf6146InnerLog leaf6146Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi274RoundedFacts
    innerPair372RoundedFacts leaf6146RoundedFacts (by rfl)

private theorem leaf6146FlatSound : Sound leaf6146Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6146CertificateValid
    leaf6146InnerLogValid leaf6146CoversExact leaf6146LowerChecked

private noncomputable def leaf6147Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (31/64), chiHi := (63/128) }

private noncomputable def leaf6147Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435835/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711283712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (780338295/536870912) }, upper := { exponent := 1, mantissa := (12097/8192) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi273LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137427680253/137422567424) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf6147InnerLog : WideLogData :=
  innerPair372Data

set_option maxRecDepth 1000000 in
private theorem leaf6147LocalValidity :
    LeafFacts leaf6147Box leaf6147Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6147Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711283712) }) = true
      norm_num [leaf6147Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6147CertificateValid :
    WideCertificateValid leaf6147Box leaf6147Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi273ValidityFacts
    leaf6147LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6147CoverageChecked :
    coverageCheck (innerAD leaf6147Box) leaf6147InnerLog = true := by
  rfl'

private theorem leaf6147InnerLogValid :
    leaf6147InnerLog.Valid 8 (innerAD leaf6147Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint99PositiveFacts.valid leaf6147CoverageChecked

private noncomputable def leaf6147InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629705/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6147InputLogOnePlusV_eq :
    leaf6147InputLogOnePlusV = outerEnclosure 24
      (leaf6147Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6147RoundedFacts : LeafRoundedFacts 8
    leaf6147Certificate.logOnePlusV leaf6147InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6147InputLogOnePlusV_eq }

private noncomputable def leaf6147Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi273InputQChi innerPair372Input
    leaf6147InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6147LowerChecked :
    lowerCheck 24 leaf6147Box leaf6147Inputs = true := by
  rfl'

private theorem leaf6147CoversExact : CoversExact 8
    leaf6147Box leaf6147Certificate leaf6147InnerLog leaf6147Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi273RoundedFacts
    innerPair372RoundedFacts leaf6147RoundedFacts (by rfl)

private theorem leaf6147FlatSound : Sound leaf6147Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6147CertificateValid
    leaf6147InnerLogValid leaf6147CoversExact leaf6147LowerChecked

private noncomputable def leaf6148Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (31/64), chiHi := (63/128) }

private noncomputable def leaf6148Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435837/268435456) }, vSqrt := { lower := (65527/65536), upper := (5285876657/5285478400) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (784401277/536870912) }, upper := { exponent := 1, mantissa := (95/64) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi273LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (10571355057/10570956800) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf6148InnerLog : WideLogData :=
  innerPair372Data

set_option maxRecDepth 1000000 in
private theorem leaf6148LocalValidity :
    LeafFacts leaf6148Box leaf6148Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6148Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (5285876657/5285478400) }) = true
      norm_num [leaf6148Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6148CertificateValid :
    WideCertificateValid leaf6148Box leaf6148Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi273ValidityFacts
    leaf6148LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6148CoverageChecked :
    coverageCheck (innerAD leaf6148Box) leaf6148InnerLog = true := by
  rfl'

private theorem leaf6148InnerLogValid :
    leaf6148InnerLog.Valid 8 (innerAD leaf6148Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint99PositiveFacts.valid leaf6148CoverageChecked

private noncomputable def leaf6148InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629713/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6148InputLogOnePlusV_eq :
    leaf6148InputLogOnePlusV = outerEnclosure 24
      (leaf6148Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6148RoundedFacts : LeafRoundedFacts 8
    leaf6148Certificate.logOnePlusV leaf6148InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6148InputLogOnePlusV_eq }

private noncomputable def leaf6148Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi273InputQChi innerPair372Input
    leaf6148InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6148LowerChecked :
    lowerCheck 24 leaf6148Box leaf6148Inputs = true := by
  rfl'

private theorem leaf6148CoversExact : CoversExact 8
    leaf6148Box leaf6148Certificate leaf6148InnerLog leaf6148Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi273RoundedFacts
    innerPair372RoundedFacts leaf6148RoundedFacts (by rfl)

private theorem leaf6148FlatSound : Sound leaf6148Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6148CertificateValid
    leaf6148InnerLogValid leaf6148CoversExact leaf6148LowerChecked

private noncomputable def leaf6149Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (63/128), chiHi := (1/2) }

private noncomputable def leaf6149Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435837/268435456) }, vSqrt := { lower := (8191/8192), upper := (5726278997/5725929472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (788595325/536870912) }, upper := { exponent := 1, mantissa := (191/128) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi274LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (11452208469/11451858944) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf6149InnerLog : WideLogData :=
  innerPair375Data

set_option maxRecDepth 1000000 in
private theorem leaf6149LocalValidity :
    LeafFacts leaf6149Box leaf6149Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6149Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5726278997/5725929472) }) = true
      norm_num [leaf6149Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6149CertificateValid :
    WideCertificateValid leaf6149Box leaf6149Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi274ValidityFacts
    leaf6149LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6149CoverageChecked :
    coverageCheck (innerAD leaf6149Box) leaf6149InnerLog = true := by
  rfl'

private theorem leaf6149InnerLogValid :
    leaf6149InnerLog.Valid 8 (innerAD leaf6149Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint99PositiveFacts.valid leaf6149CoverageChecked

private noncomputable def leaf6149InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629593/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6149InputLogOnePlusV_eq :
    leaf6149InputLogOnePlusV = outerEnclosure 24
      (leaf6149Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6149RoundedFacts : LeafRoundedFacts 8
    leaf6149Certificate.logOnePlusV leaf6149InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6149InputLogOnePlusV_eq }

private noncomputable def leaf6149Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi274InputQChi innerPair375Input
    leaf6149InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6149LowerChecked :
    lowerCheck 24 leaf6149Box leaf6149Inputs = true := by
  rfl'

private theorem leaf6149CoversExact : CoversExact 8
    leaf6149Box leaf6149Certificate leaf6149InnerLog leaf6149Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi274RoundedFacts
    innerPair375RoundedFacts leaf6149RoundedFacts (by rfl)

private theorem leaf6149FlatSound : Sound leaf6149Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6149CertificateValid
    leaf6149InnerLogValid leaf6149CoversExact leaf6149LowerChecked

private noncomputable def leaf6150Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (63/128), chiHi := (1/2) }

private noncomputable def leaf6150Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435839/268435456) }, vSqrt := { lower := (65527/65536), upper := (17178836991/17177772032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (792723839/536870912) }, upper := { exponent := 1, mantissa := (3/2) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi274LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (34356609023/34355544064) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf6150InnerLog : WideLogData :=
  innerPair375Data

set_option maxRecDepth 1000000 in
private theorem leaf6150LocalValidity :
    LeafFacts leaf6150Box leaf6150Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6150Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (17178836991/17177772032) }) = true
      norm_num [leaf6150Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6150CertificateValid :
    WideCertificateValid leaf6150Box leaf6150Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi274ValidityFacts
    leaf6150LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6150CoverageChecked :
    coverageCheck (innerAD leaf6150Box) leaf6150InnerLog = true := by
  rfl'

private theorem leaf6150InnerLogValid :
    leaf6150InnerLog.Valid 8 (innerAD leaf6150Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint99PositiveFacts.valid leaf6150CoverageChecked

private noncomputable def leaf6150InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629601/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6150InputLogOnePlusV_eq :
    leaf6150InputLogOnePlusV = outerEnclosure 24
      (leaf6150Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6150RoundedFacts : LeafRoundedFacts 8
    leaf6150Certificate.logOnePlusV leaf6150InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6150InputLogOnePlusV_eq }

private noncomputable def leaf6150Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi274InputQChi innerPair375Input
    leaf6150InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6150LowerChecked :
    lowerCheck 24 leaf6150Box leaf6150Inputs = true := by
  rfl'

private theorem leaf6150CoversExact : CoversExact 8
    leaf6150Box leaf6150Certificate leaf6150InnerLog leaf6150Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi274RoundedFacts
    innerPair375RoundedFacts leaf6150RoundedFacts (by rfl)

private theorem leaf6150FlatSound : Sound leaf6150Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6150CertificateValid
    leaf6150InnerLogValid leaf6150CoversExact leaf6150LowerChecked

private noncomputable def component122Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (7/16), chiHi := (57/128) }

set_option maxRecDepth 1000000 in
private theorem component122Node0_sound : Sound component122Node0Box :=
  sound_of_literal_split component122Node0Box leaf6087Box leaf6088Box
    .k (121/32) (by rfl) (by rfl)
    leaf6087FlatSound leaf6088FlatSound

private noncomputable def component122Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (57/128), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component122Node1_sound : Sound component122Node1Box :=
  sound_of_literal_split component122Node1Box leaf6089Box leaf6090Box
    .k (121/32) (by rfl) (by rfl)
    leaf6089FlatSound leaf6090FlatSound

private noncomputable def component122Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (7/16), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component122Node2_sound : Sound component122Node2Box :=
  sound_of_literal_split component122Node2Box component122Node0Box component122Node1Box
    .chi (57/128) (by rfl) (by rfl)
    component122Node0_sound component122Node1_sound

private noncomputable def component122Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (7/16), chiHi := (57/128) }

set_option maxRecDepth 1000000 in
private theorem component122Node3_sound : Sound component122Node3Box :=
  sound_of_literal_split component122Node3Box leaf6091Box leaf6092Box
    .k (123/32) (by rfl) (by rfl)
    leaf6091FlatSound leaf6092FlatSound

private noncomputable def component122Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (57/128), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component122Node4_sound : Sound component122Node4Box :=
  sound_of_literal_split component122Node4Box leaf6093Box leaf6094Box
    .k (123/32) (by rfl) (by rfl)
    leaf6093FlatSound leaf6094FlatSound

private noncomputable def component122Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (7/16), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component122Node5_sound : Sound component122Node5Box :=
  sound_of_literal_split component122Node5Box component122Node3Box component122Node4Box
    .chi (57/128) (by rfl) (by rfl)
    component122Node3_sound component122Node4_sound

private noncomputable def component122Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (7/16), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component122Node6_sound : Sound component122Node6Box :=
  sound_of_literal_split component122Node6Box component122Node2Box component122Node5Box
    .k (61/16) (by rfl) (by rfl)
    component122Node2_sound component122Node5_sound

private noncomputable def component122Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (29/64), chiHi := (59/128) }

set_option maxRecDepth 1000000 in
private theorem component122Node7_sound : Sound component122Node7Box :=
  sound_of_literal_split component122Node7Box leaf6095Box leaf6096Box
    .k (121/32) (by rfl) (by rfl)
    leaf6095FlatSound leaf6096FlatSound

private noncomputable def component122Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (59/128), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component122Node8_sound : Sound component122Node8Box :=
  sound_of_literal_split component122Node8Box leaf6097Box leaf6098Box
    .k (121/32) (by rfl) (by rfl)
    leaf6097FlatSound leaf6098FlatSound

private noncomputable def component122Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (29/64), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component122Node9_sound : Sound component122Node9Box :=
  sound_of_literal_split component122Node9Box component122Node7Box component122Node8Box
    .chi (59/128) (by rfl) (by rfl)
    component122Node7_sound component122Node8_sound

private noncomputable def component122Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (29/64), chiHi := (59/128) }

set_option maxRecDepth 1000000 in
private theorem component122Node10_sound : Sound component122Node10Box :=
  sound_of_literal_split component122Node10Box leaf6099Box leaf6100Box
    .k (123/32) (by rfl) (by rfl)
    leaf6099FlatSound leaf6100FlatSound

private noncomputable def component122Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (59/128), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component122Node11_sound : Sound component122Node11Box :=
  sound_of_literal_split component122Node11Box leaf6101Box leaf6102Box
    .k (123/32) (by rfl) (by rfl)
    leaf6101FlatSound leaf6102FlatSound

private noncomputable def component122Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (29/64), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component122Node12_sound : Sound component122Node12Box :=
  sound_of_literal_split component122Node12Box component122Node10Box component122Node11Box
    .chi (59/128) (by rfl) (by rfl)
    component122Node10_sound component122Node11_sound

private noncomputable def component122Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (29/64), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component122Node13_sound : Sound component122Node13Box :=
  sound_of_literal_split component122Node13Box component122Node9Box component122Node12Box
    .k (61/16) (by rfl) (by rfl)
    component122Node9_sound component122Node12_sound

private noncomputable def component122Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (7/16), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component122Node14_sound : Sound component122Node14Box :=
  sound_of_literal_split component122Node14Box component122Node6Box component122Node13Box
    .chi (29/64) (by rfl) (by rfl)
    component122Node6_sound component122Node13_sound

private noncomputable def component122Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (7/16), chiHi := (57/128) }

set_option maxRecDepth 1000000 in
private theorem component122Node15_sound : Sound component122Node15Box :=
  sound_of_literal_split component122Node15Box leaf6103Box leaf6104Box
    .k (125/32) (by rfl) (by rfl)
    leaf6103FlatSound leaf6104FlatSound

private noncomputable def component122Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (57/128), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component122Node16_sound : Sound component122Node16Box :=
  sound_of_literal_split component122Node16Box leaf6105Box leaf6106Box
    .k (125/32) (by rfl) (by rfl)
    leaf6105FlatSound leaf6106FlatSound

private noncomputable def component122Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (7/16), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component122Node17_sound : Sound component122Node17Box :=
  sound_of_literal_split component122Node17Box component122Node15Box component122Node16Box
    .chi (57/128) (by rfl) (by rfl)
    component122Node15_sound component122Node16_sound

private noncomputable def component122Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (7/16), chiHi := (57/128) }

set_option maxRecDepth 1000000 in
private theorem component122Node18_sound : Sound component122Node18Box :=
  sound_of_literal_split component122Node18Box leaf6107Box leaf6108Box
    .k (127/32) (by rfl) (by rfl)
    leaf6107FlatSound leaf6108FlatSound

private noncomputable def component122Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (57/128), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component122Node19_sound : Sound component122Node19Box :=
  sound_of_literal_split component122Node19Box leaf6109Box leaf6110Box
    .k (127/32) (by rfl) (by rfl)
    leaf6109FlatSound leaf6110FlatSound

private noncomputable def component122Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (7/16), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component122Node20_sound : Sound component122Node20Box :=
  sound_of_literal_split component122Node20Box component122Node18Box component122Node19Box
    .chi (57/128) (by rfl) (by rfl)
    component122Node18_sound component122Node19_sound

private noncomputable def component122Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (7/16), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component122Node21_sound : Sound component122Node21Box :=
  sound_of_literal_split component122Node21Box component122Node17Box component122Node20Box
    .k (63/16) (by rfl) (by rfl)
    component122Node17_sound component122Node20_sound

private noncomputable def component122Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (29/64), chiHi := (59/128) }

set_option maxRecDepth 1000000 in
private theorem component122Node22_sound : Sound component122Node22Box :=
  sound_of_literal_split component122Node22Box leaf6111Box leaf6112Box
    .k (125/32) (by rfl) (by rfl)
    leaf6111FlatSound leaf6112FlatSound

private noncomputable def component122Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (59/128), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component122Node23_sound : Sound component122Node23Box :=
  sound_of_literal_split component122Node23Box leaf6113Box leaf6114Box
    .k (125/32) (by rfl) (by rfl)
    leaf6113FlatSound leaf6114FlatSound

private noncomputable def component122Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (29/64), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component122Node24_sound : Sound component122Node24Box :=
  sound_of_literal_split component122Node24Box component122Node22Box component122Node23Box
    .chi (59/128) (by rfl) (by rfl)
    component122Node22_sound component122Node23_sound

private noncomputable def component122Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (29/64), chiHi := (59/128) }

set_option maxRecDepth 1000000 in
private theorem component122Node25_sound : Sound component122Node25Box :=
  sound_of_literal_split component122Node25Box leaf6115Box leaf6116Box
    .k (127/32) (by rfl) (by rfl)
    leaf6115FlatSound leaf6116FlatSound

private noncomputable def component122Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (59/128), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component122Node26_sound : Sound component122Node26Box :=
  sound_of_literal_split component122Node26Box leaf6117Box leaf6118Box
    .k (127/32) (by rfl) (by rfl)
    leaf6117FlatSound leaf6118FlatSound

private noncomputable def component122Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (29/64), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component122Node27_sound : Sound component122Node27Box :=
  sound_of_literal_split component122Node27Box component122Node25Box component122Node26Box
    .chi (59/128) (by rfl) (by rfl)
    component122Node25_sound component122Node26_sound

private noncomputable def component122Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (29/64), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component122Node28_sound : Sound component122Node28Box :=
  sound_of_literal_split component122Node28Box component122Node24Box component122Node27Box
    .k (63/16) (by rfl) (by rfl)
    component122Node24_sound component122Node27_sound

private noncomputable def component122Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (7/16), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component122Node29_sound : Sound component122Node29Box :=
  sound_of_literal_split component122Node29Box component122Node21Box component122Node28Box
    .chi (29/64) (by rfl) (by rfl)
    component122Node21_sound component122Node28_sound

private noncomputable def component122Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (4), chiLo := (7/16), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component122Node30_sound : Sound component122Node30Box :=
  sound_of_literal_split component122Node30Box component122Node14Box component122Node29Box
    .k (31/8) (by rfl) (by rfl)
    component122Node14_sound component122Node29_sound

private noncomputable def component122Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (15/32), chiHi := (61/128) }

set_option maxRecDepth 1000000 in
private theorem component122Node31_sound : Sound component122Node31Box :=
  sound_of_literal_split component122Node31Box leaf6119Box leaf6120Box
    .k (121/32) (by rfl) (by rfl)
    leaf6119FlatSound leaf6120FlatSound

private noncomputable def component122Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (61/128), chiHi := (31/64) }

set_option maxRecDepth 1000000 in
private theorem component122Node32_sound : Sound component122Node32Box :=
  sound_of_literal_split component122Node32Box leaf6121Box leaf6122Box
    .k (121/32) (by rfl) (by rfl)
    leaf6121FlatSound leaf6122FlatSound

private noncomputable def component122Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (15/32), chiHi := (31/64) }

set_option maxRecDepth 1000000 in
private theorem component122Node33_sound : Sound component122Node33Box :=
  sound_of_literal_split component122Node33Box component122Node31Box component122Node32Box
    .chi (61/128) (by rfl) (by rfl)
    component122Node31_sound component122Node32_sound

private noncomputable def component122Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (15/32), chiHi := (61/128) }

set_option maxRecDepth 1000000 in
private theorem component122Node34_sound : Sound component122Node34Box :=
  sound_of_literal_split component122Node34Box leaf6123Box leaf6124Box
    .k (123/32) (by rfl) (by rfl)
    leaf6123FlatSound leaf6124FlatSound

private noncomputable def component122Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (61/128), chiHi := (31/64) }

set_option maxRecDepth 1000000 in
private theorem component122Node35_sound : Sound component122Node35Box :=
  sound_of_literal_split component122Node35Box leaf6125Box leaf6126Box
    .k (123/32) (by rfl) (by rfl)
    leaf6125FlatSound leaf6126FlatSound

private noncomputable def component122Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (15/32), chiHi := (31/64) }

set_option maxRecDepth 1000000 in
private theorem component122Node36_sound : Sound component122Node36Box :=
  sound_of_literal_split component122Node36Box component122Node34Box component122Node35Box
    .chi (61/128) (by rfl) (by rfl)
    component122Node34_sound component122Node35_sound

private noncomputable def component122Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (15/32), chiHi := (31/64) }

set_option maxRecDepth 1000000 in
private theorem component122Node37_sound : Sound component122Node37Box :=
  sound_of_literal_split component122Node37Box component122Node33Box component122Node36Box
    .k (61/16) (by rfl) (by rfl)
    component122Node33_sound component122Node36_sound

private noncomputable def component122Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (31/64), chiHi := (63/128) }

set_option maxRecDepth 1000000 in
private theorem component122Node38_sound : Sound component122Node38Box :=
  sound_of_literal_split component122Node38Box leaf6127Box leaf6128Box
    .k (121/32) (by rfl) (by rfl)
    leaf6127FlatSound leaf6128FlatSound

private noncomputable def component122Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (63/128), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component122Node39_sound : Sound component122Node39Box :=
  sound_of_literal_split component122Node39Box leaf6129Box leaf6130Box
    .k (121/32) (by rfl) (by rfl)
    leaf6129FlatSound leaf6130FlatSound

private noncomputable def component122Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (31/64), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component122Node40_sound : Sound component122Node40Box :=
  sound_of_literal_split component122Node40Box component122Node38Box component122Node39Box
    .chi (63/128) (by rfl) (by rfl)
    component122Node38_sound component122Node39_sound

private noncomputable def component122Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (31/64), chiHi := (63/128) }

set_option maxRecDepth 1000000 in
private theorem component122Node41_sound : Sound component122Node41Box :=
  sound_of_literal_split component122Node41Box leaf6131Box leaf6132Box
    .k (123/32) (by rfl) (by rfl)
    leaf6131FlatSound leaf6132FlatSound

private noncomputable def component122Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (63/128), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component122Node42_sound : Sound component122Node42Box :=
  sound_of_literal_split component122Node42Box leaf6133Box leaf6134Box
    .k (123/32) (by rfl) (by rfl)
    leaf6133FlatSound leaf6134FlatSound

private noncomputable def component122Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (31/64), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component122Node43_sound : Sound component122Node43Box :=
  sound_of_literal_split component122Node43Box component122Node41Box component122Node42Box
    .chi (63/128) (by rfl) (by rfl)
    component122Node41_sound component122Node42_sound

private noncomputable def component122Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (31/64), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component122Node44_sound : Sound component122Node44Box :=
  sound_of_literal_split component122Node44Box component122Node40Box component122Node43Box
    .k (61/16) (by rfl) (by rfl)
    component122Node40_sound component122Node43_sound

private noncomputable def component122Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (15/32), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component122Node45_sound : Sound component122Node45Box :=
  sound_of_literal_split component122Node45Box component122Node37Box component122Node44Box
    .chi (31/64) (by rfl) (by rfl)
    component122Node37_sound component122Node44_sound

private noncomputable def component122Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (15/32), chiHi := (61/128) }

set_option maxRecDepth 1000000 in
private theorem component122Node46_sound : Sound component122Node46Box :=
  sound_of_literal_split component122Node46Box leaf6135Box leaf6136Box
    .k (125/32) (by rfl) (by rfl)
    leaf6135FlatSound leaf6136FlatSound

private noncomputable def component122Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (61/128), chiHi := (31/64) }

set_option maxRecDepth 1000000 in
private theorem component122Node47_sound : Sound component122Node47Box :=
  sound_of_literal_split component122Node47Box leaf6137Box leaf6138Box
    .k (125/32) (by rfl) (by rfl)
    leaf6137FlatSound leaf6138FlatSound

private noncomputable def component122Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (15/32), chiHi := (31/64) }

set_option maxRecDepth 1000000 in
private theorem component122Node48_sound : Sound component122Node48Box :=
  sound_of_literal_split component122Node48Box component122Node46Box component122Node47Box
    .chi (61/128) (by rfl) (by rfl)
    component122Node46_sound component122Node47_sound

private noncomputable def component122Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (15/32), chiHi := (61/128) }

set_option maxRecDepth 1000000 in
private theorem component122Node49_sound : Sound component122Node49Box :=
  sound_of_literal_split component122Node49Box leaf6139Box leaf6140Box
    .k (127/32) (by rfl) (by rfl)
    leaf6139FlatSound leaf6140FlatSound

private noncomputable def component122Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (61/128), chiHi := (31/64) }

set_option maxRecDepth 1000000 in
private theorem component122Node50_sound : Sound component122Node50Box :=
  sound_of_literal_split component122Node50Box leaf6141Box leaf6142Box
    .k (127/32) (by rfl) (by rfl)
    leaf6141FlatSound leaf6142FlatSound

private noncomputable def component122Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (15/32), chiHi := (31/64) }

set_option maxRecDepth 1000000 in
private theorem component122Node51_sound : Sound component122Node51Box :=
  sound_of_literal_split component122Node51Box component122Node49Box component122Node50Box
    .chi (61/128) (by rfl) (by rfl)
    component122Node49_sound component122Node50_sound

private noncomputable def component122Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (15/32), chiHi := (31/64) }

set_option maxRecDepth 1000000 in
private theorem component122Node52_sound : Sound component122Node52Box :=
  sound_of_literal_split component122Node52Box component122Node48Box component122Node51Box
    .k (63/16) (by rfl) (by rfl)
    component122Node48_sound component122Node51_sound

private noncomputable def component122Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (31/64), chiHi := (63/128) }

set_option maxRecDepth 1000000 in
private theorem component122Node53_sound : Sound component122Node53Box :=
  sound_of_literal_split component122Node53Box leaf6143Box leaf6144Box
    .k (125/32) (by rfl) (by rfl)
    leaf6143FlatSound leaf6144FlatSound

private noncomputable def component122Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (63/128), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component122Node54_sound : Sound component122Node54Box :=
  sound_of_literal_split component122Node54Box leaf6145Box leaf6146Box
    .k (125/32) (by rfl) (by rfl)
    leaf6145FlatSound leaf6146FlatSound

private noncomputable def component122Node55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (31/64), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component122Node55_sound : Sound component122Node55Box :=
  sound_of_literal_split component122Node55Box component122Node53Box component122Node54Box
    .chi (63/128) (by rfl) (by rfl)
    component122Node53_sound component122Node54_sound

private noncomputable def component122Node56Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (31/64), chiHi := (63/128) }

set_option maxRecDepth 1000000 in
private theorem component122Node56_sound : Sound component122Node56Box :=
  sound_of_literal_split component122Node56Box leaf6147Box leaf6148Box
    .k (127/32) (by rfl) (by rfl)
    leaf6147FlatSound leaf6148FlatSound

private noncomputable def component122Node57Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (63/128), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component122Node57_sound : Sound component122Node57Box :=
  sound_of_literal_split component122Node57Box leaf6149Box leaf6150Box
    .k (127/32) (by rfl) (by rfl)
    leaf6149FlatSound leaf6150FlatSound

private noncomputable def component122Node58Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (31/64), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component122Node58_sound : Sound component122Node58Box :=
  sound_of_literal_split component122Node58Box component122Node56Box component122Node57Box
    .chi (63/128) (by rfl) (by rfl)
    component122Node56_sound component122Node57_sound

private noncomputable def component122Node59Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (31/64), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component122Node59_sound : Sound component122Node59Box :=
  sound_of_literal_split component122Node59Box component122Node55Box component122Node58Box
    .k (63/16) (by rfl) (by rfl)
    component122Node55_sound component122Node58_sound

private noncomputable def component122Node60Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (15/32), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component122Node60_sound : Sound component122Node60Box :=
  sound_of_literal_split component122Node60Box component122Node52Box component122Node59Box
    .chi (31/64) (by rfl) (by rfl)
    component122Node52_sound component122Node59_sound

private noncomputable def component122Node61Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (4), chiLo := (15/32), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component122Node61_sound : Sound component122Node61Box :=
  sound_of_literal_split component122Node61Box component122Node45Box component122Node60Box
    .k (31/8) (by rfl) (by rfl)
    component122Node45_sound component122Node60_sound

noncomputable def component122Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (4), chiLo := (7/16), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
theorem component122_sound : Sound component122Box :=
  sound_of_literal_split component122Box component122Node30Box component122Node61Box
    .chi (15/32) (by rfl) (by rfl)
    component122Node30_sound component122Node61_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
