import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch6
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheSKBatch3

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

private noncomputable def leaf2687Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (233/64), chiLo := (5/32), chiHi := (41/256) }

private noncomputable def leaf2687Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742371/1073741824) }, vSqrt := { lower := (8191/8192), upper := (2694841605/2694785536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1681845471/1073741824) }, upper := { exponent := 0, mantissa := (25937/16384) } }, logOuter := sk217LogOuterCertificate, logK := sk217LogKCertificate, logChi := chi183LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (5389627141/5389571072) } }, logDArg := sk217LogDArgCertificate }

private noncomputable def leaf2687InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2687LocalValidity :
    LeafFacts leaf2687Box leaf2687Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2687Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (2694841605/2694785536) }) = true
      norm_num [leaf2687Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2687CertificateValid :
    WideCertificateValid leaf2687Box leaf2687Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk217ValidityFacts chi183ValidityFacts
    leaf2687LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2687CoverageChecked :
    coverageCheck (innerAD leaf2687Box) leaf2687InnerLog = true := by
  rfl'

private theorem leaf2687InnerLogValid :
    leaf2687InnerLog.Valid 8 (innerAD leaf2687Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2687CoverageChecked

private noncomputable def leaf2687InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629255/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2687InputLogOnePlusV_eq :
    leaf2687InputLogOnePlusV = outerEnclosure 24
      (leaf2687Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2687RoundedFacts : LeafRoundedFacts 8
    leaf2687Certificate.logOnePlusV leaf2687InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2687InputLogOnePlusV_eq }

private noncomputable def leaf2687Inputs : Inputs :=
  inputsOfCaches globalInput sk217RoundedInputs
    chi183InputQChi innerPair50Input
    leaf2687InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2687LowerChecked :
    lowerCheck 24 leaf2687Box leaf2687Inputs = true := by
  rfl'

private theorem leaf2687CoversExact : CoversExact 8
    leaf2687Box leaf2687Certificate leaf2687InnerLog leaf2687Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk217RoundedFacts chi183RoundedFacts
    innerPair50RoundedFacts leaf2687RoundedFacts (by rfl)

private theorem leaf2687FlatSound : Sound leaf2687Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2687CertificateValid
    leaf2687InnerLogValid leaf2687CoversExact leaf2687LowerChecked

private noncomputable def leaf2688Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (233/64), kHi := (117/32), chiLo := (5/32), chiHi := (41/256) }

private noncomputable def leaf2688Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742373/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434041344) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1684466749/1073741824) }, upper := { exponent := 0, mantissa := (12989/8192) } }, logOuter := sk218LogOuterCertificate, logK := sk218LogKCertificate, logChi := chi183LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870963199/274868082688) } }, logDArg := sk218LogDArgCertificate }

private noncomputable def leaf2688InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2688LocalValidity :
    LeafFacts leaf2688Box leaf2688Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2688Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434041344) }) = true
      norm_num [leaf2688Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2688CertificateValid :
    WideCertificateValid leaf2688Box leaf2688Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk218ValidityFacts chi183ValidityFacts
    leaf2688LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2688CoverageChecked :
    coverageCheck (innerAD leaf2688Box) leaf2688InnerLog = true := by
  rfl'

private theorem leaf2688InnerLogValid :
    leaf2688InnerLog.Valid 8 (innerAD leaf2688Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2688CoverageChecked

private noncomputable def leaf2688InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629257/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2688InputLogOnePlusV_eq :
    leaf2688InputLogOnePlusV = outerEnclosure 24
      (leaf2688Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2688RoundedFacts : LeafRoundedFacts 8
    leaf2688Certificate.logOnePlusV leaf2688InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2688InputLogOnePlusV_eq }

private noncomputable def leaf2688Inputs : Inputs :=
  inputsOfCaches globalInput sk218RoundedInputs
    chi183InputQChi innerPair50Input
    leaf2688InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2688LowerChecked :
    lowerCheck 24 leaf2688Box leaf2688Inputs = true := by
  rfl'

private theorem leaf2688CoversExact : CoversExact 8
    leaf2688Box leaf2688Certificate leaf2688InnerLog leaf2688Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk218RoundedFacts chi183RoundedFacts
    innerPair50RoundedFacts leaf2688RoundedFacts (by rfl)

private theorem leaf2688FlatSound : Sound leaf2688Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2688CertificateValid
    leaf2688InnerLogValid leaf2688CoversExact leaf2688LowerChecked

private noncomputable def leaf2689Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (233/64), chiLo := (41/256), chiHi := (21/128) }

private noncomputable def leaf2689Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742373/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486788608) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1697048893/1073741824) }, upper := { exponent := 0, mantissa := (13085/8192) } }, logOuter := sk217LogOuterCertificate, logK := sk217LogKCertificate, logChi := chi184LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54974172979/54973577216) } }, logDArg := sk217LogDArgCertificate }

private noncomputable def leaf2689InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2689LocalValidity :
    LeafFacts leaf2689Box leaf2689Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2689Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486788608) }) = true
      norm_num [leaf2689Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2689CertificateValid :
    WideCertificateValid leaf2689Box leaf2689Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk217ValidityFacts chi184ValidityFacts
    leaf2689LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2689CoverageChecked :
    coverageCheck (innerAD leaf2689Box) leaf2689InnerLog = true := by
  rfl'

private theorem leaf2689InnerLogValid :
    leaf2689InnerLog.Valid 8 (innerAD leaf2689Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2689CoverageChecked

private noncomputable def leaf2689InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629263/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2689InputLogOnePlusV_eq :
    leaf2689InputLogOnePlusV = outerEnclosure 24
      (leaf2689Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2689RoundedFacts : LeafRoundedFacts 8
    leaf2689Certificate.logOnePlusV leaf2689InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2689InputLogOnePlusV_eq }

private noncomputable def leaf2689Inputs : Inputs :=
  inputsOfCaches globalInput sk217RoundedInputs
    chi184InputQChi innerPair50Input
    leaf2689InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2689LowerChecked :
    lowerCheck 24 leaf2689Box leaf2689Inputs = true := by
  rfl'

private theorem leaf2689CoversExact : CoversExact 8
    leaf2689Box leaf2689Certificate leaf2689InnerLog leaf2689Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk217RoundedFacts chi184RoundedFacts
    innerPair50RoundedFacts leaf2689RoundedFacts (by rfl)

private theorem leaf2689FlatSound : Sound leaf2689Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2689CertificateValid
    leaf2689InnerLogValid leaf2689CoversExact leaf2689LowerChecked

private noncomputable def leaf2690Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (233/64), kHi := (117/32), chiLo := (41/256), chiHi := (21/128) }

private noncomputable def leaf2690Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742375/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433921536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1699735703/1073741824) }, upper := { exponent := 0, mantissa := (6553/4096) } }, logOuter := sk218LogOuterCertificate, logK := sk218LogKCertificate, logChi := chi184LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870843391/274867843072) } }, logDArg := sk218LogDArgCertificate }

private noncomputable def leaf2690InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2690LocalValidity :
    LeafFacts leaf2690Box leaf2690Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2690Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433921536) }) = true
      norm_num [leaf2690Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2690CertificateValid :
    WideCertificateValid leaf2690Box leaf2690Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk218ValidityFacts chi184ValidityFacts
    leaf2690LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2690CoverageChecked :
    coverageCheck (innerAD leaf2690Box) leaf2690InnerLog = true := by
  rfl'

private theorem leaf2690InnerLogValid :
    leaf2690InnerLog.Valid 8 (innerAD leaf2690Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2690CoverageChecked

private noncomputable def leaf2690InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726829/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf2690InputLogOnePlusV_eq :
    leaf2690InputLogOnePlusV = outerEnclosure 24
      (leaf2690Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2690RoundedFacts : LeafRoundedFacts 8
    leaf2690Certificate.logOnePlusV leaf2690InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2690InputLogOnePlusV_eq }

private noncomputable def leaf2690Inputs : Inputs :=
  inputsOfCaches globalInput sk218RoundedInputs
    chi184InputQChi innerPair50Input
    leaf2690InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2690LowerChecked :
    lowerCheck 24 leaf2690Box leaf2690Inputs = true := by
  rfl'

private theorem leaf2690CoversExact : CoversExact 8
    leaf2690Box leaf2690Certificate leaf2690InnerLog leaf2690Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk218RoundedFacts chi184RoundedFacts
    innerPair50RoundedFacts leaf2690RoundedFacts (by rfl)

private theorem leaf2690FlatSound : Sound leaf2690Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2690CertificateValid
    leaf2690InnerLogValid leaf2690CoversExact leaf2690LowerChecked

private noncomputable def leaf2691Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (235/64), chiLo := (5/32), chiHi := (41/256) }

private noncomputable def leaf2691Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742375/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434020352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1687088027/1073741824) }, upper := { exponent := 0, mantissa := (26019/16384) } }, logOuter := sk219LogOuterCertificate, logK := sk219LogKCertificate, logChi := chi183LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870942207/274868040704) } }, logDArg := sk219LogDArgCertificate }

private noncomputable def leaf2691InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2691LocalValidity :
    LeafFacts leaf2691Box leaf2691Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2691Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434020352) }) = true
      norm_num [leaf2691Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2691CertificateValid :
    WideCertificateValid leaf2691Box leaf2691Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk219ValidityFacts chi183ValidityFacts
    leaf2691LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2691CoverageChecked :
    coverageCheck (innerAD leaf2691Box) leaf2691InnerLog = true := by
  rfl'

private theorem leaf2691InnerLogValid :
    leaf2691InnerLog.Valid 8 (innerAD leaf2691Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2691CoverageChecked

private noncomputable def leaf2691InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814629/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2691InputLogOnePlusV_eq :
    leaf2691InputLogOnePlusV = outerEnclosure 24
      (leaf2691Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2691RoundedFacts : LeafRoundedFacts 8
    leaf2691Certificate.logOnePlusV leaf2691InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2691InputLogOnePlusV_eq }

private noncomputable def leaf2691Inputs : Inputs :=
  inputsOfCaches globalInput sk219RoundedInputs
    chi183InputQChi innerPair50Input
    leaf2691InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2691LowerChecked :
    lowerCheck 24 leaf2691Box leaf2691Inputs = true := by
  rfl'

private theorem leaf2691CoversExact : CoversExact 8
    leaf2691Box leaf2691Certificate leaf2691InnerLog leaf2691Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk219RoundedFacts chi183RoundedFacts
    innerPair50RoundedFacts leaf2691RoundedFacts (by rfl)

private theorem leaf2691FlatSound : Sound leaf2691Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2691CertificateValid
    leaf2691InnerLogValid leaf2691CoversExact leaf2691LowerChecked

private noncomputable def leaf2692Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (235/64), kHi := (59/16), chiLo := (5/32), chiHi := (41/256) }

private noncomputable def leaf2692Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742377/1073741824) }, vSqrt := { lower := (8191/8192), upper := (213080499/213075968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1689709305/1073741824) }, upper := { exponent := 0, mantissa := (6515/4096) } }, logOuter := sk220LogOuterCertificate, logK := sk220LogKCertificate, logChi := chi183LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (426156467/426151936) } }, logDArg := sk220LogDArgCertificate }

private noncomputable def leaf2692InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2692LocalValidity :
    LeafFacts leaf2692Box leaf2692Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2692Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (213080499/213075968) }) = true
      norm_num [leaf2692Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2692CertificateValid :
    WideCertificateValid leaf2692Box leaf2692Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk220ValidityFacts chi183ValidityFacts
    leaf2692LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2692CoverageChecked :
    coverageCheck (innerAD leaf2692Box) leaf2692InnerLog = true := by
  rfl'

private theorem leaf2692InnerLogValid :
    leaf2692InnerLog.Valid 8 (innerAD leaf2692Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2692CoverageChecked

private noncomputable def leaf2692InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629259/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2692InputLogOnePlusV_eq :
    leaf2692InputLogOnePlusV = outerEnclosure 24
      (leaf2692Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2692RoundedFacts : LeafRoundedFacts 8
    leaf2692Certificate.logOnePlusV leaf2692InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2692InputLogOnePlusV_eq }

private noncomputable def leaf2692Inputs : Inputs :=
  inputsOfCaches globalInput sk220RoundedInputs
    chi183InputQChi innerPair50Input
    leaf2692InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2692LowerChecked :
    lowerCheck 24 leaf2692Box leaf2692Inputs = true := by
  rfl'

private theorem leaf2692CoversExact : CoversExact 8
    leaf2692Box leaf2692Certificate leaf2692InnerLog leaf2692Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk220RoundedFacts chi183RoundedFacts
    innerPair50RoundedFacts leaf2692RoundedFacts (by rfl)

private theorem leaf2692FlatSound : Sound leaf2692Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2692CertificateValid
    leaf2692InnerLogValid leaf2692CoversExact leaf2692LowerChecked

private noncomputable def leaf2693Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (235/64), chiLo := (41/256), chiHi := (21/128) }

private noncomputable def leaf2693Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742377/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433900032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1702422513/1073741824) }, upper := { exponent := 0, mantissa := (13127/8192) } }, logOuter := sk219LogOuterCertificate, logK := sk219LogKCertificate, logChi := chi184LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870821887/274867800064) } }, logDArg := sk219LogDArgCertificate }

private noncomputable def leaf2693InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2693LocalValidity :
    LeafFacts leaf2693Box leaf2693Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2693Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433900032) }) = true
      norm_num [leaf2693Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2693CertificateValid :
    WideCertificateValid leaf2693Box leaf2693Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk219ValidityFacts chi184ValidityFacts
    leaf2693LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2693CoverageChecked :
    coverageCheck (innerAD leaf2693Box) leaf2693InnerLog = true := by
  rfl'

private theorem leaf2693InnerLogValid :
    leaf2693InnerLog.Valid 8 (innerAD leaf2693Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2693CoverageChecked

private noncomputable def leaf2693InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629265/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2693InputLogOnePlusV_eq :
    leaf2693InputLogOnePlusV = outerEnclosure 24
      (leaf2693Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2693RoundedFacts : LeafRoundedFacts 8
    leaf2693Certificate.logOnePlusV leaf2693InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2693InputLogOnePlusV_eq }

private noncomputable def leaf2693Inputs : Inputs :=
  inputsOfCaches globalInput sk219RoundedInputs
    chi184InputQChi innerPair50Input
    leaf2693InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2693LowerChecked :
    lowerCheck 24 leaf2693Box leaf2693Inputs = true := by
  rfl'

private theorem leaf2693CoversExact : CoversExact 8
    leaf2693Box leaf2693Certificate leaf2693InnerLog leaf2693Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk219RoundedFacts chi184RoundedFacts
    innerPair50RoundedFacts leaf2693RoundedFacts (by rfl)

private theorem leaf2693FlatSound : Sound leaf2693Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2693CertificateValid
    leaf2693InnerLogValid leaf2693CoversExact leaf2693LowerChecked

private noncomputable def leaf2694Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (235/64), kHi := (59/16), chiLo := (41/256), chiHi := (21/128) }

private noncomputable def leaf2694Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742379/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433878528) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1705109323/1073741824) }, upper := { exponent := 0, mantissa := (3287/2048) } }, logOuter := sk220LogOuterCertificate, logK := sk220LogKCertificate, logChi := chi184LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870800383/274867757056) } }, logDArg := sk220LogDArgCertificate }

private noncomputable def leaf2694InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2694LocalValidity :
    LeafFacts leaf2694Box leaf2694Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2694Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433878528) }) = true
      norm_num [leaf2694Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2694CertificateValid :
    WideCertificateValid leaf2694Box leaf2694Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk220ValidityFacts chi184ValidityFacts
    leaf2694LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2694CoverageChecked :
    coverageCheck (innerAD leaf2694Box) leaf2694InnerLog = true := by
  rfl'

private theorem leaf2694InnerLogValid :
    leaf2694InnerLog.Valid 8 (innerAD leaf2694Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2694CoverageChecked

private noncomputable def leaf2694InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814633/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2694InputLogOnePlusV_eq :
    leaf2694InputLogOnePlusV = outerEnclosure 24
      (leaf2694Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2694RoundedFacts : LeafRoundedFacts 8
    leaf2694Certificate.logOnePlusV leaf2694InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2694InputLogOnePlusV_eq }

private noncomputable def leaf2694Inputs : Inputs :=
  inputsOfCaches globalInput sk220RoundedInputs
    chi184InputQChi innerPair50Input
    leaf2694InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2694LowerChecked :
    lowerCheck 24 leaf2694Box leaf2694Inputs = true := by
  rfl'

private theorem leaf2694CoversExact : CoversExact 8
    leaf2694Box leaf2694Certificate leaf2694InnerLog leaf2694Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk220RoundedFacts chi184RoundedFacts
    innerPair50RoundedFacts leaf2694RoundedFacts (by rfl)

private theorem leaf2694FlatSound : Sound leaf2694Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2694CertificateValid
    leaf2694InnerLogValid leaf2694CoversExact leaf2694LowerChecked

private noncomputable def leaf2695Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (233/64), chiLo := (21/128), chiHi := (43/256) }

private noncomputable def leaf2695Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742375/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433823744) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1712252315/1073741824) }, upper := { exponent := 0, mantissa := (26403/16384) } }, logOuter := sk217LogOuterCertificate, logK := sk217LogKCertificate, logChi := chi185LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870745599/274867647488) } }, logDArg := sk217LogDArgCertificate }

private noncomputable def leaf2695InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2695LocalValidity :
    LeafFacts leaf2695Box leaf2695Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2695Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433823744) }) = true
      norm_num [leaf2695Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2695CertificateValid :
    WideCertificateValid leaf2695Box leaf2695Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk217ValidityFacts chi185ValidityFacts
    leaf2695LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2695CoverageChecked :
    coverageCheck (innerAD leaf2695Box) leaf2695InnerLog = true := by
  rfl'

private theorem leaf2695InnerLogValid :
    leaf2695InnerLog.Valid 8 (innerAD leaf2695Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2695CoverageChecked

private noncomputable def leaf2695InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814635/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2695InputLogOnePlusV_eq :
    leaf2695InputLogOnePlusV = outerEnclosure 24
      (leaf2695Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2695RoundedFacts : LeafRoundedFacts 8
    leaf2695Certificate.logOnePlusV leaf2695InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2695InputLogOnePlusV_eq }

private noncomputable def leaf2695Inputs : Inputs :=
  inputsOfCaches globalInput sk217RoundedInputs
    chi185InputQChi innerPair50Input
    leaf2695InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2695LowerChecked :
    lowerCheck 24 leaf2695Box leaf2695Inputs = true := by
  rfl'

private theorem leaf2695CoversExact : CoversExact 8
    leaf2695Box leaf2695Certificate leaf2695InnerLog leaf2695Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk217RoundedFacts chi185RoundedFacts
    innerPair50RoundedFacts leaf2695RoundedFacts (by rfl)

private theorem leaf2695FlatSound : Sound leaf2695Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2695CertificateValid
    leaf2695InnerLogValid leaf2695CoversExact leaf2695LowerChecked

private noncomputable def leaf2696Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (233/64), kHi := (117/32), chiLo := (21/128), chiHi := (43/256) }

private noncomputable def leaf2696Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742377/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433801728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1715004657/1073741824) }, upper := { exponent := 0, mantissa := (13223/8192) } }, logOuter := sk218LogOuterCertificate, logK := sk218LogKCertificate, logChi := chi185LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870723583/274867603456) } }, logDArg := sk218LogDArgCertificate }

private noncomputable def leaf2696InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2696LocalValidity :
    LeafFacts leaf2696Box leaf2696Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2696Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433801728) }) = true
      norm_num [leaf2696Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2696CertificateValid :
    WideCertificateValid leaf2696Box leaf2696Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk218ValidityFacts chi185ValidityFacts
    leaf2696LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2696CoverageChecked :
    coverageCheck (innerAD leaf2696Box) leaf2696InnerLog = true := by
  rfl'

private theorem leaf2696InnerLogValid :
    leaf2696InnerLog.Valid 8 (innerAD leaf2696Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2696CoverageChecked

private noncomputable def leaf2696InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629271/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2696InputLogOnePlusV_eq :
    leaf2696InputLogOnePlusV = outerEnclosure 24
      (leaf2696Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2696RoundedFacts : LeafRoundedFacts 8
    leaf2696Certificate.logOnePlusV leaf2696InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2696InputLogOnePlusV_eq }

private noncomputable def leaf2696Inputs : Inputs :=
  inputsOfCaches globalInput sk218RoundedInputs
    chi185InputQChi innerPair50Input
    leaf2696InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2696LowerChecked :
    lowerCheck 24 leaf2696Box leaf2696Inputs = true := by
  rfl'

private theorem leaf2696CoversExact : CoversExact 8
    leaf2696Box leaf2696Certificate leaf2696InnerLog leaf2696Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk218RoundedFacts chi185RoundedFacts
    innerPair50RoundedFacts leaf2696RoundedFacts (by rfl)

private theorem leaf2696FlatSound : Sound leaf2696Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2696CertificateValid
    leaf2696InnerLogValid leaf2696CoversExact leaf2696LowerChecked

private noncomputable def leaf2697Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (233/64), chiLo := (43/256), chiHi := (11/64) }

private noncomputable def leaf2697Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742377/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45811234816) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1727455737/1073741824) }, upper := { exponent := 0, mantissa := (6659/4096) } }, logOuter := sk217LogOuterCertificate, logK := sk217LogKCertificate, logChi := chi186LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623542101/91622469632) } }, logDArg := sk217LogDArgCertificate }

private noncomputable def leaf2697InnerLog : WideLogData :=
  innerPair157Data

set_option maxRecDepth 1000000 in
private theorem leaf2697LocalValidity :
    LeafFacts leaf2697Box leaf2697Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2697Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45811234816) }) = true
      norm_num [leaf2697Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2697CertificateValid :
    WideCertificateValid leaf2697Box leaf2697Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk217ValidityFacts chi186ValidityFacts
    leaf2697LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2697CoverageChecked :
    coverageCheck (innerAD leaf2697Box) leaf2697InnerLog = true := by
  rfl'

private theorem leaf2697InnerLogValid :
    leaf2697InnerLog.Valid 8 (innerAD leaf2697Box) :=
  wideLogDataValid_of_cachedCheck endpoint44PositiveFacts
    endpoint45PositiveFacts.valid leaf2697CoverageChecked

private noncomputable def leaf2697InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629277/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2697InputLogOnePlusV_eq :
    leaf2697InputLogOnePlusV = outerEnclosure 24
      (leaf2697Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2697RoundedFacts : LeafRoundedFacts 8
    leaf2697Certificate.logOnePlusV leaf2697InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2697InputLogOnePlusV_eq }

private noncomputable def leaf2697Inputs : Inputs :=
  inputsOfCaches globalInput sk217RoundedInputs
    chi186InputQChi innerPair157Input
    leaf2697InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2697LowerChecked :
    lowerCheck 24 leaf2697Box leaf2697Inputs = true := by
  rfl'

private theorem leaf2697CoversExact : CoversExact 8
    leaf2697Box leaf2697Certificate leaf2697InnerLog leaf2697Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk217RoundedFacts chi186RoundedFacts
    innerPair157RoundedFacts leaf2697RoundedFacts (by rfl)

private theorem leaf2697FlatSound : Sound leaf2697Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2697CertificateValid
    leaf2697InnerLogValid leaf2697CoversExact leaf2697LowerChecked

private noncomputable def leaf2698Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (233/64), kHi := (117/32), chiLo := (43/256), chiHi := (11/64) }

private noncomputable def leaf2698Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742379/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486736384) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1730273611/1073741824) }, upper := { exponent := 0, mantissa := (3335/2048) } }, logOuter := sk218LogOuterCertificate, logK := sk218LogKCertificate, logChi := chi186LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54974120755/54973472768) } }, logDArg := sk218LogDArgCertificate }

private noncomputable def leaf2698InnerLog : WideLogData :=
  innerPair166Data

set_option maxRecDepth 1000000 in
private theorem leaf2698LocalValidity :
    LeafFacts leaf2698Box leaf2698Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2698Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486736384) }) = true
      norm_num [leaf2698Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2698CertificateValid :
    WideCertificateValid leaf2698Box leaf2698Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk218ValidityFacts chi186ValidityFacts
    leaf2698LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2698CoverageChecked :
    coverageCheck (innerAD leaf2698Box) leaf2698InnerLog = true := by
  rfl'

private theorem leaf2698InnerLogValid :
    leaf2698InnerLog.Valid 8 (innerAD leaf2698Box) :=
  wideLogDataValid_of_cachedCheck endpoint46PositiveFacts
    endpoint45PositiveFacts.valid leaf2698CoverageChecked

private noncomputable def leaf2698InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814639/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2698InputLogOnePlusV_eq :
    leaf2698InputLogOnePlusV = outerEnclosure 24
      (leaf2698Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2698RoundedFacts : LeafRoundedFacts 8
    leaf2698Certificate.logOnePlusV leaf2698InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2698InputLogOnePlusV_eq }

private noncomputable def leaf2698Inputs : Inputs :=
  inputsOfCaches globalInput sk218RoundedInputs
    chi186InputQChi innerPair166Input
    leaf2698InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2698LowerChecked :
    lowerCheck 24 leaf2698Box leaf2698Inputs = true := by
  rfl'

private theorem leaf2698CoversExact : CoversExact 8
    leaf2698Box leaf2698Certificate leaf2698InnerLog leaf2698Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk218RoundedFacts chi186RoundedFacts
    innerPair166RoundedFacts leaf2698RoundedFacts (by rfl)

private theorem leaf2698FlatSound : Sound leaf2698Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2698CertificateValid
    leaf2698InnerLogValid leaf2698CoversExact leaf2698LowerChecked

private noncomputable def leaf2699Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (235/64), chiLo := (21/128), chiHi := (43/256) }

private noncomputable def leaf2699Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742379/1073741824) }, vSqrt := { lower := (8191/8192), upper := (15270769095/15270419968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1717756999/1073741824) }, upper := { exponent := 0, mantissa := (26489/16384) } }, logOuter := sk219LogOuterCertificate, logK := sk219LogKCertificate, logChi := chi185LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (30541189063/30540839936) } }, logDArg := sk219LogDArgCertificate }

private noncomputable def leaf2699InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2699LocalValidity :
    LeafFacts leaf2699Box leaf2699Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2699Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (15270769095/15270419968) }) = true
      norm_num [leaf2699Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2699CertificateValid :
    WideCertificateValid leaf2699Box leaf2699Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk219ValidityFacts chi185ValidityFacts
    leaf2699LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2699CoverageChecked :
    coverageCheck (innerAD leaf2699Box) leaf2699InnerLog = true := by
  rfl'

private theorem leaf2699InnerLogValid :
    leaf2699InnerLog.Valid 8 (innerAD leaf2699Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2699CoverageChecked

private noncomputable def leaf2699InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629273/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2699InputLogOnePlusV_eq :
    leaf2699InputLogOnePlusV = outerEnclosure 24
      (leaf2699Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2699RoundedFacts : LeafRoundedFacts 8
    leaf2699Certificate.logOnePlusV leaf2699InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2699InputLogOnePlusV_eq }

private noncomputable def leaf2699Inputs : Inputs :=
  inputsOfCaches globalInput sk219RoundedInputs
    chi185InputQChi innerPair50Input
    leaf2699InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2699LowerChecked :
    lowerCheck 24 leaf2699Box leaf2699Inputs = true := by
  rfl'

private theorem leaf2699CoversExact : CoversExact 8
    leaf2699Box leaf2699Certificate leaf2699InnerLog leaf2699Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk219RoundedFacts chi185RoundedFacts
    innerPair50RoundedFacts leaf2699RoundedFacts (by rfl)

private theorem leaf2699FlatSound : Sound leaf2699Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2699CertificateValid
    leaf2699InnerLogValid leaf2699CoversExact leaf2699LowerChecked

private noncomputable def leaf2700Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (235/64), kHi := (59/16), chiLo := (21/128), chiHi := (43/256) }

private noncomputable def leaf2700Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742381/1073741824) }, vSqrt := { lower := (8191/8192), upper := (8084524815/8084338688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1720509341/1073741824) }, upper := { exponent := 0, mantissa := (6633/4096) } }, logOuter := sk220LogOuterCertificate, logK := sk220LogKCertificate, logChi := chi185LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16168863503/16168677376) } }, logDArg := sk220LogDArgCertificate }

private noncomputable def leaf2700InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2700LocalValidity :
    LeafFacts leaf2700Box leaf2700Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2700Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8084524815/8084338688) }) = true
      norm_num [leaf2700Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2700CertificateValid :
    WideCertificateValid leaf2700Box leaf2700Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk220ValidityFacts chi185ValidityFacts
    leaf2700LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2700CoverageChecked :
    coverageCheck (innerAD leaf2700Box) leaf2700InnerLog = true := by
  rfl'

private theorem leaf2700InnerLogValid :
    leaf2700InnerLog.Valid 8 (innerAD leaf2700Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2700CoverageChecked

private noncomputable def leaf2700InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814637/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2700InputLogOnePlusV_eq :
    leaf2700InputLogOnePlusV = outerEnclosure 24
      (leaf2700Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2700RoundedFacts : LeafRoundedFacts 8
    leaf2700Certificate.logOnePlusV leaf2700InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2700InputLogOnePlusV_eq }

private noncomputable def leaf2700Inputs : Inputs :=
  inputsOfCaches globalInput sk220RoundedInputs
    chi185InputQChi innerPair50Input
    leaf2700InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2700LowerChecked :
    lowerCheck 24 leaf2700Box leaf2700Inputs = true := by
  rfl'

private theorem leaf2700CoversExact : CoversExact 8
    leaf2700Box leaf2700Certificate leaf2700InnerLog leaf2700Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk220RoundedFacts chi185RoundedFacts
    innerPair50RoundedFacts leaf2700RoundedFacts (by rfl)

private theorem leaf2700FlatSound : Sound leaf2700Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2700CertificateValid
    leaf2700InnerLogValid leaf2700CoversExact leaf2700LowerChecked

private noncomputable def leaf2701Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (235/64), chiLo := (43/256), chiHi := (11/64) }

private noncomputable def leaf2701Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742381/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433659392) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1733091485/1073741824) }, upper := { exponent := 0, mantissa := (6681/4096) } }, logOuter := sk219LogOuterCertificate, logK := sk219LogKCertificate, logChi := chi186LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870581247/274867318784) } }, logDArg := sk219LogDArgCertificate }

private noncomputable def leaf2701InnerLog : WideLogData :=
  innerPair166Data

set_option maxRecDepth 1000000 in
private theorem leaf2701LocalValidity :
    LeafFacts leaf2701Box leaf2701Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2701Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433659392) }) = true
      norm_num [leaf2701Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2701CertificateValid :
    WideCertificateValid leaf2701Box leaf2701Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk219ValidityFacts chi186ValidityFacts
    leaf2701LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2701CoverageChecked :
    coverageCheck (innerAD leaf2701Box) leaf2701InnerLog = true := by
  rfl'

private theorem leaf2701InnerLogValid :
    leaf2701InnerLog.Valid 8 (innerAD leaf2701Box) :=
  wideLogDataValid_of_cachedCheck endpoint46PositiveFacts
    endpoint45PositiveFacts.valid leaf2701CoverageChecked

private noncomputable def leaf2701InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (363415/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf2701InputLogOnePlusV_eq :
    leaf2701InputLogOnePlusV = outerEnclosure 24
      (leaf2701Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2701RoundedFacts : LeafRoundedFacts 8
    leaf2701Certificate.logOnePlusV leaf2701InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2701InputLogOnePlusV_eq }

private noncomputable def leaf2701Inputs : Inputs :=
  inputsOfCaches globalInput sk219RoundedInputs
    chi186InputQChi innerPair166Input
    leaf2701InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2701LowerChecked :
    lowerCheck 24 leaf2701Box leaf2701Inputs = true := by
  rfl'

private theorem leaf2701CoversExact : CoversExact 8
    leaf2701Box leaf2701Certificate leaf2701InnerLog leaf2701Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk219RoundedFacts chi186RoundedFacts
    innerPair166RoundedFacts leaf2701RoundedFacts (by rfl)

private theorem leaf2701FlatSound : Sound leaf2701Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2701CertificateValid
    leaf2701InnerLogValid leaf2701CoversExact leaf2701LowerChecked

private noncomputable def leaf2702Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (235/64), kHi := (59/16), chiLo := (43/256), chiHi := (11/64) }

private noncomputable def leaf2702Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742383/1073741824) }, vSqrt := { lower := (8191/8192), upper := (15270769095/15270404096) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1735909359/1073741824) }, upper := { exponent := 0, mantissa := (1673/1024) } }, logOuter := sk220LogOuterCertificate, logK := sk220LogKCertificate, logChi := chi186LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (30541173191/30540808192) } }, logDArg := sk220LogDArgCertificate }

private noncomputable def leaf2702InnerLog : WideLogData :=
  innerPair166Data

set_option maxRecDepth 1000000 in
private theorem leaf2702LocalValidity :
    LeafFacts leaf2702Box leaf2702Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2702Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (15270769095/15270404096) }) = true
      norm_num [leaf2702Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2702CertificateValid :
    WideCertificateValid leaf2702Box leaf2702Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk220ValidityFacts chi186ValidityFacts
    leaf2702LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2702CoverageChecked :
    coverageCheck (innerAD leaf2702Box) leaf2702InnerLog = true := by
  rfl'

private theorem leaf2702InnerLogValid :
    leaf2702InnerLog.Valid 8 (innerAD leaf2702Box) :=
  wideLogDataValid_of_cachedCheck endpoint46PositiveFacts
    endpoint45PositiveFacts.valid leaf2702CoverageChecked

private noncomputable def leaf2702InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629281/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2702InputLogOnePlusV_eq :
    leaf2702InputLogOnePlusV = outerEnclosure 24
      (leaf2702Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2702RoundedFacts : LeafRoundedFacts 8
    leaf2702Certificate.logOnePlusV leaf2702InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2702InputLogOnePlusV_eq }

private noncomputable def leaf2702Inputs : Inputs :=
  inputsOfCaches globalInput sk220RoundedInputs
    chi186InputQChi innerPair166Input
    leaf2702InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2702LowerChecked :
    lowerCheck 24 leaf2702Box leaf2702Inputs = true := by
  rfl'

private theorem leaf2702CoversExact : CoversExact 8
    leaf2702Box leaf2702Certificate leaf2702InnerLog leaf2702Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk220RoundedFacts chi186RoundedFacts
    innerPair166RoundedFacts leaf2702RoundedFacts (by rfl)

private theorem leaf2702FlatSound : Sound leaf2702Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2702CertificateValid
    leaf2702InnerLogValid leaf2702CoversExact leaf2702LowerChecked

private noncomputable def leaf2703Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (237/64), chiLo := (5/32), chiHi := (41/256) }

private noncomputable def leaf2703Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742379/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433978368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1692330583/1073741824) }, upper := { exponent := 0, mantissa := (26101/16384) } }, logOuter := sk221LogOuterCertificate, logK := sk221LogKCertificate, logChi := chi183LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870900223/274867956736) } }, logDArg := sk221LogDArgCertificate }

private noncomputable def leaf2703InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2703LocalValidity :
    LeafFacts leaf2703Box leaf2703Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2703Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433978368) }) = true
      norm_num [leaf2703Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2703CertificateValid :
    WideCertificateValid leaf2703Box leaf2703Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk221ValidityFacts chi183ValidityFacts
    leaf2703LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2703CoverageChecked :
    coverageCheck (innerAD leaf2703Box) leaf2703InnerLog = true := by
  rfl'

private theorem leaf2703InnerLogValid :
    leaf2703InnerLog.Valid 8 (innerAD leaf2703Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2703CoverageChecked

private noncomputable def leaf2703InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907315/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2703InputLogOnePlusV_eq :
    leaf2703InputLogOnePlusV = outerEnclosure 24
      (leaf2703Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2703RoundedFacts : LeafRoundedFacts 8
    leaf2703Certificate.logOnePlusV leaf2703InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2703InputLogOnePlusV_eq }

private noncomputable def leaf2703Inputs : Inputs :=
  inputsOfCaches globalInput sk221RoundedInputs
    chi183InputQChi innerPair50Input
    leaf2703InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2703LowerChecked :
    lowerCheck 24 leaf2703Box leaf2703Inputs = true := by
  rfl'

private theorem leaf2703CoversExact : CoversExact 8
    leaf2703Box leaf2703Certificate leaf2703InnerLog leaf2703Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk221RoundedFacts chi183RoundedFacts
    innerPair50RoundedFacts leaf2703RoundedFacts (by rfl)

private theorem leaf2703FlatSound : Sound leaf2703Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2703CertificateValid
    leaf2703InnerLogValid leaf2703CoversExact leaf2703LowerChecked

private noncomputable def leaf2704Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (237/64), kHi := (119/32), chiLo := (5/32), chiHi := (41/256) }

private noncomputable def leaf2704Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742381/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433957376) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1694951861/1073741824) }, upper := { exponent := 0, mantissa := (13071/8192) } }, logOuter := sk222LogOuterCertificate, logK := sk222LogKCertificate, logChi := chi183LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870879231/274867914752) } }, logDArg := sk222LogDArgCertificate }

private noncomputable def leaf2704InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2704LocalValidity :
    LeafFacts leaf2704Box leaf2704Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2704Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433957376) }) = true
      norm_num [leaf2704Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2704CertificateValid :
    WideCertificateValid leaf2704Box leaf2704Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk222ValidityFacts chi183ValidityFacts
    leaf2704LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2704CoverageChecked :
    coverageCheck (innerAD leaf2704Box) leaf2704InnerLog = true := by
  rfl'

private theorem leaf2704InnerLogValid :
    leaf2704InnerLog.Valid 8 (innerAD leaf2704Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2704CoverageChecked

private noncomputable def leaf2704InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814631/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2704InputLogOnePlusV_eq :
    leaf2704InputLogOnePlusV = outerEnclosure 24
      (leaf2704Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2704RoundedFacts : LeafRoundedFacts 8
    leaf2704Certificate.logOnePlusV leaf2704InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2704InputLogOnePlusV_eq }

private noncomputable def leaf2704Inputs : Inputs :=
  inputsOfCaches globalInput sk222RoundedInputs
    chi183InputQChi innerPair50Input
    leaf2704InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2704LowerChecked :
    lowerCheck 24 leaf2704Box leaf2704Inputs = true := by
  rfl'

private theorem leaf2704CoversExact : CoversExact 8
    leaf2704Box leaf2704Certificate leaf2704InnerLog leaf2704Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk222RoundedFacts chi183RoundedFacts
    innerPair50RoundedFacts leaf2704RoundedFacts (by rfl)

private theorem leaf2704FlatSound : Sound leaf2704Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2704CertificateValid
    leaf2704InnerLogValid leaf2704CoversExact leaf2704LowerChecked

private noncomputable def leaf2705Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (237/64), chiLo := (41/256), chiHi := (21/128) }

private noncomputable def leaf2705Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742381/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433857024) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1707796133/1073741824) }, upper := { exponent := 0, mantissa := (13169/8192) } }, logOuter := sk221LogOuterCertificate, logK := sk221LogKCertificate, logChi := chi184LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870778879/274867714048) } }, logDArg := sk221LogDArgCertificate }

private noncomputable def leaf2705InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2705LocalValidity :
    LeafFacts leaf2705Box leaf2705Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2705Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433857024) }) = true
      norm_num [leaf2705Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2705CertificateValid :
    WideCertificateValid leaf2705Box leaf2705Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk221ValidityFacts chi184ValidityFacts
    leaf2705LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2705CoverageChecked :
    coverageCheck (innerAD leaf2705Box) leaf2705InnerLog = true := by
  rfl'

private theorem leaf2705InnerLogValid :
    leaf2705InnerLog.Valid 8 (innerAD leaf2705Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2705CoverageChecked

private noncomputable def leaf2705InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907317/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2705InputLogOnePlusV_eq :
    leaf2705InputLogOnePlusV = outerEnclosure 24
      (leaf2705Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2705RoundedFacts : LeafRoundedFacts 8
    leaf2705Certificate.logOnePlusV leaf2705InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2705InputLogOnePlusV_eq }

private noncomputable def leaf2705Inputs : Inputs :=
  inputsOfCaches globalInput sk221RoundedInputs
    chi184InputQChi innerPair50Input
    leaf2705InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2705LowerChecked :
    lowerCheck 24 leaf2705Box leaf2705Inputs = true := by
  rfl'

private theorem leaf2705CoversExact : CoversExact 8
    leaf2705Box leaf2705Certificate leaf2705InnerLog leaf2705Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk221RoundedFacts chi184RoundedFacts
    innerPair50RoundedFacts leaf2705RoundedFacts (by rfl)

private theorem leaf2705FlatSound : Sound leaf2705Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2705CertificateValid
    leaf2705InnerLogValid leaf2705CoversExact leaf2705LowerChecked

private noncomputable def leaf2706Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (237/64), kHi := (119/32), chiLo := (41/256), chiHi := (21/128) }

private noncomputable def leaf2706Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742383/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486767104) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1710482943/1073741824) }, upper := { exponent := 0, mantissa := (6595/4096) } }, logOuter := sk222LogOuterCertificate, logK := sk222LogKCertificate, logChi := chi184LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54974151475/54973534208) } }, logDArg := sk222LogDArgCertificate }

private noncomputable def leaf2706InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2706LocalValidity :
    LeafFacts leaf2706Box leaf2706Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2706Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486767104) }) = true
      norm_num [leaf2706Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2706CertificateValid :
    WideCertificateValid leaf2706Box leaf2706Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk222ValidityFacts chi184ValidityFacts
    leaf2706LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2706CoverageChecked :
    coverageCheck (innerAD leaf2706Box) leaf2706InnerLog = true := by
  rfl'

private theorem leaf2706InnerLogValid :
    leaf2706InnerLog.Valid 8 (innerAD leaf2706Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2706CoverageChecked

private noncomputable def leaf2706InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629269/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2706InputLogOnePlusV_eq :
    leaf2706InputLogOnePlusV = outerEnclosure 24
      (leaf2706Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2706RoundedFacts : LeafRoundedFacts 8
    leaf2706Certificate.logOnePlusV leaf2706InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2706InputLogOnePlusV_eq }

private noncomputable def leaf2706Inputs : Inputs :=
  inputsOfCaches globalInput sk222RoundedInputs
    chi184InputQChi innerPair50Input
    leaf2706InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2706LowerChecked :
    lowerCheck 24 leaf2706Box leaf2706Inputs = true := by
  rfl'

private theorem leaf2706CoversExact : CoversExact 8
    leaf2706Box leaf2706Certificate leaf2706InnerLog leaf2706Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk222RoundedFacts chi184RoundedFacts
    innerPair50RoundedFacts leaf2706RoundedFacts (by rfl)

private theorem leaf2706FlatSound : Sound leaf2706Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2706CertificateValid
    leaf2706InnerLogValid leaf2706CoversExact leaf2706LowerChecked

private noncomputable def leaf2707Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (239/64), chiLo := (5/32), chiHi := (41/256) }

private noncomputable def leaf2707Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742383/1073741824) }, vSqrt := { lower := (8191/8192), upper := (5090256365/5090145792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1697573139/1073741824) }, upper := { exponent := 0, mantissa := (26183/16384) } }, logOuter := sk223LogOuterCertificate, logK := sk223LogKCertificate, logChi := chi183LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (10180402157/10180291584) } }, logDArg := sk223LogDArgCertificate }

private noncomputable def leaf2707InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2707LocalValidity :
    LeafFacts leaf2707Box leaf2707Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2707Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5090256365/5090145792) }) = true
      norm_num [leaf2707Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2707CertificateValid :
    WideCertificateValid leaf2707Box leaf2707Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk223ValidityFacts chi183ValidityFacts
    leaf2707LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2707CoverageChecked :
    coverageCheck (innerAD leaf2707Box) leaf2707InnerLog = true := by
  rfl'

private theorem leaf2707InnerLogValid :
    leaf2707InnerLog.Valid 8 (innerAD leaf2707Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2707CoverageChecked

private noncomputable def leaf2707InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629263/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2707InputLogOnePlusV_eq :
    leaf2707InputLogOnePlusV = outerEnclosure 24
      (leaf2707Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2707RoundedFacts : LeafRoundedFacts 8
    leaf2707Certificate.logOnePlusV leaf2707InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2707InputLogOnePlusV_eq }

private noncomputable def leaf2707Inputs : Inputs :=
  inputsOfCaches globalInput sk223RoundedInputs
    chi183InputQChi innerPair50Input
    leaf2707InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2707LowerChecked :
    lowerCheck 24 leaf2707Box leaf2707Inputs = true := by
  rfl'

private theorem leaf2707CoversExact : CoversExact 8
    leaf2707Box leaf2707Certificate leaf2707InnerLog leaf2707Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk223RoundedFacts chi183RoundedFacts
    innerPair50RoundedFacts leaf2707RoundedFacts (by rfl)

private theorem leaf2707FlatSound : Sound leaf2707Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2707CertificateValid
    leaf2707InnerLogValid leaf2707CoversExact leaf2707LowerChecked

private noncomputable def leaf2708Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (239/64), kHi := (15/4), chiLo := (5/32), chiHi := (41/256) }

private noncomputable def leaf2708Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742385/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433915392) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1700194417/1073741824) }, upper := { exponent := 0, mantissa := (1639/1024) } }, logOuter := sk224LogOuterCertificate, logK := sk224LogKCertificate, logChi := chi183LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870837247/274867830784) } }, logDArg := sk224LogDArgCertificate }

private noncomputable def leaf2708InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2708LocalValidity :
    LeafFacts leaf2708Box leaf2708Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2708Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433915392) }) = true
      norm_num [leaf2708Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2708CertificateValid :
    WideCertificateValid leaf2708Box leaf2708Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk224ValidityFacts chi183ValidityFacts
    leaf2708LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2708CoverageChecked :
    coverageCheck (innerAD leaf2708Box) leaf2708InnerLog = true := by
  rfl'

private theorem leaf2708InnerLogValid :
    leaf2708InnerLog.Valid 8 (innerAD leaf2708Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2708CoverageChecked

private noncomputable def leaf2708InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726829/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf2708InputLogOnePlusV_eq :
    leaf2708InputLogOnePlusV = outerEnclosure 24
      (leaf2708Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2708RoundedFacts : LeafRoundedFacts 8
    leaf2708Certificate.logOnePlusV leaf2708InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2708InputLogOnePlusV_eq }

private noncomputable def leaf2708Inputs : Inputs :=
  inputsOfCaches globalInput sk224RoundedInputs
    chi183InputQChi innerPair50Input
    leaf2708InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2708LowerChecked :
    lowerCheck 24 leaf2708Box leaf2708Inputs = true := by
  rfl'

private theorem leaf2708CoversExact : CoversExact 8
    leaf2708Box leaf2708Certificate leaf2708InnerLog leaf2708Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk224RoundedFacts chi183RoundedFacts
    innerPair50RoundedFacts leaf2708RoundedFacts (by rfl)

private theorem leaf2708FlatSound : Sound leaf2708Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2708CertificateValid
    leaf2708InnerLogValid leaf2708CoversExact leaf2708LowerChecked

private noncomputable def leaf2709Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (239/64), chiLo := (41/256), chiHi := (21/128) }

private noncomputable def leaf2709Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742385/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433814016) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1713169753/1073741824) }, upper := { exponent := 0, mantissa := (13211/8192) } }, logOuter := sk223LogOuterCertificate, logK := sk223LogKCertificate, logChi := chi184LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870735871/274867628032) } }, logDArg := sk223LogDArgCertificate }

private noncomputable def leaf2709InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2709LocalValidity :
    LeafFacts leaf2709Box leaf2709Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2709Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433814016) }) = true
      norm_num [leaf2709Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2709CertificateValid :
    WideCertificateValid leaf2709Box leaf2709Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk223ValidityFacts chi184ValidityFacts
    leaf2709LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2709CoverageChecked :
    coverageCheck (innerAD leaf2709Box) leaf2709InnerLog = true := by
  rfl'

private theorem leaf2709InnerLogValid :
    leaf2709InnerLog.Valid 8 (innerAD leaf2709Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2709CoverageChecked

private noncomputable def leaf2709InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814635/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2709InputLogOnePlusV_eq :
    leaf2709InputLogOnePlusV = outerEnclosure 24
      (leaf2709Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2709RoundedFacts : LeafRoundedFacts 8
    leaf2709Certificate.logOnePlusV leaf2709InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2709InputLogOnePlusV_eq }

private noncomputable def leaf2709Inputs : Inputs :=
  inputsOfCaches globalInput sk223RoundedInputs
    chi184InputQChi innerPair50Input
    leaf2709InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2709LowerChecked :
    lowerCheck 24 leaf2709Box leaf2709Inputs = true := by
  rfl'

private theorem leaf2709CoversExact : CoversExact 8
    leaf2709Box leaf2709Certificate leaf2709InnerLog leaf2709Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk223RoundedFacts chi184RoundedFacts
    innerPair50RoundedFacts leaf2709RoundedFacts (by rfl)

private theorem leaf2709FlatSound : Sound leaf2709Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2709CertificateValid
    leaf2709InnerLogValid leaf2709CoversExact leaf2709LowerChecked

private noncomputable def leaf2710Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (239/64), kHi := (15/4), chiLo := (41/256), chiHi := (21/128) }

private noncomputable def leaf2710Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742387/1073741824) }, vSqrt := { lower := (8191/8192), upper := (8084524815/8084340736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1715856563/1073741824) }, upper := { exponent := 0, mantissa := (827/512) } }, logOuter := sk224LogOuterCertificate, logK := sk224LogKCertificate, logChi := chi184LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16168865551/16168681472) } }, logDArg := sk224LogDArgCertificate }

private noncomputable def leaf2710InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2710LocalValidity :
    LeafFacts leaf2710Box leaf2710Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2710Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8084524815/8084340736) }) = true
      norm_num [leaf2710Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2710CertificateValid :
    WideCertificateValid leaf2710Box leaf2710Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk224ValidityFacts chi184ValidityFacts
    leaf2710LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2710CoverageChecked :
    coverageCheck (innerAD leaf2710Box) leaf2710InnerLog = true := by
  rfl'

private theorem leaf2710InnerLogValid :
    leaf2710InnerLog.Valid 8 (innerAD leaf2710Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2710CoverageChecked

private noncomputable def leaf2710InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453659/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf2710InputLogOnePlusV_eq :
    leaf2710InputLogOnePlusV = outerEnclosure 24
      (leaf2710Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2710RoundedFacts : LeafRoundedFacts 8
    leaf2710Certificate.logOnePlusV leaf2710InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2710InputLogOnePlusV_eq }

private noncomputable def leaf2710Inputs : Inputs :=
  inputsOfCaches globalInput sk224RoundedInputs
    chi184InputQChi innerPair50Input
    leaf2710InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2710LowerChecked :
    lowerCheck 24 leaf2710Box leaf2710Inputs = true := by
  rfl'

private theorem leaf2710CoversExact : CoversExact 8
    leaf2710Box leaf2710Certificate leaf2710InnerLog leaf2710Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk224RoundedFacts chi184RoundedFacts
    innerPair50RoundedFacts leaf2710RoundedFacts (by rfl)

private theorem leaf2710FlatSound : Sound leaf2710Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2710CertificateValid
    leaf2710InnerLogValid leaf2710CoversExact leaf2710LowerChecked

private noncomputable def leaf2711Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (237/64), chiLo := (21/128), chiHi := (43/256) }

private noncomputable def leaf2711Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742383/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486747136) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1723261683/1073741824) }, upper := { exponent := 0, mantissa := (26575/16384) } }, logOuter := sk221LogOuterCertificate, logK := sk221LogKCertificate, logChi := chi185LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54974131507/54973494272) } }, logDArg := sk221LogDArgCertificate }

private noncomputable def leaf2711InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2711LocalValidity :
    LeafFacts leaf2711Box leaf2711Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2711Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486747136) }) = true
      norm_num [leaf2711Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2711CertificateValid :
    WideCertificateValid leaf2711Box leaf2711Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk221ValidityFacts chi185ValidityFacts
    leaf2711LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2711CoverageChecked :
    coverageCheck (innerAD leaf2711Box) leaf2711InnerLog = true := by
  rfl'

private theorem leaf2711InnerLogValid :
    leaf2711InnerLog.Valid 8 (innerAD leaf2711Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2711CoverageChecked

private noncomputable def leaf2711InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629275/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2711InputLogOnePlusV_eq :
    leaf2711InputLogOnePlusV = outerEnclosure 24
      (leaf2711Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2711RoundedFacts : LeafRoundedFacts 8
    leaf2711Certificate.logOnePlusV leaf2711InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2711InputLogOnePlusV_eq }

private noncomputable def leaf2711Inputs : Inputs :=
  inputsOfCaches globalInput sk221RoundedInputs
    chi185InputQChi innerPair50Input
    leaf2711InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2711LowerChecked :
    lowerCheck 24 leaf2711Box leaf2711Inputs = true := by
  rfl'

private theorem leaf2711CoversExact : CoversExact 8
    leaf2711Box leaf2711Certificate leaf2711InnerLog leaf2711Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk221RoundedFacts chi185RoundedFacts
    innerPair50RoundedFacts leaf2711RoundedFacts (by rfl)

private theorem leaf2711FlatSound : Sound leaf2711Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2711CertificateValid
    leaf2711InnerLogValid leaf2711CoversExact leaf2711LowerChecked

private noncomputable def leaf2712Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (237/64), kHi := (119/32), chiLo := (21/128), chiHi := (43/256) }

private noncomputable def leaf2712Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742385/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45811237888) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1726014025/1073741824) }, upper := { exponent := 0, mantissa := (13309/8192) } }, logOuter := sk222LogOuterCertificate, logK := sk222LogKCertificate, logChi := chi185LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623545173/91622475776) } }, logDArg := sk222LogDArgCertificate }

private noncomputable def leaf2712InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2712LocalValidity :
    LeafFacts leaf2712Box leaf2712Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2712Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45811237888) }) = true
      norm_num [leaf2712Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2712CertificateValid :
    WideCertificateValid leaf2712Box leaf2712Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk222ValidityFacts chi185ValidityFacts
    leaf2712LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2712CoverageChecked :
    coverageCheck (innerAD leaf2712Box) leaf2712InnerLog = true := by
  rfl'

private theorem leaf2712InnerLogValid :
    leaf2712InnerLog.Valid 8 (innerAD leaf2712Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2712CoverageChecked

private noncomputable def leaf2712InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629277/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2712InputLogOnePlusV_eq :
    leaf2712InputLogOnePlusV = outerEnclosure 24
      (leaf2712Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2712RoundedFacts : LeafRoundedFacts 8
    leaf2712Certificate.logOnePlusV leaf2712InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2712InputLogOnePlusV_eq }

private noncomputable def leaf2712Inputs : Inputs :=
  inputsOfCaches globalInput sk222RoundedInputs
    chi185InputQChi innerPair50Input
    leaf2712InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2712LowerChecked :
    lowerCheck 24 leaf2712Box leaf2712Inputs = true := by
  rfl'

private theorem leaf2712CoversExact : CoversExact 8
    leaf2712Box leaf2712Certificate leaf2712InnerLog leaf2712Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk222RoundedFacts chi185RoundedFacts
    innerPair50RoundedFacts leaf2712RoundedFacts (by rfl)

private theorem leaf2712FlatSound : Sound leaf2712Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2712CertificateValid
    leaf2712InnerLogValid leaf2712CoversExact leaf2712LowerChecked

private noncomputable def leaf2713Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (237/64), chiLo := (43/256), chiHi := (11/64) }

private noncomputable def leaf2713Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742385/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433614336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1738727233/1073741824) }, upper := { exponent := 0, mantissa := (6703/4096) } }, logOuter := sk221LogOuterCertificate, logK := sk221LogKCertificate, logChi := chi186LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870536191/274867228672) } }, logDArg := sk221LogDArgCertificate }

private noncomputable def leaf2713InnerLog : WideLogData :=
  innerPair166Data

set_option maxRecDepth 1000000 in
private theorem leaf2713LocalValidity :
    LeafFacts leaf2713Box leaf2713Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2713Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433614336) }) = true
      norm_num [leaf2713Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2713CertificateValid :
    WideCertificateValid leaf2713Box leaf2713Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk221ValidityFacts chi186ValidityFacts
    leaf2713LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2713CoverageChecked :
    coverageCheck (innerAD leaf2713Box) leaf2713InnerLog = true := by
  rfl'

private theorem leaf2713InnerLogValid :
    leaf2713InnerLog.Valid 8 (innerAD leaf2713Box) :=
  wideLogDataValid_of_cachedCheck endpoint46PositiveFacts
    endpoint45PositiveFacts.valid leaf2713CoverageChecked

private noncomputable def leaf2713InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629283/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2713InputLogOnePlusV_eq :
    leaf2713InputLogOnePlusV = outerEnclosure 24
      (leaf2713Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2713RoundedFacts : LeafRoundedFacts 8
    leaf2713Certificate.logOnePlusV leaf2713InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2713InputLogOnePlusV_eq }

private noncomputable def leaf2713Inputs : Inputs :=
  inputsOfCaches globalInput sk221RoundedInputs
    chi186InputQChi innerPair166Input
    leaf2713InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2713LowerChecked :
    lowerCheck 24 leaf2713Box leaf2713Inputs = true := by
  rfl'

private theorem leaf2713CoversExact : CoversExact 8
    leaf2713Box leaf2713Certificate leaf2713InnerLog leaf2713Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk221RoundedFacts chi186RoundedFacts
    innerPair166RoundedFacts leaf2713RoundedFacts (by rfl)

private theorem leaf2713FlatSound : Sound leaf2713Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2713CertificateValid
    leaf2713InnerLogValid leaf2713CoversExact leaf2713LowerChecked

private noncomputable def leaf2714Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (237/64), kHi := (119/32), chiLo := (43/256), chiHi := (11/64) }

private noncomputable def leaf2714Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742387/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433591808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1741545107/1073741824) }, upper := { exponent := 0, mantissa := (3357/2048) } }, logOuter := sk222LogOuterCertificate, logK := sk222LogKCertificate, logChi := chi186LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870513663/274867183616) } }, logDArg := sk222LogDArgCertificate }

private noncomputable def leaf2714InnerLog : WideLogData :=
  innerPair166Data

set_option maxRecDepth 1000000 in
private theorem leaf2714LocalValidity :
    LeafFacts leaf2714Box leaf2714Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2714Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433591808) }) = true
      norm_num [leaf2714Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2714CertificateValid :
    WideCertificateValid leaf2714Box leaf2714Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk222ValidityFacts chi186ValidityFacts
    leaf2714LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2714CoverageChecked :
    coverageCheck (innerAD leaf2714Box) leaf2714InnerLog = true := by
  rfl'

private theorem leaf2714InnerLogValid :
    leaf2714InnerLog.Valid 8 (innerAD leaf2714Box) :=
  wideLogDataValid_of_cachedCheck endpoint46PositiveFacts
    endpoint45PositiveFacts.valid leaf2714CoverageChecked

private noncomputable def leaf2714InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907321/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2714InputLogOnePlusV_eq :
    leaf2714InputLogOnePlusV = outerEnclosure 24
      (leaf2714Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2714RoundedFacts : LeafRoundedFacts 8
    leaf2714Certificate.logOnePlusV leaf2714InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2714InputLogOnePlusV_eq }

private noncomputable def leaf2714Inputs : Inputs :=
  inputsOfCaches globalInput sk222RoundedInputs
    chi186InputQChi innerPair166Input
    leaf2714InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2714LowerChecked :
    lowerCheck 24 leaf2714Box leaf2714Inputs = true := by
  rfl'

private theorem leaf2714CoversExact : CoversExact 8
    leaf2714Box leaf2714Certificate leaf2714InnerLog leaf2714Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk222RoundedFacts chi186RoundedFacts
    innerPair166RoundedFacts leaf2714RoundedFacts (by rfl)

private theorem leaf2714FlatSound : Sound leaf2714Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2714CertificateValid
    leaf2714InnerLogValid leaf2714CoversExact leaf2714LowerChecked

private noncomputable def leaf2715Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (239/64), chiLo := (21/128), chiHi := (43/256) }

private noncomputable def leaf2715Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742387/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433691648) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1728766367/1073741824) }, upper := { exponent := 0, mantissa := (26661/16384) } }, logOuter := sk223LogOuterCertificate, logK := sk223LogKCertificate, logChi := chi185LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870613503/274867383296) } }, logDArg := sk223LogDArgCertificate }

private noncomputable def leaf2715InnerLog : WideLogData :=
  innerPair166Data

set_option maxRecDepth 1000000 in
private theorem leaf2715LocalValidity :
    LeafFacts leaf2715Box leaf2715Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2715Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433691648) }) = true
      norm_num [leaf2715Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2715CertificateValid :
    WideCertificateValid leaf2715Box leaf2715Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk223ValidityFacts chi185ValidityFacts
    leaf2715LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2715CoverageChecked :
    coverageCheck (innerAD leaf2715Box) leaf2715InnerLog = true := by
  rfl'

private theorem leaf2715InnerLogValid :
    leaf2715InnerLog.Valid 8 (innerAD leaf2715Box) :=
  wideLogDataValid_of_cachedCheck endpoint46PositiveFacts
    endpoint45PositiveFacts.valid leaf2715CoverageChecked

private noncomputable def leaf2715InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814639/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2715InputLogOnePlusV_eq :
    leaf2715InputLogOnePlusV = outerEnclosure 24
      (leaf2715Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2715RoundedFacts : LeafRoundedFacts 8
    leaf2715Certificate.logOnePlusV leaf2715InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2715InputLogOnePlusV_eq }

private noncomputable def leaf2715Inputs : Inputs :=
  inputsOfCaches globalInput sk223RoundedInputs
    chi185InputQChi innerPair166Input
    leaf2715InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2715LowerChecked :
    lowerCheck 24 leaf2715Box leaf2715Inputs = true := by
  rfl'

private theorem leaf2715CoversExact : CoversExact 8
    leaf2715Box leaf2715Certificate leaf2715InnerLog leaf2715Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk223RoundedFacts chi185RoundedFacts
    innerPair166RoundedFacts leaf2715RoundedFacts (by rfl)

private theorem leaf2715FlatSound : Sound leaf2715Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2715CertificateValid
    leaf2715InnerLogValid leaf2715CoversExact leaf2715LowerChecked

private noncomputable def leaf2716Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (239/64), kHi := (15/4), chiLo := (21/128), chiHi := (43/256) }

private noncomputable def leaf2716Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742389/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433669632) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1731518709/1073741824) }, upper := { exponent := 0, mantissa := (1669/1024) } }, logOuter := sk224LogOuterCertificate, logK := sk224LogKCertificate, logChi := chi185LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870591487/274867339264) } }, logDArg := sk224LogDArgCertificate }

private noncomputable def leaf2716InnerLog : WideLogData :=
  innerPair166Data

set_option maxRecDepth 1000000 in
private theorem leaf2716LocalValidity :
    LeafFacts leaf2716Box leaf2716Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2716Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433669632) }) = true
      norm_num [leaf2716Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2716CertificateValid :
    WideCertificateValid leaf2716Box leaf2716Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk224ValidityFacts chi185ValidityFacts
    leaf2716LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2716CoverageChecked :
    coverageCheck (innerAD leaf2716Box) leaf2716InnerLog = true := by
  rfl'

private theorem leaf2716InnerLogValid :
    leaf2716InnerLog.Valid 8 (innerAD leaf2716Box) :=
  wideLogDataValid_of_cachedCheck endpoint46PositiveFacts
    endpoint45PositiveFacts.valid leaf2716CoverageChecked

private noncomputable def leaf2716InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629279/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2716InputLogOnePlusV_eq :
    leaf2716InputLogOnePlusV = outerEnclosure 24
      (leaf2716Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2716RoundedFacts : LeafRoundedFacts 8
    leaf2716Certificate.logOnePlusV leaf2716InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2716InputLogOnePlusV_eq }

private noncomputable def leaf2716Inputs : Inputs :=
  inputsOfCaches globalInput sk224RoundedInputs
    chi185InputQChi innerPair166Input
    leaf2716InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2716LowerChecked :
    lowerCheck 24 leaf2716Box leaf2716Inputs = true := by
  rfl'

private theorem leaf2716CoversExact : CoversExact 8
    leaf2716Box leaf2716Certificate leaf2716InnerLog leaf2716Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk224RoundedFacts chi185RoundedFacts
    innerPair166RoundedFacts leaf2716RoundedFacts (by rfl)

private theorem leaf2716FlatSound : Sound leaf2716Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2716CertificateValid
    leaf2716InnerLogValid leaf2716CoversExact leaf2716LowerChecked

private noncomputable def leaf2717Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (239/64), chiLo := (43/256), chiHi := (11/64) }

private noncomputable def leaf2717Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742389/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9162461457/9162237952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1744362981/1073741824) }, upper := { exponent := 0, mantissa := (6725/4096) } }, logOuter := sk223LogOuterCertificate, logK := sk223LogKCertificate, logChi := chi186LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (18324699409/18324475904) } }, logDArg := sk223LogDArgCertificate }

private noncomputable def leaf2717InnerLog : WideLogData :=
  innerPair167Data

set_option maxRecDepth 1000000 in
private theorem leaf2717LocalValidity :
    LeafFacts leaf2717Box leaf2717Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2717Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9162461457/9162237952) }) = true
      norm_num [leaf2717Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2717CertificateValid :
    WideCertificateValid leaf2717Box leaf2717Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk223ValidityFacts chi186ValidityFacts
    leaf2717LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2717CoverageChecked :
    coverageCheck (innerAD leaf2717Box) leaf2717InnerLog = true := by
  rfl'

private theorem leaf2717InnerLogValid :
    leaf2717InnerLog.Valid 8 (innerAD leaf2717Box) :=
  wideLogDataValid_of_cachedCheck endpoint46PositiveFacts
    endpoint48PositiveFacts.valid leaf2717CoverageChecked

private noncomputable def leaf2717InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629285/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2717InputLogOnePlusV_eq :
    leaf2717InputLogOnePlusV = outerEnclosure 24
      (leaf2717Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2717RoundedFacts : LeafRoundedFacts 8
    leaf2717Certificate.logOnePlusV leaf2717InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2717InputLogOnePlusV_eq }

private noncomputable def leaf2717Inputs : Inputs :=
  inputsOfCaches globalInput sk223RoundedInputs
    chi186InputQChi innerPair167Input
    leaf2717InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2717LowerChecked :
    lowerCheck 24 leaf2717Box leaf2717Inputs = true := by
  rfl'

private theorem leaf2717CoversExact : CoversExact 8
    leaf2717Box leaf2717Certificate leaf2717InnerLog leaf2717Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk223RoundedFacts chi186RoundedFacts
    innerPair167RoundedFacts leaf2717RoundedFacts (by rfl)

private theorem leaf2717FlatSound : Sound leaf2717Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2717CertificateValid
    leaf2717InnerLogValid leaf2717CoversExact leaf2717LowerChecked

private noncomputable def leaf2718Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (239/64), kHi := (15/4), chiLo := (43/256), chiHi := (11/64) }

private noncomputable def leaf2718Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742391/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433546752) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1747180855/1073741824) }, upper := { exponent := 0, mantissa := (421/256) } }, logOuter := sk224LogOuterCertificate, logK := sk224LogKCertificate, logChi := chi186LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870468607/274867093504) } }, logDArg := sk224LogDArgCertificate }

private noncomputable def leaf2718InnerLog : WideLogData :=
  innerPair61Data

set_option maxRecDepth 1000000 in
private theorem leaf2718LocalValidity :
    LeafFacts leaf2718Box leaf2718Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2718Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433546752) }) = true
      norm_num [leaf2718Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2718CertificateValid :
    WideCertificateValid leaf2718Box leaf2718Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk224ValidityFacts chi186ValidityFacts
    leaf2718LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2718CoverageChecked :
    coverageCheck (innerAD leaf2718Box) leaf2718InnerLog = true := by
  rfl'

private theorem leaf2718InnerLogValid :
    leaf2718InnerLog.Valid 8 (innerAD leaf2718Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint48PositiveFacts.valid leaf2718CoverageChecked

private noncomputable def leaf2718InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629287/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2718InputLogOnePlusV_eq :
    leaf2718InputLogOnePlusV = outerEnclosure 24
      (leaf2718Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2718RoundedFacts : LeafRoundedFacts 8
    leaf2718Certificate.logOnePlusV leaf2718InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2718InputLogOnePlusV_eq }

private noncomputable def leaf2718Inputs : Inputs :=
  inputsOfCaches globalInput sk224RoundedInputs
    chi186InputQChi innerPair61Input
    leaf2718InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2718LowerChecked :
    lowerCheck 24 leaf2718Box leaf2718Inputs = true := by
  rfl'

private theorem leaf2718CoversExact : CoversExact 8
    leaf2718Box leaf2718Certificate leaf2718InnerLog leaf2718Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk224RoundedFacts chi186RoundedFacts
    innerPair61RoundedFacts leaf2718RoundedFacts (by rfl)

private theorem leaf2718FlatSound : Sound leaf2718Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2718CertificateValid
    leaf2718InnerLogValid leaf2718CoversExact leaf2718LowerChecked

private noncomputable def leaf2719Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (233/64), chiLo := (11/64), chiHi := (45/256) }

private noncomputable def leaf2719Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742379/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433585152) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1742659159/1073741824) }, upper := { exponent := 0, mantissa := (26869/16384) } }, logOuter := sk217LogOuterCertificate, logK := sk217LogKCertificate, logChi := chi133LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870507007/274867170304) } }, logDArg := sk217LogDArgCertificate }

private noncomputable def leaf2719InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf2719LocalValidity :
    LeafFacts leaf2719Box leaf2719Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2719Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433585152) }) = true
      norm_num [leaf2719Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2719CertificateValid :
    WideCertificateValid leaf2719Box leaf2719Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk217ValidityFacts chi133ValidityFacts
    leaf2719LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2719CoverageChecked :
    coverageCheck (innerAD leaf2719Box) leaf2719InnerLog = true := by
  rfl'

private theorem leaf2719InnerLogValid :
    leaf2719InnerLog.Valid 8 (innerAD leaf2719Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf2719CoverageChecked

private noncomputable def leaf2719InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907321/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2719InputLogOnePlusV_eq :
    leaf2719InputLogOnePlusV = outerEnclosure 24
      (leaf2719Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2719RoundedFacts : LeafRoundedFacts 8
    leaf2719Certificate.logOnePlusV leaf2719InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2719InputLogOnePlusV_eq }

private noncomputable def leaf2719Inputs : Inputs :=
  inputsOfCaches globalInput sk217RoundedInputs
    chi133InputQChi innerPair51Input
    leaf2719InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2719LowerChecked :
    lowerCheck 24 leaf2719Box leaf2719Inputs = true := by
  rfl'

private theorem leaf2719CoversExact : CoversExact 8
    leaf2719Box leaf2719Certificate leaf2719InnerLog leaf2719Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk217RoundedFacts chi133RoundedFacts
    innerPair51RoundedFacts leaf2719RoundedFacts (by rfl)

private theorem leaf2719FlatSound : Sound leaf2719Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2719CertificateValid
    leaf2719InnerLogValid leaf2719CoversExact leaf2719LowerChecked

private noncomputable def leaf2720Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (233/64), kHi := (117/32), chiLo := (11/64), chiHi := (45/256) }

private noncomputable def leaf2720Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742381/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433562112) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1745542565/1073741824) }, upper := { exponent := 0, mantissa := (13457/8192) } }, logOuter := sk218LogOuterCertificate, logK := sk218LogKCertificate, logChi := chi133LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870483967/274867124224) } }, logDArg := sk218LogDArgCertificate }

private noncomputable def leaf2720InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2720LocalValidity :
    LeafFacts leaf2720Box leaf2720Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2720Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433562112) }) = true
      norm_num [leaf2720Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2720CertificateValid :
    WideCertificateValid leaf2720Box leaf2720Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk218ValidityFacts chi133ValidityFacts
    leaf2720LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2720CoverageChecked :
    coverageCheck (innerAD leaf2720Box) leaf2720InnerLog = true := by
  rfl'

private theorem leaf2720InnerLogValid :
    leaf2720InnerLog.Valid 8 (innerAD leaf2720Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2720CoverageChecked

private noncomputable def leaf2720InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814643/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2720InputLogOnePlusV_eq :
    leaf2720InputLogOnePlusV = outerEnclosure 24
      (leaf2720Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2720RoundedFacts : LeafRoundedFacts 8
    leaf2720Certificate.logOnePlusV leaf2720InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2720InputLogOnePlusV_eq }

private noncomputable def leaf2720Inputs : Inputs :=
  inputsOfCaches globalInput sk218RoundedInputs
    chi133InputQChi innerPair56Input
    leaf2720InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2720LowerChecked :
    lowerCheck 24 leaf2720Box leaf2720Inputs = true := by
  rfl'

private theorem leaf2720CoversExact : CoversExact 8
    leaf2720Box leaf2720Certificate leaf2720InnerLog leaf2720Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk218RoundedFacts chi133RoundedFacts
    innerPair56RoundedFacts leaf2720RoundedFacts (by rfl)

private theorem leaf2720FlatSound : Sound leaf2720Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2720CertificateValid
    leaf2720InnerLogValid leaf2720CoversExact leaf2720LowerChecked

private noncomputable def leaf2721Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (233/64), chiLo := (45/256), chiHi := (23/128) }

private noncomputable def leaf2721Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742381/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433465856) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1757862581/1073741824) }, upper := { exponent := 0, mantissa := (13551/8192) } }, logOuter := sk217LogOuterCertificate, logK := sk217LogKCertificate, logChi := chi134LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870387711/274866931712) } }, logDArg := sk217LogDArgCertificate }

private noncomputable def leaf2721InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2721LocalValidity :
    LeafFacts leaf2721Box leaf2721Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2721Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433465856) }) = true
      norm_num [leaf2721Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2721CertificateValid :
    WideCertificateValid leaf2721Box leaf2721Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk217ValidityFacts chi134ValidityFacts
    leaf2721LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2721CoverageChecked :
    coverageCheck (innerAD leaf2721Box) leaf2721InnerLog = true := by
  rfl'

private theorem leaf2721InnerLogValid :
    leaf2721InnerLog.Valid 8 (innerAD leaf2721Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2721CoverageChecked

private noncomputable def leaf2721InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907323/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2721InputLogOnePlusV_eq :
    leaf2721InputLogOnePlusV = outerEnclosure 24
      (leaf2721Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2721RoundedFacts : LeafRoundedFacts 8
    leaf2721Certificate.logOnePlusV leaf2721InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2721InputLogOnePlusV_eq }

private noncomputable def leaf2721Inputs : Inputs :=
  inputsOfCaches globalInput sk217RoundedInputs
    chi134InputQChi innerPair56Input
    leaf2721InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2721LowerChecked :
    lowerCheck 24 leaf2721Box leaf2721Inputs = true := by
  rfl'

private theorem leaf2721CoversExact : CoversExact 8
    leaf2721Box leaf2721Certificate leaf2721InnerLog leaf2721Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk217RoundedFacts chi134RoundedFacts
    innerPair56RoundedFacts leaf2721RoundedFacts (by rfl)

private theorem leaf2721FlatSound : Sound leaf2721Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2721CertificateValid
    leaf2721InnerLogValid leaf2721CoversExact leaf2721LowerChecked

private noncomputable def leaf2722Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (233/64), kHi := (117/32), chiLo := (45/256), chiHi := (23/128) }

private noncomputable def leaf2722Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742383/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433442304) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1760811519/1073741824) }, upper := { exponent := 0, mantissa := (6787/4096) } }, logOuter := sk218LogOuterCertificate, logK := sk218LogKCertificate, logChi := chi134LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870364159/274866884608) } }, logDArg := sk218LogDArgCertificate }

private noncomputable def leaf2722InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2722LocalValidity :
    LeafFacts leaf2722Box leaf2722Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2722Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433442304) }) = true
      norm_num [leaf2722Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2722CertificateValid :
    WideCertificateValid leaf2722Box leaf2722Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk218ValidityFacts chi134ValidityFacts
    leaf2722LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2722CoverageChecked :
    coverageCheck (innerAD leaf2722Box) leaf2722InnerLog = true := by
  rfl'

private theorem leaf2722InnerLogValid :
    leaf2722InnerLog.Valid 8 (innerAD leaf2722Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2722CoverageChecked

private noncomputable def leaf2722InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629293/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2722InputLogOnePlusV_eq :
    leaf2722InputLogOnePlusV = outerEnclosure 24
      (leaf2722Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2722RoundedFacts : LeafRoundedFacts 8
    leaf2722Certificate.logOnePlusV leaf2722InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2722InputLogOnePlusV_eq }

private noncomputable def leaf2722Inputs : Inputs :=
  inputsOfCaches globalInput sk218RoundedInputs
    chi134InputQChi innerPair56Input
    leaf2722InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2722LowerChecked :
    lowerCheck 24 leaf2722Box leaf2722Inputs = true := by
  rfl'

private theorem leaf2722CoversExact : CoversExact 8
    leaf2722Box leaf2722Certificate leaf2722InnerLog leaf2722Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk218RoundedFacts chi134RoundedFacts
    innerPair56RoundedFacts leaf2722RoundedFacts (by rfl)

private theorem leaf2722FlatSound : Sound leaf2722Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2722CertificateValid
    leaf2722InnerLogValid leaf2722CoversExact leaf2722LowerChecked

private noncomputable def leaf2723Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (235/64), chiLo := (11/64), chiHi := (45/256) }

private noncomputable def leaf2723Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742383/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433539072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1748425971/1073741824) }, upper := { exponent := 0, mantissa := (26959/16384) } }, logOuter := sk219LogOuterCertificate, logK := sk219LogKCertificate, logChi := chi133LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870460927/274867078144) } }, logDArg := sk219LogDArgCertificate }

private noncomputable def leaf2723InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2723LocalValidity :
    LeafFacts leaf2723Box leaf2723Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2723Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433539072) }) = true
      norm_num [leaf2723Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2723CertificateValid :
    WideCertificateValid leaf2723Box leaf2723Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk219ValidityFacts chi133ValidityFacts
    leaf2723LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2723CoverageChecked :
    coverageCheck (innerAD leaf2723Box) leaf2723InnerLog = true := by
  rfl'

private theorem leaf2723InnerLogValid :
    leaf2723InnerLog.Valid 8 (innerAD leaf2723Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2723CoverageChecked

private noncomputable def leaf2723InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629287/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2723InputLogOnePlusV_eq :
    leaf2723InputLogOnePlusV = outerEnclosure 24
      (leaf2723Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2723RoundedFacts : LeafRoundedFacts 8
    leaf2723Certificate.logOnePlusV leaf2723InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2723InputLogOnePlusV_eq }

private noncomputable def leaf2723Inputs : Inputs :=
  inputsOfCaches globalInput sk219RoundedInputs
    chi133InputQChi innerPair56Input
    leaf2723InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2723LowerChecked :
    lowerCheck 24 leaf2723Box leaf2723Inputs = true := by
  rfl'

private theorem leaf2723CoversExact : CoversExact 8
    leaf2723Box leaf2723Certificate leaf2723InnerLog leaf2723Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk219RoundedFacts chi133RoundedFacts
    innerPair56RoundedFacts leaf2723RoundedFacts (by rfl)

private theorem leaf2723FlatSound : Sound leaf2723Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2723CertificateValid
    leaf2723InnerLogValid leaf2723CoversExact leaf2723LowerChecked

private noncomputable def leaf2724Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (235/64), kHi := (59/16), chiLo := (11/64), chiHi := (45/256) }

private noncomputable def leaf2724Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742385/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433516032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1751309377/1073741824) }, upper := { exponent := 0, mantissa := (6751/4096) } }, logOuter := sk220LogOuterCertificate, logK := sk220LogKCertificate, logChi := chi133LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870437887/274867032064) } }, logDArg := sk220LogDArgCertificate }

private noncomputable def leaf2724InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2724LocalValidity :
    LeafFacts leaf2724Box leaf2724Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2724Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433516032) }) = true
      norm_num [leaf2724Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2724CertificateValid :
    WideCertificateValid leaf2724Box leaf2724Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk220ValidityFacts chi133ValidityFacts
    leaf2724LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2724CoverageChecked :
    coverageCheck (innerAD leaf2724Box) leaf2724InnerLog = true := by
  rfl'

private theorem leaf2724InnerLogValid :
    leaf2724InnerLog.Valid 8 (innerAD leaf2724Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2724CoverageChecked

private noncomputable def leaf2724InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629289/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2724InputLogOnePlusV_eq :
    leaf2724InputLogOnePlusV = outerEnclosure 24
      (leaf2724Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2724RoundedFacts : LeafRoundedFacts 8
    leaf2724Certificate.logOnePlusV leaf2724InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2724InputLogOnePlusV_eq }

private noncomputable def leaf2724Inputs : Inputs :=
  inputsOfCaches globalInput sk220RoundedInputs
    chi133InputQChi innerPair56Input
    leaf2724InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2724LowerChecked :
    lowerCheck 24 leaf2724Box leaf2724Inputs = true := by
  rfl'

private theorem leaf2724CoversExact : CoversExact 8
    leaf2724Box leaf2724Certificate leaf2724InnerLog leaf2724Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk220RoundedFacts chi133RoundedFacts
    innerPair56RoundedFacts leaf2724RoundedFacts (by rfl)

private theorem leaf2724FlatSound : Sound leaf2724Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2724CertificateValid
    leaf2724InnerLogValid leaf2724CoversExact leaf2724LowerChecked

private noncomputable def leaf2725Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (235/64), chiLo := (45/256), chiHi := (23/128) }

private noncomputable def leaf2725Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742385/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45811139584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1763760457/1073741824) }, upper := { exponent := 0, mantissa := (13597/8192) } }, logOuter := sk219LogOuterCertificate, logK := sk219LogKCertificate, logChi := chi134LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623446869/91622279168) } }, logDArg := sk219LogDArgCertificate }

private noncomputable def leaf2725InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2725LocalValidity :
    LeafFacts leaf2725Box leaf2725Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2725Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45811139584) }) = true
      norm_num [leaf2725Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2725CertificateValid :
    WideCertificateValid leaf2725Box leaf2725Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk219ValidityFacts chi134ValidityFacts
    leaf2725LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2725CoverageChecked :
    coverageCheck (innerAD leaf2725Box) leaf2725InnerLog = true := by
  rfl'

private theorem leaf2725InnerLogValid :
    leaf2725InnerLog.Valid 8 (innerAD leaf2725Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2725CoverageChecked

private noncomputable def leaf2725InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629295/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2725InputLogOnePlusV_eq :
    leaf2725InputLogOnePlusV = outerEnclosure 24
      (leaf2725Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2725RoundedFacts : LeafRoundedFacts 8
    leaf2725Certificate.logOnePlusV leaf2725InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2725InputLogOnePlusV_eq }

private noncomputable def leaf2725Inputs : Inputs :=
  inputsOfCaches globalInput sk219RoundedInputs
    chi134InputQChi innerPair56Input
    leaf2725InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2725LowerChecked :
    lowerCheck 24 leaf2725Box leaf2725Inputs = true := by
  rfl'

private theorem leaf2725CoversExact : CoversExact 8
    leaf2725Box leaf2725Certificate leaf2725InnerLog leaf2725Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk219RoundedFacts chi134RoundedFacts
    innerPair56RoundedFacts leaf2725RoundedFacts (by rfl)

private theorem leaf2725FlatSound : Sound leaf2725Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2725CertificateValid
    leaf2725InnerLogValid leaf2725CoversExact leaf2725LowerChecked

private noncomputable def leaf2726Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (235/64), kHi := (59/16), chiLo := (45/256), chiHi := (23/128) }

private noncomputable def leaf2726Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742387/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486679040) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1766709395/1073741824) }, upper := { exponent := 0, mantissa := (3405/2048) } }, logOuter := sk220LogOuterCertificate, logK := sk220LogKCertificate, logChi := chi134LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54974063411/54973358080) } }, logDArg := sk220LogDArgCertificate }

private noncomputable def leaf2726InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2726LocalValidity :
    LeafFacts leaf2726Box leaf2726Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2726Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486679040) }) = true
      norm_num [leaf2726Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2726CertificateValid :
    WideCertificateValid leaf2726Box leaf2726Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk220ValidityFacts chi134ValidityFacts
    leaf2726LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2726CoverageChecked :
    coverageCheck (innerAD leaf2726Box) leaf2726InnerLog = true := by
  rfl'

private theorem leaf2726InnerLogValid :
    leaf2726InnerLog.Valid 8 (innerAD leaf2726Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2726CoverageChecked

private noncomputable def leaf2726InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726831/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf2726InputLogOnePlusV_eq :
    leaf2726InputLogOnePlusV = outerEnclosure 24
      (leaf2726Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2726RoundedFacts : LeafRoundedFacts 8
    leaf2726Certificate.logOnePlusV leaf2726InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2726InputLogOnePlusV_eq }

private noncomputable def leaf2726Inputs : Inputs :=
  inputsOfCaches globalInput sk220RoundedInputs
    chi134InputQChi innerPair56Input
    leaf2726InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2726LowerChecked :
    lowerCheck 24 leaf2726Box leaf2726Inputs = true := by
  rfl'

private theorem leaf2726CoversExact : CoversExact 8
    leaf2726Box leaf2726Certificate leaf2726InnerLog leaf2726Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk220RoundedFacts chi134RoundedFacts
    innerPair56RoundedFacts leaf2726RoundedFacts (by rfl)

private theorem leaf2726FlatSound : Sound leaf2726Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2726CertificateValid
    leaf2726InnerLogValid leaf2726CoversExact leaf2726LowerChecked

private noncomputable def leaf2727Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (233/64), chiLo := (23/128), chiHi := (47/256) }

private noncomputable def leaf2727Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742383/1073741824) }, vSqrt := { lower := (8191/8192), upper := (3054153819/3054074368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1773066003/1073741824) }, upper := { exponent := 0, mantissa := (27335/16384) } }, logOuter := sk217LogOuterCertificate, logK := sk217LogKCertificate, logChi := chi135LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (6108228187/6108148736) } }, logDArg := sk217LogDArgCertificate }

private noncomputable def leaf2727InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2727LocalValidity :
    LeafFacts leaf2727Box leaf2727Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2727Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (3054153819/3054074368) }) = true
      norm_num [leaf2727Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2727CertificateValid :
    WideCertificateValid leaf2727Box leaf2727Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk217ValidityFacts chi135ValidityFacts
    leaf2727LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2727CoverageChecked :
    coverageCheck (innerAD leaf2727Box) leaf2727InnerLog = true := by
  rfl'

private theorem leaf2727InnerLogValid :
    leaf2727InnerLog.Valid 8 (innerAD leaf2727Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2727CoverageChecked

private noncomputable def leaf2727InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629299/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2727InputLogOnePlusV_eq :
    leaf2727InputLogOnePlusV = outerEnclosure 24
      (leaf2727Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2727RoundedFacts : LeafRoundedFacts 8
    leaf2727Certificate.logOnePlusV leaf2727InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2727InputLogOnePlusV_eq }

private noncomputable def leaf2727Inputs : Inputs :=
  inputsOfCaches globalInput sk217RoundedInputs
    chi135InputQChi innerPair56Input
    leaf2727InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2727LowerChecked :
    lowerCheck 24 leaf2727Box leaf2727Inputs = true := by
  rfl'

private theorem leaf2727CoversExact : CoversExact 8
    leaf2727Box leaf2727Certificate leaf2727InnerLog leaf2727Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk217RoundedFacts chi135RoundedFacts
    innerPair56RoundedFacts leaf2727RoundedFacts (by rfl)

private theorem leaf2727FlatSound : Sound leaf2727Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2727CertificateValid
    leaf2727InnerLogValid leaf2727CoversExact leaf2727LowerChecked

private noncomputable def leaf2728Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (233/64), kHi := (117/32), chiLo := (23/128), chiHi := (47/256) }

private noncomputable def leaf2728Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742385/1073741824) }, vSqrt := { lower := (8191/8192), upper := (8084524815/8084313088) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1776080473/1073741824) }, upper := { exponent := 0, mantissa := (13691/8192) } }, logOuter := sk218LogOuterCertificate, logK := sk218LogKCertificate, logChi := chi135LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16168837903/16168626176) } }, logDArg := sk218LogDArgCertificate }

private noncomputable def leaf2728InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2728LocalValidity :
    LeafFacts leaf2728Box leaf2728Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2728Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8084524815/8084313088) }) = true
      norm_num [leaf2728Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2728CertificateValid :
    WideCertificateValid leaf2728Box leaf2728Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk218ValidityFacts chi135ValidityFacts
    leaf2728LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2728CoverageChecked :
    coverageCheck (innerAD leaf2728Box) leaf2728InnerLog = true := by
  rfl'

private theorem leaf2728InnerLogValid :
    leaf2728InnerLog.Valid 8 (innerAD leaf2728Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2728CoverageChecked

private noncomputable def leaf2728InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907325/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2728InputLogOnePlusV_eq :
    leaf2728InputLogOnePlusV = outerEnclosure 24
      (leaf2728Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2728RoundedFacts : LeafRoundedFacts 8
    leaf2728Certificate.logOnePlusV leaf2728InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2728InputLogOnePlusV_eq }

private noncomputable def leaf2728Inputs : Inputs :=
  inputsOfCaches globalInput sk218RoundedInputs
    chi135InputQChi innerPair56Input
    leaf2728InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2728LowerChecked :
    lowerCheck 24 leaf2728Box leaf2728Inputs = true := by
  rfl'

private theorem leaf2728CoversExact : CoversExact 8
    leaf2728Box leaf2728Certificate leaf2728InnerLog leaf2728Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk218RoundedFacts chi135RoundedFacts
    innerPair56RoundedFacts leaf2728RoundedFacts (by rfl)

private theorem leaf2728FlatSound : Sound leaf2728Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2728CertificateValid
    leaf2728InnerLogValid leaf2728CoversExact leaf2728LowerChecked

private noncomputable def leaf2729Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (233/64), chiLo := (47/256), chiHi := (3/16) }

private noncomputable def leaf2729Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742385/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433227264) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1788269425/1073741824) }, upper := { exponent := 0, mantissa := (1723/1024) } }, logOuter := sk217LogOuterCertificate, logK := sk217LogKCertificate, logChi := chi136LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870149119/274866454528) } }, logDArg := sk217LogDArgCertificate }

private noncomputable def leaf2729InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2729LocalValidity :
    LeafFacts leaf2729Box leaf2729Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2729Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433227264) }) = true
      norm_num [leaf2729Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2729CertificateValid :
    WideCertificateValid leaf2729Box leaf2729Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk217ValidityFacts chi136ValidityFacts
    leaf2729LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2729CoverageChecked :
    coverageCheck (innerAD leaf2729Box) leaf2729InnerLog = true := by
  rfl'

private theorem leaf2729InnerLogValid :
    leaf2729InnerLog.Valid 8 (innerAD leaf2729Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2729CoverageChecked

private noncomputable def leaf2729InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814653/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2729InputLogOnePlusV_eq :
    leaf2729InputLogOnePlusV = outerEnclosure 24
      (leaf2729Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2729RoundedFacts : LeafRoundedFacts 8
    leaf2729Certificate.logOnePlusV leaf2729InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2729InputLogOnePlusV_eq }

private noncomputable def leaf2729Inputs : Inputs :=
  inputsOfCaches globalInput sk217RoundedInputs
    chi136InputQChi innerPair56Input
    leaf2729InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2729LowerChecked :
    lowerCheck 24 leaf2729Box leaf2729Inputs = true := by
  rfl'

private theorem leaf2729CoversExact : CoversExact 8
    leaf2729Box leaf2729Certificate leaf2729InnerLog leaf2729Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk217RoundedFacts chi136RoundedFacts
    innerPair56RoundedFacts leaf2729RoundedFacts (by rfl)

private theorem leaf2729FlatSound : Sound leaf2729Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2729CertificateValid
    leaf2729InnerLogValid leaf2729CoversExact leaf2729LowerChecked

private noncomputable def leaf2730Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (233/64), kHi := (117/32), chiLo := (47/256), chiHi := (3/16) }

private noncomputable def leaf2730Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742387/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433202688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1791349427/1073741824) }, upper := { exponent := 0, mantissa := (863/512) } }, logOuter := sk218LogOuterCertificate, logK := sk218LogKCertificate, logChi := chi136LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870124543/274866405376) } }, logDArg := sk218LogDArgCertificate }

private noncomputable def leaf2730InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2730LocalValidity :
    LeafFacts leaf2730Box leaf2730Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2730Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433202688) }) = true
      norm_num [leaf2730Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2730CertificateValid :
    WideCertificateValid leaf2730Box leaf2730Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk218ValidityFacts chi136ValidityFacts
    leaf2730LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2730CoverageChecked :
    coverageCheck (innerAD leaf2730Box) leaf2730InnerLog = true := by
  rfl'

private theorem leaf2730InnerLogValid :
    leaf2730InnerLog.Valid 8 (innerAD leaf2730Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2730CoverageChecked

private noncomputable def leaf2730InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907327/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2730InputLogOnePlusV_eq :
    leaf2730InputLogOnePlusV = outerEnclosure 24
      (leaf2730Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2730RoundedFacts : LeafRoundedFacts 8
    leaf2730Certificate.logOnePlusV leaf2730InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2730InputLogOnePlusV_eq }

private noncomputable def leaf2730Inputs : Inputs :=
  inputsOfCaches globalInput sk218RoundedInputs
    chi136InputQChi innerPair56Input
    leaf2730InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2730LowerChecked :
    lowerCheck 24 leaf2730Box leaf2730Inputs = true := by
  rfl'

private theorem leaf2730CoversExact : CoversExact 8
    leaf2730Box leaf2730Certificate leaf2730InnerLog leaf2730Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk218RoundedFacts chi136RoundedFacts
    innerPair56RoundedFacts leaf2730RoundedFacts (by rfl)

private theorem leaf2730FlatSound : Sound leaf2730Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2730CertificateValid
    leaf2730InnerLogValid leaf2730CoversExact leaf2730LowerChecked

private noncomputable def leaf2731Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (235/64), chiLo := (23/128), chiHi := (47/256) }

private noncomputable def leaf2731Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742387/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433298432) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1779094943/1073741824) }, upper := { exponent := 0, mantissa := (27429/16384) } }, logOuter := sk219LogOuterCertificate, logK := sk219LogKCertificate, logChi := chi135LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870220287/274866596864) } }, logDArg := sk219LogDArgCertificate }

private noncomputable def leaf2731InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2731LocalValidity :
    LeafFacts leaf2731Box leaf2731Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2731Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433298432) }) = true
      norm_num [leaf2731Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2731CertificateValid :
    WideCertificateValid leaf2731Box leaf2731Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk219ValidityFacts chi135ValidityFacts
    leaf2731LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2731CoverageChecked :
    coverageCheck (innerAD leaf2731Box) leaf2731InnerLog = true := by
  rfl'

private theorem leaf2731InnerLogValid :
    leaf2731InnerLog.Valid 8 (innerAD leaf2731Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2731CoverageChecked

private noncomputable def leaf2731InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814651/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2731InputLogOnePlusV_eq :
    leaf2731InputLogOnePlusV = outerEnclosure 24
      (leaf2731Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2731RoundedFacts : LeafRoundedFacts 8
    leaf2731Certificate.logOnePlusV leaf2731InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2731InputLogOnePlusV_eq }

private noncomputable def leaf2731Inputs : Inputs :=
  inputsOfCaches globalInput sk219RoundedInputs
    chi135InputQChi innerPair56Input
    leaf2731InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2731LowerChecked :
    lowerCheck 24 leaf2731Box leaf2731Inputs = true := by
  rfl'

private theorem leaf2731CoversExact : CoversExact 8
    leaf2731Box leaf2731Certificate leaf2731InnerLog leaf2731Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk219RoundedFacts chi135RoundedFacts
    innerPair56RoundedFacts leaf2731RoundedFacts (by rfl)

private theorem leaf2731FlatSound : Sound leaf2731Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2731CertificateValid
    leaf2731InnerLogValid leaf2731CoversExact leaf2731LowerChecked

private noncomputable def leaf2732Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (235/64), kHi := (59/16), chiLo := (23/128), chiHi := (47/256) }

private noncomputable def leaf2732Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742389/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45811091456) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1782109413/1073741824) }, upper := { exponent := 0, mantissa := (6869/4096) } }, logOuter := sk220LogOuterCertificate, logK := sk220LogKCertificate, logChi := chi135LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623398741/91622182912) } }, logDArg := sk220LogDArgCertificate }

private noncomputable def leaf2732InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2732LocalValidity :
    LeafFacts leaf2732Box leaf2732Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2732Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45811091456) }) = true
      norm_num [leaf2732Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2732CertificateValid :
    WideCertificateValid leaf2732Box leaf2732Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk220ValidityFacts chi135ValidityFacts
    leaf2732LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2732CoverageChecked :
    coverageCheck (innerAD leaf2732Box) leaf2732InnerLog = true := by
  rfl'

private theorem leaf2732InnerLogValid :
    leaf2732InnerLog.Valid 8 (innerAD leaf2732Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2732CoverageChecked

private noncomputable def leaf2732InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629303/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2732InputLogOnePlusV_eq :
    leaf2732InputLogOnePlusV = outerEnclosure 24
      (leaf2732Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2732RoundedFacts : LeafRoundedFacts 8
    leaf2732Certificate.logOnePlusV leaf2732InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2732InputLogOnePlusV_eq }

private noncomputable def leaf2732Inputs : Inputs :=
  inputsOfCaches globalInput sk220RoundedInputs
    chi135InputQChi innerPair56Input
    leaf2732InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2732LowerChecked :
    lowerCheck 24 leaf2732Box leaf2732Inputs = true := by
  rfl'

private theorem leaf2732CoversExact : CoversExact 8
    leaf2732Box leaf2732Certificate leaf2732InnerLog leaf2732Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk220RoundedFacts chi135RoundedFacts
    innerPair56RoundedFacts leaf2732RoundedFacts (by rfl)

private theorem leaf2732FlatSound : Sound leaf2732Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2732CertificateValid
    leaf2732InnerLogValid leaf2732CoversExact leaf2732LowerChecked

private noncomputable def leaf2733Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (235/64), chiLo := (47/256), chiHi := (3/16) }

private noncomputable def leaf2733Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742389/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433178112) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1794429429/1073741824) }, upper := { exponent := 0, mantissa := (1729/1024) } }, logOuter := sk219LogOuterCertificate, logK := sk219LogKCertificate, logChi := chi136LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870099967/274866356224) } }, logDArg := sk219LogDArgCertificate }

private noncomputable def leaf2733InnerLog : WideLogData :=
  innerPair173Data

set_option maxRecDepth 1000000 in
private theorem leaf2733LocalValidity :
    LeafFacts leaf2733Box leaf2733Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2733Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433178112) }) = true
      norm_num [leaf2733Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2733CertificateValid :
    WideCertificateValid leaf2733Box leaf2733Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk219ValidityFacts chi136ValidityFacts
    leaf2733LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2733CoverageChecked :
    coverageCheck (innerAD leaf2733Box) leaf2733InnerLog = true := by
  rfl'

private theorem leaf2733InnerLogValid :
    leaf2733InnerLog.Valid 8 (innerAD leaf2733Box) :=
  wideLogDataValid_of_cachedCheck endpoint48PositiveFacts
    endpoint20PositiveFacts.valid leaf2733CoverageChecked

private noncomputable def leaf2733InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629309/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2733InputLogOnePlusV_eq :
    leaf2733InputLogOnePlusV = outerEnclosure 24
      (leaf2733Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2733RoundedFacts : LeafRoundedFacts 8
    leaf2733Certificate.logOnePlusV leaf2733InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2733InputLogOnePlusV_eq }

private noncomputable def leaf2733Inputs : Inputs :=
  inputsOfCaches globalInput sk219RoundedInputs
    chi136InputQChi innerPair173Input
    leaf2733InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2733LowerChecked :
    lowerCheck 24 leaf2733Box leaf2733Inputs = true := by
  rfl'

private theorem leaf2733CoversExact : CoversExact 8
    leaf2733Box leaf2733Certificate leaf2733InnerLog leaf2733Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk219RoundedFacts chi136RoundedFacts
    innerPair173RoundedFacts leaf2733RoundedFacts (by rfl)

private theorem leaf2733FlatSound : Sound leaf2733Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2733CertificateValid
    leaf2733InnerLogValid leaf2733CoversExact leaf2733LowerChecked

private noncomputable def leaf2734Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (235/64), kHi := (59/16), chiLo := (47/256), chiHi := (3/16) }

private noncomputable def leaf2734Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742391/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433153536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1797509431/1073741824) }, upper := { exponent := 0, mantissa := (433/256) } }, logOuter := sk220LogOuterCertificate, logK := sk220LogKCertificate, logChi := chi136LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870075391/274866307072) } }, logDArg := sk220LogDArgCertificate }

private noncomputable def leaf2734InnerLog : WideLogData :=
  innerPair420Data

set_option maxRecDepth 1000000 in
private theorem leaf2734LocalValidity :
    LeafFacts leaf2734Box leaf2734Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2734Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433153536) }) = true
      norm_num [leaf2734Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2734CertificateValid :
    WideCertificateValid leaf2734Box leaf2734Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk220ValidityFacts chi136ValidityFacts
    leaf2734LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2734CoverageChecked :
    coverageCheck (innerAD leaf2734Box) leaf2734InnerLog = true := by
  rfl'

private theorem leaf2734InnerLogValid :
    leaf2734InnerLog.Valid 8 (innerAD leaf2734Box) :=
  wideLogDataValid_of_cachedCheck endpoint133PositiveFacts
    endpoint20PositiveFacts.valid leaf2734CoverageChecked

private noncomputable def leaf2734InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629311/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2734InputLogOnePlusV_eq :
    leaf2734InputLogOnePlusV = outerEnclosure 24
      (leaf2734Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2734RoundedFacts : LeafRoundedFacts 8
    leaf2734Certificate.logOnePlusV leaf2734InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2734InputLogOnePlusV_eq }

private noncomputable def leaf2734Inputs : Inputs :=
  inputsOfCaches globalInput sk220RoundedInputs
    chi136InputQChi innerPair420Input
    leaf2734InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2734LowerChecked :
    lowerCheck 24 leaf2734Box leaf2734Inputs = true := by
  rfl'

private theorem leaf2734CoversExact : CoversExact 8
    leaf2734Box leaf2734Certificate leaf2734InnerLog leaf2734Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk220RoundedFacts chi136RoundedFacts
    innerPair420RoundedFacts leaf2734RoundedFacts (by rfl)

private theorem leaf2734FlatSound : Sound leaf2734Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2734CertificateValid
    leaf2734InnerLogValid leaf2734CoversExact leaf2734LowerChecked

private noncomputable def leaf2735Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (237/64), chiLo := (11/64), chiHi := (45/256) }

private noncomputable def leaf2735Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742387/1073741824) }, vSqrt := { lower := (8191/8192), upper := (3196207485/3196127744) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1754192783/1073741824) }, upper := { exponent := 0, mantissa := (27049/16384) } }, logOuter := sk221LogOuterCertificate, logK := sk221LogKCertificate, logChi := chi133LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (6392335229/6392255488) } }, logDArg := sk221LogDArgCertificate }

private noncomputable def leaf2735InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2735LocalValidity :
    LeafFacts leaf2735Box leaf2735Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2735Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (3196207485/3196127744) }) = true
      norm_num [leaf2735Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2735CertificateValid :
    WideCertificateValid leaf2735Box leaf2735Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk221ValidityFacts chi133ValidityFacts
    leaf2735LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2735CoverageChecked :
    coverageCheck (innerAD leaf2735Box) leaf2735InnerLog = true := by
  rfl'

private theorem leaf2735InnerLogValid :
    leaf2735InnerLog.Valid 8 (innerAD leaf2735Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2735CoverageChecked

private noncomputable def leaf2735InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814645/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2735InputLogOnePlusV_eq :
    leaf2735InputLogOnePlusV = outerEnclosure 24
      (leaf2735Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2735RoundedFacts : LeafRoundedFacts 8
    leaf2735Certificate.logOnePlusV leaf2735InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2735InputLogOnePlusV_eq }

private noncomputable def leaf2735Inputs : Inputs :=
  inputsOfCaches globalInput sk221RoundedInputs
    chi133InputQChi innerPair56Input
    leaf2735InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2735LowerChecked :
    lowerCheck 24 leaf2735Box leaf2735Inputs = true := by
  rfl'

private theorem leaf2735CoversExact : CoversExact 8
    leaf2735Box leaf2735Certificate leaf2735InnerLog leaf2735Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk221RoundedFacts chi133RoundedFacts
    innerPair56RoundedFacts leaf2735RoundedFacts (by rfl)

private theorem leaf2735FlatSound : Sound leaf2735Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2735CertificateValid
    leaf2735InnerLogValid leaf2735CoversExact leaf2735LowerChecked

private noncomputable def leaf2736Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (237/64), kHi := (119/32), chiLo := (11/64), chiHi := (45/256) }

private noncomputable def leaf2736Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742389/1073741824) }, vSqrt := { lower := (8191/8192), upper := (25362045/25361408) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1757076189/1073741824) }, upper := { exponent := 0, mantissa := (13547/8192) } }, logOuter := sk222LogOuterCertificate, logK := sk222LogKCertificate, logChi := chi133LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (50723453/50722816) } }, logDArg := sk222LogDArgCertificate }

private noncomputable def leaf2736InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2736LocalValidity :
    LeafFacts leaf2736Box leaf2736Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2736Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (25362045/25361408) }) = true
      norm_num [leaf2736Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2736CertificateValid :
    WideCertificateValid leaf2736Box leaf2736Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk222ValidityFacts chi133ValidityFacts
    leaf2736LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2736CoverageChecked :
    coverageCheck (innerAD leaf2736Box) leaf2736InnerLog = true := by
  rfl'

private theorem leaf2736InnerLogValid :
    leaf2736InnerLog.Valid 8 (innerAD leaf2736Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2736CoverageChecked

private noncomputable def leaf2736InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629291/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2736InputLogOnePlusV_eq :
    leaf2736InputLogOnePlusV = outerEnclosure 24
      (leaf2736Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2736RoundedFacts : LeafRoundedFacts 8
    leaf2736Certificate.logOnePlusV leaf2736InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2736InputLogOnePlusV_eq }

private noncomputable def leaf2736Inputs : Inputs :=
  inputsOfCaches globalInput sk222RoundedInputs
    chi133InputQChi innerPair56Input
    leaf2736InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2736LowerChecked :
    lowerCheck 24 leaf2736Box leaf2736Inputs = true := by
  rfl'

private theorem leaf2736CoversExact : CoversExact 8
    leaf2736Box leaf2736Certificate leaf2736InnerLog leaf2736Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk222RoundedFacts chi133RoundedFacts
    innerPair56RoundedFacts leaf2736RoundedFacts (by rfl)

private theorem leaf2736FlatSound : Sound leaf2736Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2736CertificateValid
    leaf2736InnerLogValid leaf2736CoversExact leaf2736LowerChecked

private noncomputable def leaf2737Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (237/64), chiLo := (45/256), chiHi := (23/128) }

private noncomputable def leaf2737Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742389/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433371648) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1769658333/1073741824) }, upper := { exponent := 0, mantissa := (13643/8192) } }, logOuter := sk221LogOuterCertificate, logK := sk221LogKCertificate, logChi := chi134LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870293503/274866743296) } }, logDArg := sk221LogDArgCertificate }

private noncomputable def leaf2737InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2737LocalValidity :
    LeafFacts leaf2737Box leaf2737Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2737Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433371648) }) = true
      norm_num [leaf2737Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2737CertificateValid :
    WideCertificateValid leaf2737Box leaf2737Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk221ValidityFacts chi134ValidityFacts
    leaf2737LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2737CoverageChecked :
    coverageCheck (innerAD leaf2737Box) leaf2737InnerLog = true := by
  rfl'

private theorem leaf2737InnerLogValid :
    leaf2737InnerLog.Valid 8 (innerAD leaf2737Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2737CoverageChecked

private noncomputable def leaf2737InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629297/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2737InputLogOnePlusV_eq :
    leaf2737InputLogOnePlusV = outerEnclosure 24
      (leaf2737Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2737RoundedFacts : LeafRoundedFacts 8
    leaf2737Certificate.logOnePlusV leaf2737InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2737InputLogOnePlusV_eq }

private noncomputable def leaf2737Inputs : Inputs :=
  inputsOfCaches globalInput sk221RoundedInputs
    chi134InputQChi innerPair56Input
    leaf2737InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2737LowerChecked :
    lowerCheck 24 leaf2737Box leaf2737Inputs = true := by
  rfl'

private theorem leaf2737CoversExact : CoversExact 8
    leaf2737Box leaf2737Certificate leaf2737InnerLog leaf2737Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk221RoundedFacts chi134RoundedFacts
    innerPair56RoundedFacts leaf2737RoundedFacts (by rfl)

private theorem leaf2737FlatSound : Sound leaf2737Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2737CertificateValid
    leaf2737InnerLogValid leaf2737CoversExact leaf2737LowerChecked

private noncomputable def leaf2738Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (237/64), kHi := (119/32), chiLo := (45/256), chiHi := (23/128) }

private noncomputable def leaf2738Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742391/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45811116032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1772607271/1073741824) }, upper := { exponent := 0, mantissa := (6833/4096) } }, logOuter := sk222LogOuterCertificate, logK := sk222LogKCertificate, logChi := chi134LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623423317/91622232064) } }, logDArg := sk222LogDArgCertificate }

private noncomputable def leaf2738InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2738LocalValidity :
    LeafFacts leaf2738Box leaf2738Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2738Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45811116032) }) = true
      norm_num [leaf2738Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2738CertificateValid :
    WideCertificateValid leaf2738Box leaf2738Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk222ValidityFacts chi134ValidityFacts
    leaf2738LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2738CoverageChecked :
    coverageCheck (innerAD leaf2738Box) leaf2738InnerLog = true := by
  rfl'

private theorem leaf2738InnerLogValid :
    leaf2738InnerLog.Valid 8 (innerAD leaf2738Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2738CoverageChecked

private noncomputable def leaf2738InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629299/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2738InputLogOnePlusV_eq :
    leaf2738InputLogOnePlusV = outerEnclosure 24
      (leaf2738Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2738RoundedFacts : LeafRoundedFacts 8
    leaf2738Certificate.logOnePlusV leaf2738InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2738InputLogOnePlusV_eq }

private noncomputable def leaf2738Inputs : Inputs :=
  inputsOfCaches globalInput sk222RoundedInputs
    chi134InputQChi innerPair56Input
    leaf2738InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2738LowerChecked :
    lowerCheck 24 leaf2738Box leaf2738Inputs = true := by
  rfl'

private theorem leaf2738CoversExact : CoversExact 8
    leaf2738Box leaf2738Certificate leaf2738InnerLog leaf2738Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk222RoundedFacts chi134RoundedFacts
    innerPair56RoundedFacts leaf2738RoundedFacts (by rfl)

private theorem leaf2738FlatSound : Sound leaf2738Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2738CertificateValid
    leaf2738InnerLogValid leaf2738CoversExact leaf2738LowerChecked

private noncomputable def leaf2739Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (239/64), chiLo := (11/64), chiHi := (45/256) }

private noncomputable def leaf2739Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742391/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433446912) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1759959595/1073741824) }, upper := { exponent := 0, mantissa := (27139/16384) } }, logOuter := sk223LogOuterCertificate, logK := sk223LogKCertificate, logChi := chi133LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870368767/274866893824) } }, logDArg := sk223LogDArgCertificate }

private noncomputable def leaf2739InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2739LocalValidity :
    LeafFacts leaf2739Box leaf2739Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2739Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433446912) }) = true
      norm_num [leaf2739Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2739CertificateValid :
    WideCertificateValid leaf2739Box leaf2739Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk223ValidityFacts chi133ValidityFacts
    leaf2739LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2739CoverageChecked :
    coverageCheck (innerAD leaf2739Box) leaf2739InnerLog = true := by
  rfl'

private theorem leaf2739InnerLogValid :
    leaf2739InnerLog.Valid 8 (innerAD leaf2739Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2739CoverageChecked

private noncomputable def leaf2739InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629293/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2739InputLogOnePlusV_eq :
    leaf2739InputLogOnePlusV = outerEnclosure 24
      (leaf2739Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2739RoundedFacts : LeafRoundedFacts 8
    leaf2739Certificate.logOnePlusV leaf2739InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2739InputLogOnePlusV_eq }

private noncomputable def leaf2739Inputs : Inputs :=
  inputsOfCaches globalInput sk223RoundedInputs
    chi133InputQChi innerPair56Input
    leaf2739InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2739LowerChecked :
    lowerCheck 24 leaf2739Box leaf2739Inputs = true := by
  rfl'

private theorem leaf2739CoversExact : CoversExact 8
    leaf2739Box leaf2739Certificate leaf2739InnerLog leaf2739Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk223RoundedFacts chi133RoundedFacts
    innerPair56RoundedFacts leaf2739RoundedFacts (by rfl)

private theorem leaf2739FlatSound : Sound leaf2739Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2739CertificateValid
    leaf2739InnerLogValid leaf2739CoversExact leaf2739LowerChecked

private noncomputable def leaf2740Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (239/64), kHi := (15/4), chiLo := (11/64), chiHi := (45/256) }

private noncomputable def leaf2740Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742393/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433423872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1762843001/1073741824) }, upper := { exponent := 0, mantissa := (1699/1024) } }, logOuter := sk224LogOuterCertificate, logK := sk224LogKCertificate, logChi := chi133LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870345727/274866847744) } }, logDArg := sk224LogDArgCertificate }

private noncomputable def leaf2740InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2740LocalValidity :
    LeafFacts leaf2740Box leaf2740Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2740Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433423872) }) = true
      norm_num [leaf2740Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2740CertificateValid :
    WideCertificateValid leaf2740Box leaf2740Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk224ValidityFacts chi133ValidityFacts
    leaf2740LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2740CoverageChecked :
    coverageCheck (innerAD leaf2740Box) leaf2740InnerLog = true := by
  rfl'

private theorem leaf2740InnerLogValid :
    leaf2740InnerLog.Valid 8 (innerAD leaf2740Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2740CoverageChecked

private noncomputable def leaf2740InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814647/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2740InputLogOnePlusV_eq :
    leaf2740InputLogOnePlusV = outerEnclosure 24
      (leaf2740Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2740RoundedFacts : LeafRoundedFacts 8
    leaf2740Certificate.logOnePlusV leaf2740InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2740InputLogOnePlusV_eq }

private noncomputable def leaf2740Inputs : Inputs :=
  inputsOfCaches globalInput sk224RoundedInputs
    chi133InputQChi innerPair56Input
    leaf2740InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2740LowerChecked :
    lowerCheck 24 leaf2740Box leaf2740Inputs = true := by
  rfl'

private theorem leaf2740CoversExact : CoversExact 8
    leaf2740Box leaf2740Certificate leaf2740InnerLog leaf2740Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk224RoundedFacts chi133RoundedFacts
    innerPair56RoundedFacts leaf2740RoundedFacts (by rfl)

private theorem leaf2740FlatSound : Sound leaf2740Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2740CertificateValid
    leaf2740InnerLogValid leaf2740CoversExact leaf2740LowerChecked

private noncomputable def leaf2741Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (239/64), chiLo := (45/256), chiHi := (23/128) }

private noncomputable def leaf2741Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742393/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433324544) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1775556209/1073741824) }, upper := { exponent := 0, mantissa := (13689/8192) } }, logOuter := sk223LogOuterCertificate, logK := sk223LogKCertificate, logChi := chi134LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870246399/274866649088) } }, logDArg := sk223LogDArgCertificate }

private noncomputable def leaf2741InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2741LocalValidity :
    LeafFacts leaf2741Box leaf2741Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2741Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433324544) }) = true
      norm_num [leaf2741Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2741CertificateValid :
    WideCertificateValid leaf2741Box leaf2741Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk223ValidityFacts chi134ValidityFacts
    leaf2741LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2741CoverageChecked :
    coverageCheck (innerAD leaf2741Box) leaf2741InnerLog = true := by
  rfl'

private theorem leaf2741InnerLogValid :
    leaf2741InnerLog.Valid 8 (innerAD leaf2741Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2741CoverageChecked

private noncomputable def leaf2741InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907325/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2741InputLogOnePlusV_eq :
    leaf2741InputLogOnePlusV = outerEnclosure 24
      (leaf2741Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2741RoundedFacts : LeafRoundedFacts 8
    leaf2741Certificate.logOnePlusV leaf2741InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2741InputLogOnePlusV_eq }

private noncomputable def leaf2741Inputs : Inputs :=
  inputsOfCaches globalInput sk223RoundedInputs
    chi134InputQChi innerPair56Input
    leaf2741InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2741LowerChecked :
    lowerCheck 24 leaf2741Box leaf2741Inputs = true := by
  rfl'

private theorem leaf2741CoversExact : CoversExact 8
    leaf2741Box leaf2741Certificate leaf2741InnerLog leaf2741Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk223RoundedFacts chi134RoundedFacts
    innerPair56RoundedFacts leaf2741RoundedFacts (by rfl)

private theorem leaf2741FlatSound : Sound leaf2741Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2741CertificateValid
    leaf2741InnerLogValid leaf2741CoversExact leaf2741LowerChecked

private noncomputable def leaf2742Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (239/64), kHi := (15/4), chiLo := (45/256), chiHi := (23/128) }

private noncomputable def leaf2742Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742395/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433300992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1778505147/1073741824) }, upper := { exponent := 0, mantissa := (857/512) } }, logOuter := sk224LogOuterCertificate, logK := sk224LogKCertificate, logChi := chi134LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870222847/274866601984) } }, logDArg := sk224LogDArgCertificate }

private noncomputable def leaf2742InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2742LocalValidity :
    LeafFacts leaf2742Box leaf2742Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2742Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433300992) }) = true
      norm_num [leaf2742Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2742CertificateValid :
    WideCertificateValid leaf2742Box leaf2742Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk224ValidityFacts chi134ValidityFacts
    leaf2742LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2742CoverageChecked :
    coverageCheck (innerAD leaf2742Box) leaf2742InnerLog = true := by
  rfl'

private theorem leaf2742InnerLogValid :
    leaf2742InnerLog.Valid 8 (innerAD leaf2742Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2742CoverageChecked

private noncomputable def leaf2742InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814651/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2742InputLogOnePlusV_eq :
    leaf2742InputLogOnePlusV = outerEnclosure 24
      (leaf2742Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2742RoundedFacts : LeafRoundedFacts 8
    leaf2742Certificate.logOnePlusV leaf2742InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2742InputLogOnePlusV_eq }

private noncomputable def leaf2742Inputs : Inputs :=
  inputsOfCaches globalInput sk224RoundedInputs
    chi134InputQChi innerPair56Input
    leaf2742InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2742LowerChecked :
    lowerCheck 24 leaf2742Box leaf2742Inputs = true := by
  rfl'

private theorem leaf2742CoversExact : CoversExact 8
    leaf2742Box leaf2742Certificate leaf2742InnerLog leaf2742Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk224RoundedFacts chi134RoundedFacts
    innerPair56RoundedFacts leaf2742RoundedFacts (by rfl)

private theorem leaf2742FlatSound : Sound leaf2742Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2742CertificateValid
    leaf2742InnerLogValid leaf2742CoversExact leaf2742LowerChecked

private noncomputable def leaf2743Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (237/64), chiLo := (23/128), chiHi := (47/256) }

private noncomputable def leaf2743Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742391/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433250304) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1785123883/1073741824) }, upper := { exponent := 0, mantissa := (27523/16384) } }, logOuter := sk221LogOuterCertificate, logK := sk221LogKCertificate, logChi := chi135LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870172159/274866500608) } }, logDArg := sk221LogDArgCertificate }

private noncomputable def leaf2743InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2743LocalValidity :
    LeafFacts leaf2743Box leaf2743Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2743Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433250304) }) = true
      norm_num [leaf2743Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2743CertificateValid :
    WideCertificateValid leaf2743Box leaf2743Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk221ValidityFacts chi135ValidityFacts
    leaf2743LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2743CoverageChecked :
    coverageCheck (innerAD leaf2743Box) leaf2743InnerLog = true := by
  rfl'

private theorem leaf2743InnerLogValid :
    leaf2743InnerLog.Valid 8 (innerAD leaf2743Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2743CoverageChecked

private noncomputable def leaf2743InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629305/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2743InputLogOnePlusV_eq :
    leaf2743InputLogOnePlusV = outerEnclosure 24
      (leaf2743Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2743RoundedFacts : LeafRoundedFacts 8
    leaf2743Certificate.logOnePlusV leaf2743InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2743InputLogOnePlusV_eq }

private noncomputable def leaf2743Inputs : Inputs :=
  inputsOfCaches globalInput sk221RoundedInputs
    chi135InputQChi innerPair56Input
    leaf2743InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2743LowerChecked :
    lowerCheck 24 leaf2743Box leaf2743Inputs = true := by
  rfl'

private theorem leaf2743CoversExact : CoversExact 8
    leaf2743Box leaf2743Certificate leaf2743InnerLog leaf2743Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk221RoundedFacts chi135RoundedFacts
    innerPair56RoundedFacts leaf2743RoundedFacts (by rfl)

private theorem leaf2743FlatSound : Sound leaf2743Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2743CertificateValid
    leaf2743InnerLogValid leaf2743CoversExact leaf2743LowerChecked

private noncomputable def leaf2744Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (237/64), kHi := (119/32), chiLo := (23/128), chiHi := (47/256) }

private noncomputable def leaf2744Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742393/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486645248) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1788138353/1073741824) }, upper := { exponent := 0, mantissa := (13785/8192) } }, logOuter := sk222LogOuterCertificate, logK := sk222LogKCertificate, logChi := chi135LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54974029619/54973290496) } }, logDArg := sk222LogDArgCertificate }

private noncomputable def leaf2744InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2744LocalValidity :
    LeafFacts leaf2744Box leaf2744Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2744Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486645248) }) = true
      norm_num [leaf2744Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2744CertificateValid :
    WideCertificateValid leaf2744Box leaf2744Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk222ValidityFacts chi135ValidityFacts
    leaf2744LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2744CoverageChecked :
    coverageCheck (innerAD leaf2744Box) leaf2744InnerLog = true := by
  rfl'

private theorem leaf2744InnerLogValid :
    leaf2744InnerLog.Valid 8 (innerAD leaf2744Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2744CoverageChecked

private noncomputable def leaf2744InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814653/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2744InputLogOnePlusV_eq :
    leaf2744InputLogOnePlusV = outerEnclosure 24
      (leaf2744Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2744RoundedFacts : LeafRoundedFacts 8
    leaf2744Certificate.logOnePlusV leaf2744InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2744InputLogOnePlusV_eq }

private noncomputable def leaf2744Inputs : Inputs :=
  inputsOfCaches globalInput sk222RoundedInputs
    chi135InputQChi innerPair56Input
    leaf2744InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2744LowerChecked :
    lowerCheck 24 leaf2744Box leaf2744Inputs = true := by
  rfl'

private theorem leaf2744CoversExact : CoversExact 8
    leaf2744Box leaf2744Certificate leaf2744InnerLog leaf2744Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk222RoundedFacts chi135RoundedFacts
    innerPair56RoundedFacts leaf2744RoundedFacts (by rfl)

private theorem leaf2744FlatSound : Sound leaf2744Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2744CertificateValid
    leaf2744InnerLogValid leaf2744CoversExact leaf2744LowerChecked

private noncomputable def leaf2745Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (237/64), chiLo := (47/256), chiHi := (3/16) }

private noncomputable def leaf2745Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742393/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486625792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1800589433/1073741824) }, upper := { exponent := 0, mantissa := (1735/1024) } }, logOuter := sk221LogOuterCertificate, logK := sk221LogKCertificate, logChi := chi136LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54974010163/54973251584) } }, logDArg := sk221LogDArgCertificate }

private noncomputable def leaf2745InnerLog : WideLogData :=
  innerPair420Data

set_option maxRecDepth 1000000 in
private theorem leaf2745LocalValidity :
    LeafFacts leaf2745Box leaf2745Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2745Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486625792) }) = true
      norm_num [leaf2745Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2745CertificateValid :
    WideCertificateValid leaf2745Box leaf2745Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk221ValidityFacts chi136ValidityFacts
    leaf2745LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2745CoverageChecked :
    coverageCheck (innerAD leaf2745Box) leaf2745InnerLog = true := by
  rfl'

private theorem leaf2745InnerLogValid :
    leaf2745InnerLog.Valid 8 (innerAD leaf2745Box) :=
  wideLogDataValid_of_cachedCheck endpoint133PositiveFacts
    endpoint20PositiveFacts.valid leaf2745CoverageChecked

private noncomputable def leaf2745InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (45427/65536) }

set_option maxRecDepth 1000000 in
private theorem leaf2745InputLogOnePlusV_eq :
    leaf2745InputLogOnePlusV = outerEnclosure 24
      (leaf2745Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2745RoundedFacts : LeafRoundedFacts 8
    leaf2745Certificate.logOnePlusV leaf2745InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2745InputLogOnePlusV_eq }

private noncomputable def leaf2745Inputs : Inputs :=
  inputsOfCaches globalInput sk221RoundedInputs
    chi136InputQChi innerPair420Input
    leaf2745InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2745LowerChecked :
    lowerCheck 24 leaf2745Box leaf2745Inputs = true := by
  rfl'

private theorem leaf2745CoversExact : CoversExact 8
    leaf2745Box leaf2745Certificate leaf2745InnerLog leaf2745Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk221RoundedFacts chi136RoundedFacts
    innerPair420RoundedFacts leaf2745RoundedFacts (by rfl)

private theorem leaf2745FlatSound : Sound leaf2745Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2745CertificateValid
    leaf2745InnerLogValid leaf2745CoversExact leaf2745LowerChecked

private noncomputable def leaf2746Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (237/64), kHi := (119/32), chiLo := (47/256), chiHi := (3/16) }

private noncomputable def leaf2746Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742395/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433104384) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1803669435/1073741824) }, upper := { exponent := 0, mantissa := (869/512) } }, logOuter := sk222LogOuterCertificate, logK := sk222LogKCertificate, logChi := chi136LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870026239/274866208768) } }, logDArg := sk222LogDArgCertificate }

private noncomputable def leaf2746InnerLog : WideLogData :=
  innerPair420Data

set_option maxRecDepth 1000000 in
private theorem leaf2746LocalValidity :
    LeafFacts leaf2746Box leaf2746Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2746Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433104384) }) = true
      norm_num [leaf2746Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2746CertificateValid :
    WideCertificateValid leaf2746Box leaf2746Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk222ValidityFacts chi136ValidityFacts
    leaf2746LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2746CoverageChecked :
    coverageCheck (innerAD leaf2746Box) leaf2746InnerLog = true := by
  rfl'

private theorem leaf2746InnerLogValid :
    leaf2746InnerLog.Valid 8 (innerAD leaf2746Box) :=
  wideLogDataValid_of_cachedCheck endpoint133PositiveFacts
    endpoint20PositiveFacts.valid leaf2746CoverageChecked

private noncomputable def leaf2746InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814657/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2746InputLogOnePlusV_eq :
    leaf2746InputLogOnePlusV = outerEnclosure 24
      (leaf2746Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2746RoundedFacts : LeafRoundedFacts 8
    leaf2746Certificate.logOnePlusV leaf2746InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2746InputLogOnePlusV_eq }

private noncomputable def leaf2746Inputs : Inputs :=
  inputsOfCaches globalInput sk222RoundedInputs
    chi136InputQChi innerPair420Input
    leaf2746InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2746LowerChecked :
    lowerCheck 24 leaf2746Box leaf2746Inputs = true := by
  rfl'

private theorem leaf2746CoversExact : CoversExact 8
    leaf2746Box leaf2746Certificate leaf2746InnerLog leaf2746Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk222RoundedFacts chi136RoundedFacts
    innerPair420RoundedFacts leaf2746RoundedFacts (by rfl)

private theorem leaf2746FlatSound : Sound leaf2746Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2746CertificateValid
    leaf2746InnerLogValid leaf2746CoversExact leaf2746LowerChecked

private noncomputable def leaf2747Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (239/64), chiLo := (23/128), chiHi := (47/256) }

private noncomputable def leaf2747Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742395/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45811067392) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1791152823/1073741824) }, upper := { exponent := 0, mantissa := (27617/16384) } }, logOuter := sk223LogOuterCertificate, logK := sk223LogKCertificate, logChi := chi135LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623374677/91622134784) } }, logDArg := sk223LogDArgCertificate }

private noncomputable def leaf2747InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2747LocalValidity :
    LeafFacts leaf2747Box leaf2747Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2747Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45811067392) }) = true
      norm_num [leaf2747Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2747CertificateValid :
    WideCertificateValid leaf2747Box leaf2747Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk223ValidityFacts chi135ValidityFacts
    leaf2747LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2747CoverageChecked :
    coverageCheck (innerAD leaf2747Box) leaf2747InnerLog = true := by
  rfl'

private theorem leaf2747InnerLogValid :
    leaf2747InnerLog.Valid 8 (innerAD leaf2747Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2747CoverageChecked

private noncomputable def leaf2747InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907327/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2747InputLogOnePlusV_eq :
    leaf2747InputLogOnePlusV = outerEnclosure 24
      (leaf2747Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2747RoundedFacts : LeafRoundedFacts 8
    leaf2747Certificate.logOnePlusV leaf2747InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2747InputLogOnePlusV_eq }

private noncomputable def leaf2747Inputs : Inputs :=
  inputsOfCaches globalInput sk223RoundedInputs
    chi135InputQChi innerPair56Input
    leaf2747InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2747LowerChecked :
    lowerCheck 24 leaf2747Box leaf2747Inputs = true := by
  rfl'

private theorem leaf2747CoversExact : CoversExact 8
    leaf2747Box leaf2747Certificate leaf2747InnerLog leaf2747Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk223RoundedFacts chi135RoundedFacts
    innerPair56RoundedFacts leaf2747RoundedFacts (by rfl)

private theorem leaf2747FlatSound : Sound leaf2747Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2747CertificateValid
    leaf2747InnerLogValid leaf2747CoversExact leaf2747LowerChecked

private noncomputable def leaf2748Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (239/64), kHi := (15/4), chiLo := (23/128), chiHi := (47/256) }

private noncomputable def leaf2748Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742397/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433178112) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1794167293/1073741824) }, upper := { exponent := 0, mantissa := (1729/1024) } }, logOuter := sk224LogOuterCertificate, logK := sk224LogKCertificate, logChi := chi135LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870099967/274866356224) } }, logDArg := sk224LogDArgCertificate }

private noncomputable def leaf2748InnerLog : WideLogData :=
  innerPair173Data

set_option maxRecDepth 1000000 in
private theorem leaf2748LocalValidity :
    LeafFacts leaf2748Box leaf2748Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2748Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433178112) }) = true
      norm_num [leaf2748Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2748CertificateValid :
    WideCertificateValid leaf2748Box leaf2748Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk224ValidityFacts chi135ValidityFacts
    leaf2748LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2748CoverageChecked :
    coverageCheck (innerAD leaf2748Box) leaf2748InnerLog = true := by
  rfl'

private theorem leaf2748InnerLogValid :
    leaf2748InnerLog.Valid 8 (innerAD leaf2748Box) :=
  wideLogDataValid_of_cachedCheck endpoint48PositiveFacts
    endpoint20PositiveFacts.valid leaf2748CoverageChecked

private noncomputable def leaf2748InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629309/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2748InputLogOnePlusV_eq :
    leaf2748InputLogOnePlusV = outerEnclosure 24
      (leaf2748Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2748RoundedFacts : LeafRoundedFacts 8
    leaf2748Certificate.logOnePlusV leaf2748InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2748InputLogOnePlusV_eq }

private noncomputable def leaf2748Inputs : Inputs :=
  inputsOfCaches globalInput sk224RoundedInputs
    chi135InputQChi innerPair173Input
    leaf2748InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2748LowerChecked :
    lowerCheck 24 leaf2748Box leaf2748Inputs = true := by
  rfl'

private theorem leaf2748CoversExact : CoversExact 8
    leaf2748Box leaf2748Certificate leaf2748InnerLog leaf2748Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk224RoundedFacts chi135RoundedFacts
    innerPair173RoundedFacts leaf2748RoundedFacts (by rfl)

private theorem leaf2748FlatSound : Sound leaf2748Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2748CertificateValid
    leaf2748InnerLogValid leaf2748CoversExact leaf2748LowerChecked

private noncomputable def leaf2749Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (239/64), chiLo := (47/256), chiHi := (3/16) }

private noncomputable def leaf2749Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742397/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433079808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1806749437/1073741824) }, upper := { exponent := 0, mantissa := (1741/1024) } }, logOuter := sk223LogOuterCertificate, logK := sk223LogKCertificate, logChi := chi136LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870001663/274866159616) } }, logDArg := sk223LogDArgCertificate }

private noncomputable def leaf2749InnerLog : WideLogData :=
  innerPair420Data

set_option maxRecDepth 1000000 in
private theorem leaf2749LocalValidity :
    LeafFacts leaf2749Box leaf2749Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2749Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433079808) }) = true
      norm_num [leaf2749Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2749CertificateValid :
    WideCertificateValid leaf2749Box leaf2749Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk223ValidityFacts chi136ValidityFacts
    leaf2749LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2749CoverageChecked :
    coverageCheck (innerAD leaf2749Box) leaf2749InnerLog = true := by
  rfl'

private theorem leaf2749InnerLogValid :
    leaf2749InnerLog.Valid 8 (innerAD leaf2749Box) :=
  wideLogDataValid_of_cachedCheck endpoint133PositiveFacts
    endpoint20PositiveFacts.valid leaf2749CoverageChecked

private noncomputable def leaf2749InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629315/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2749InputLogOnePlusV_eq :
    leaf2749InputLogOnePlusV = outerEnclosure 24
      (leaf2749Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2749RoundedFacts : LeafRoundedFacts 8
    leaf2749Certificate.logOnePlusV leaf2749InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2749InputLogOnePlusV_eq }

private noncomputable def leaf2749Inputs : Inputs :=
  inputsOfCaches globalInput sk223RoundedInputs
    chi136InputQChi innerPair420Input
    leaf2749InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2749LowerChecked :
    lowerCheck 24 leaf2749Box leaf2749Inputs = true := by
  rfl'

private theorem leaf2749CoversExact : CoversExact 8
    leaf2749Box leaf2749Certificate leaf2749InnerLog leaf2749Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk223RoundedFacts chi136RoundedFacts
    innerPair420RoundedFacts leaf2749RoundedFacts (by rfl)

private theorem leaf2749FlatSound : Sound leaf2749Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2749CertificateValid
    leaf2749InnerLogValid leaf2749CoversExact leaf2749LowerChecked

private noncomputable def leaf2750Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (239/64), kHi := (15/4), chiLo := (47/256), chiHi := (3/16) }

private noncomputable def leaf2750Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742399/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433055232) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1809829439/1073741824) }, upper := { exponent := 0, mantissa := (109/64) } }, logOuter := sk224LogOuterCertificate, logK := sk224LogKCertificate, logChi := chi136LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869977087/274866110464) } }, logDArg := sk224LogDArgCertificate }

private noncomputable def leaf2750InnerLog : WideLogData :=
  innerPair420Data

set_option maxRecDepth 1000000 in
private theorem leaf2750LocalValidity :
    LeafFacts leaf2750Box leaf2750Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2750Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433055232) }) = true
      norm_num [leaf2750Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2750CertificateValid :
    WideCertificateValid leaf2750Box leaf2750Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk224ValidityFacts chi136ValidityFacts
    leaf2750LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2750CoverageChecked :
    coverageCheck (innerAD leaf2750Box) leaf2750InnerLog = true := by
  rfl'

private theorem leaf2750InnerLogValid :
    leaf2750InnerLog.Valid 8 (innerAD leaf2750Box) :=
  wideLogDataValid_of_cachedCheck endpoint133PositiveFacts
    endpoint20PositiveFacts.valid leaf2750CoverageChecked

private noncomputable def leaf2750InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629317/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2750InputLogOnePlusV_eq :
    leaf2750InputLogOnePlusV = outerEnclosure 24
      (leaf2750Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2750RoundedFacts : LeafRoundedFacts 8
    leaf2750Certificate.logOnePlusV leaf2750InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2750InputLogOnePlusV_eq }

private noncomputable def leaf2750Inputs : Inputs :=
  inputsOfCaches globalInput sk224RoundedInputs
    chi136InputQChi innerPair420Input
    leaf2750InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2750LowerChecked :
    lowerCheck 24 leaf2750Box leaf2750Inputs = true := by
  rfl'

private theorem leaf2750CoversExact : CoversExact 8
    leaf2750Box leaf2750Certificate leaf2750InnerLog leaf2750Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk224RoundedFacts chi136RoundedFacts
    innerPair420RoundedFacts leaf2750RoundedFacts (by rfl)

private theorem leaf2750FlatSound : Sound leaf2750Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2750CertificateValid
    leaf2750InnerLogValid leaf2750CoversExact leaf2750LowerChecked

private noncomputable def component57Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (5/32), chiHi := (41/256) }

set_option maxRecDepth 1000000 in
private theorem component57Node0_sound : Sound component57Node0Box :=
  sound_of_literal_split component57Node0Box leaf2687Box leaf2688Box
    .k (233/64) (by rfl) (by rfl)
    leaf2687FlatSound leaf2688FlatSound

private noncomputable def component57Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (41/256), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component57Node1_sound : Sound component57Node1Box :=
  sound_of_literal_split component57Node1Box leaf2689Box leaf2690Box
    .k (233/64) (by rfl) (by rfl)
    leaf2689FlatSound leaf2690FlatSound

private noncomputable def component57Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component57Node2_sound : Sound component57Node2Box :=
  sound_of_literal_split component57Node2Box component57Node0Box component57Node1Box
    .chi (41/256) (by rfl) (by rfl)
    component57Node0_sound component57Node1_sound

private noncomputable def component57Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (5/32), chiHi := (41/256) }

set_option maxRecDepth 1000000 in
private theorem component57Node3_sound : Sound component57Node3Box :=
  sound_of_literal_split component57Node3Box leaf2691Box leaf2692Box
    .k (235/64) (by rfl) (by rfl)
    leaf2691FlatSound leaf2692FlatSound

private noncomputable def component57Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (41/256), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component57Node4_sound : Sound component57Node4Box :=
  sound_of_literal_split component57Node4Box leaf2693Box leaf2694Box
    .k (235/64) (by rfl) (by rfl)
    leaf2693FlatSound leaf2694FlatSound

private noncomputable def component57Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component57Node5_sound : Sound component57Node5Box :=
  sound_of_literal_split component57Node5Box component57Node3Box component57Node4Box
    .chi (41/256) (by rfl) (by rfl)
    component57Node3_sound component57Node4_sound

private noncomputable def component57Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component57Node6_sound : Sound component57Node6Box :=
  sound_of_literal_split component57Node6Box component57Node2Box component57Node5Box
    .k (117/32) (by rfl) (by rfl)
    component57Node2_sound component57Node5_sound

private noncomputable def component57Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (21/128), chiHi := (43/256) }

set_option maxRecDepth 1000000 in
private theorem component57Node7_sound : Sound component57Node7Box :=
  sound_of_literal_split component57Node7Box leaf2695Box leaf2696Box
    .k (233/64) (by rfl) (by rfl)
    leaf2695FlatSound leaf2696FlatSound

private noncomputable def component57Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (43/256), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component57Node8_sound : Sound component57Node8Box :=
  sound_of_literal_split component57Node8Box leaf2697Box leaf2698Box
    .k (233/64) (by rfl) (by rfl)
    leaf2697FlatSound leaf2698FlatSound

private noncomputable def component57Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component57Node9_sound : Sound component57Node9Box :=
  sound_of_literal_split component57Node9Box component57Node7Box component57Node8Box
    .chi (43/256) (by rfl) (by rfl)
    component57Node7_sound component57Node8_sound

private noncomputable def component57Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (21/128), chiHi := (43/256) }

set_option maxRecDepth 1000000 in
private theorem component57Node10_sound : Sound component57Node10Box :=
  sound_of_literal_split component57Node10Box leaf2699Box leaf2700Box
    .k (235/64) (by rfl) (by rfl)
    leaf2699FlatSound leaf2700FlatSound

private noncomputable def component57Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (43/256), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component57Node11_sound : Sound component57Node11Box :=
  sound_of_literal_split component57Node11Box leaf2701Box leaf2702Box
    .k (235/64) (by rfl) (by rfl)
    leaf2701FlatSound leaf2702FlatSound

private noncomputable def component57Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component57Node12_sound : Sound component57Node12Box :=
  sound_of_literal_split component57Node12Box component57Node10Box component57Node11Box
    .chi (43/256) (by rfl) (by rfl)
    component57Node10_sound component57Node11_sound

private noncomputable def component57Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component57Node13_sound : Sound component57Node13Box :=
  sound_of_literal_split component57Node13Box component57Node9Box component57Node12Box
    .k (117/32) (by rfl) (by rfl)
    component57Node9_sound component57Node12_sound

private noncomputable def component57Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (5/32), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component57Node14_sound : Sound component57Node14Box :=
  sound_of_literal_split component57Node14Box component57Node6Box component57Node13Box
    .chi (21/128) (by rfl) (by rfl)
    component57Node6_sound component57Node13_sound

private noncomputable def component57Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (5/32), chiHi := (41/256) }

set_option maxRecDepth 1000000 in
private theorem component57Node15_sound : Sound component57Node15Box :=
  sound_of_literal_split component57Node15Box leaf2703Box leaf2704Box
    .k (237/64) (by rfl) (by rfl)
    leaf2703FlatSound leaf2704FlatSound

private noncomputable def component57Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (41/256), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component57Node16_sound : Sound component57Node16Box :=
  sound_of_literal_split component57Node16Box leaf2705Box leaf2706Box
    .k (237/64) (by rfl) (by rfl)
    leaf2705FlatSound leaf2706FlatSound

private noncomputable def component57Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component57Node17_sound : Sound component57Node17Box :=
  sound_of_literal_split component57Node17Box component57Node15Box component57Node16Box
    .chi (41/256) (by rfl) (by rfl)
    component57Node15_sound component57Node16_sound

private noncomputable def component57Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (5/32), chiHi := (41/256) }

set_option maxRecDepth 1000000 in
private theorem component57Node18_sound : Sound component57Node18Box :=
  sound_of_literal_split component57Node18Box leaf2707Box leaf2708Box
    .k (239/64) (by rfl) (by rfl)
    leaf2707FlatSound leaf2708FlatSound

private noncomputable def component57Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (41/256), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component57Node19_sound : Sound component57Node19Box :=
  sound_of_literal_split component57Node19Box leaf2709Box leaf2710Box
    .k (239/64) (by rfl) (by rfl)
    leaf2709FlatSound leaf2710FlatSound

private noncomputable def component57Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component57Node20_sound : Sound component57Node20Box :=
  sound_of_literal_split component57Node20Box component57Node18Box component57Node19Box
    .chi (41/256) (by rfl) (by rfl)
    component57Node18_sound component57Node19_sound

private noncomputable def component57Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component57Node21_sound : Sound component57Node21Box :=
  sound_of_literal_split component57Node21Box component57Node17Box component57Node20Box
    .k (119/32) (by rfl) (by rfl)
    component57Node17_sound component57Node20_sound

private noncomputable def component57Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (21/128), chiHi := (43/256) }

set_option maxRecDepth 1000000 in
private theorem component57Node22_sound : Sound component57Node22Box :=
  sound_of_literal_split component57Node22Box leaf2711Box leaf2712Box
    .k (237/64) (by rfl) (by rfl)
    leaf2711FlatSound leaf2712FlatSound

private noncomputable def component57Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (43/256), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component57Node23_sound : Sound component57Node23Box :=
  sound_of_literal_split component57Node23Box leaf2713Box leaf2714Box
    .k (237/64) (by rfl) (by rfl)
    leaf2713FlatSound leaf2714FlatSound

private noncomputable def component57Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component57Node24_sound : Sound component57Node24Box :=
  sound_of_literal_split component57Node24Box component57Node22Box component57Node23Box
    .chi (43/256) (by rfl) (by rfl)
    component57Node22_sound component57Node23_sound

private noncomputable def component57Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (21/128), chiHi := (43/256) }

set_option maxRecDepth 1000000 in
private theorem component57Node25_sound : Sound component57Node25Box :=
  sound_of_literal_split component57Node25Box leaf2715Box leaf2716Box
    .k (239/64) (by rfl) (by rfl)
    leaf2715FlatSound leaf2716FlatSound

private noncomputable def component57Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (43/256), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component57Node26_sound : Sound component57Node26Box :=
  sound_of_literal_split component57Node26Box leaf2717Box leaf2718Box
    .k (239/64) (by rfl) (by rfl)
    leaf2717FlatSound leaf2718FlatSound

private noncomputable def component57Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component57Node27_sound : Sound component57Node27Box :=
  sound_of_literal_split component57Node27Box component57Node25Box component57Node26Box
    .chi (43/256) (by rfl) (by rfl)
    component57Node25_sound component57Node26_sound

private noncomputable def component57Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component57Node28_sound : Sound component57Node28Box :=
  sound_of_literal_split component57Node28Box component57Node24Box component57Node27Box
    .k (119/32) (by rfl) (by rfl)
    component57Node24_sound component57Node27_sound

private noncomputable def component57Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (5/32), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component57Node29_sound : Sound component57Node29Box :=
  sound_of_literal_split component57Node29Box component57Node21Box component57Node28Box
    .chi (21/128) (by rfl) (by rfl)
    component57Node21_sound component57Node28_sound

private noncomputable def component57Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (5/32), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component57Node30_sound : Sound component57Node30Box :=
  sound_of_literal_split component57Node30Box component57Node14Box component57Node29Box
    .k (59/16) (by rfl) (by rfl)
    component57Node14_sound component57Node29_sound

private noncomputable def component57Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (11/64), chiHi := (45/256) }

set_option maxRecDepth 1000000 in
private theorem component57Node31_sound : Sound component57Node31Box :=
  sound_of_literal_split component57Node31Box leaf2719Box leaf2720Box
    .k (233/64) (by rfl) (by rfl)
    leaf2719FlatSound leaf2720FlatSound

private noncomputable def component57Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (45/256), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component57Node32_sound : Sound component57Node32Box :=
  sound_of_literal_split component57Node32Box leaf2721Box leaf2722Box
    .k (233/64) (by rfl) (by rfl)
    leaf2721FlatSound leaf2722FlatSound

private noncomputable def component57Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (11/64), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component57Node33_sound : Sound component57Node33Box :=
  sound_of_literal_split component57Node33Box component57Node31Box component57Node32Box
    .chi (45/256) (by rfl) (by rfl)
    component57Node31_sound component57Node32_sound

private noncomputable def component57Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (11/64), chiHi := (45/256) }

set_option maxRecDepth 1000000 in
private theorem component57Node34_sound : Sound component57Node34Box :=
  sound_of_literal_split component57Node34Box leaf2723Box leaf2724Box
    .k (235/64) (by rfl) (by rfl)
    leaf2723FlatSound leaf2724FlatSound

private noncomputable def component57Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (45/256), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component57Node35_sound : Sound component57Node35Box :=
  sound_of_literal_split component57Node35Box leaf2725Box leaf2726Box
    .k (235/64) (by rfl) (by rfl)
    leaf2725FlatSound leaf2726FlatSound

private noncomputable def component57Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (11/64), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component57Node36_sound : Sound component57Node36Box :=
  sound_of_literal_split component57Node36Box component57Node34Box component57Node35Box
    .chi (45/256) (by rfl) (by rfl)
    component57Node34_sound component57Node35_sound

private noncomputable def component57Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (11/64), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component57Node37_sound : Sound component57Node37Box :=
  sound_of_literal_split component57Node37Box component57Node33Box component57Node36Box
    .k (117/32) (by rfl) (by rfl)
    component57Node33_sound component57Node36_sound

private noncomputable def component57Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (23/128), chiHi := (47/256) }

set_option maxRecDepth 1000000 in
private theorem component57Node38_sound : Sound component57Node38Box :=
  sound_of_literal_split component57Node38Box leaf2727Box leaf2728Box
    .k (233/64) (by rfl) (by rfl)
    leaf2727FlatSound leaf2728FlatSound

private noncomputable def component57Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (47/256), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component57Node39_sound : Sound component57Node39Box :=
  sound_of_literal_split component57Node39Box leaf2729Box leaf2730Box
    .k (233/64) (by rfl) (by rfl)
    leaf2729FlatSound leaf2730FlatSound

private noncomputable def component57Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (23/128), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component57Node40_sound : Sound component57Node40Box :=
  sound_of_literal_split component57Node40Box component57Node38Box component57Node39Box
    .chi (47/256) (by rfl) (by rfl)
    component57Node38_sound component57Node39_sound

private noncomputable def component57Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (23/128), chiHi := (47/256) }

set_option maxRecDepth 1000000 in
private theorem component57Node41_sound : Sound component57Node41Box :=
  sound_of_literal_split component57Node41Box leaf2731Box leaf2732Box
    .k (235/64) (by rfl) (by rfl)
    leaf2731FlatSound leaf2732FlatSound

private noncomputable def component57Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (47/256), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component57Node42_sound : Sound component57Node42Box :=
  sound_of_literal_split component57Node42Box leaf2733Box leaf2734Box
    .k (235/64) (by rfl) (by rfl)
    leaf2733FlatSound leaf2734FlatSound

private noncomputable def component57Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (23/128), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component57Node43_sound : Sound component57Node43Box :=
  sound_of_literal_split component57Node43Box component57Node41Box component57Node42Box
    .chi (47/256) (by rfl) (by rfl)
    component57Node41_sound component57Node42_sound

private noncomputable def component57Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (23/128), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component57Node44_sound : Sound component57Node44Box :=
  sound_of_literal_split component57Node44Box component57Node40Box component57Node43Box
    .k (117/32) (by rfl) (by rfl)
    component57Node40_sound component57Node43_sound

private noncomputable def component57Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (11/64), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component57Node45_sound : Sound component57Node45Box :=
  sound_of_literal_split component57Node45Box component57Node37Box component57Node44Box
    .chi (23/128) (by rfl) (by rfl)
    component57Node37_sound component57Node44_sound

private noncomputable def component57Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (11/64), chiHi := (45/256) }

set_option maxRecDepth 1000000 in
private theorem component57Node46_sound : Sound component57Node46Box :=
  sound_of_literal_split component57Node46Box leaf2735Box leaf2736Box
    .k (237/64) (by rfl) (by rfl)
    leaf2735FlatSound leaf2736FlatSound

private noncomputable def component57Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (45/256), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component57Node47_sound : Sound component57Node47Box :=
  sound_of_literal_split component57Node47Box leaf2737Box leaf2738Box
    .k (237/64) (by rfl) (by rfl)
    leaf2737FlatSound leaf2738FlatSound

private noncomputable def component57Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (11/64), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component57Node48_sound : Sound component57Node48Box :=
  sound_of_literal_split component57Node48Box component57Node46Box component57Node47Box
    .chi (45/256) (by rfl) (by rfl)
    component57Node46_sound component57Node47_sound

private noncomputable def component57Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (11/64), chiHi := (45/256) }

set_option maxRecDepth 1000000 in
private theorem component57Node49_sound : Sound component57Node49Box :=
  sound_of_literal_split component57Node49Box leaf2739Box leaf2740Box
    .k (239/64) (by rfl) (by rfl)
    leaf2739FlatSound leaf2740FlatSound

private noncomputable def component57Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (45/256), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component57Node50_sound : Sound component57Node50Box :=
  sound_of_literal_split component57Node50Box leaf2741Box leaf2742Box
    .k (239/64) (by rfl) (by rfl)
    leaf2741FlatSound leaf2742FlatSound

private noncomputable def component57Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (11/64), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component57Node51_sound : Sound component57Node51Box :=
  sound_of_literal_split component57Node51Box component57Node49Box component57Node50Box
    .chi (45/256) (by rfl) (by rfl)
    component57Node49_sound component57Node50_sound

private noncomputable def component57Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (11/64), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component57Node52_sound : Sound component57Node52Box :=
  sound_of_literal_split component57Node52Box component57Node48Box component57Node51Box
    .k (119/32) (by rfl) (by rfl)
    component57Node48_sound component57Node51_sound

private noncomputable def component57Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (23/128), chiHi := (47/256) }

set_option maxRecDepth 1000000 in
private theorem component57Node53_sound : Sound component57Node53Box :=
  sound_of_literal_split component57Node53Box leaf2743Box leaf2744Box
    .k (237/64) (by rfl) (by rfl)
    leaf2743FlatSound leaf2744FlatSound

private noncomputable def component57Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (47/256), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component57Node54_sound : Sound component57Node54Box :=
  sound_of_literal_split component57Node54Box leaf2745Box leaf2746Box
    .k (237/64) (by rfl) (by rfl)
    leaf2745FlatSound leaf2746FlatSound

private noncomputable def component57Node55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (23/128), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component57Node55_sound : Sound component57Node55Box :=
  sound_of_literal_split component57Node55Box component57Node53Box component57Node54Box
    .chi (47/256) (by rfl) (by rfl)
    component57Node53_sound component57Node54_sound

private noncomputable def component57Node56Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (23/128), chiHi := (47/256) }

set_option maxRecDepth 1000000 in
private theorem component57Node56_sound : Sound component57Node56Box :=
  sound_of_literal_split component57Node56Box leaf2747Box leaf2748Box
    .k (239/64) (by rfl) (by rfl)
    leaf2747FlatSound leaf2748FlatSound

private noncomputable def component57Node57Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (47/256), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component57Node57_sound : Sound component57Node57Box :=
  sound_of_literal_split component57Node57Box leaf2749Box leaf2750Box
    .k (239/64) (by rfl) (by rfl)
    leaf2749FlatSound leaf2750FlatSound

private noncomputable def component57Node58Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (23/128), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component57Node58_sound : Sound component57Node58Box :=
  sound_of_literal_split component57Node58Box component57Node56Box component57Node57Box
    .chi (47/256) (by rfl) (by rfl)
    component57Node56_sound component57Node57_sound

private noncomputable def component57Node59Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (23/128), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component57Node59_sound : Sound component57Node59Box :=
  sound_of_literal_split component57Node59Box component57Node55Box component57Node58Box
    .k (119/32) (by rfl) (by rfl)
    component57Node55_sound component57Node58_sound

private noncomputable def component57Node60Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (11/64), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component57Node60_sound : Sound component57Node60Box :=
  sound_of_literal_split component57Node60Box component57Node52Box component57Node59Box
    .chi (23/128) (by rfl) (by rfl)
    component57Node52_sound component57Node59_sound

private noncomputable def component57Node61Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (11/64), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component57Node61_sound : Sound component57Node61Box :=
  sound_of_literal_split component57Node61Box component57Node45Box component57Node60Box
    .k (59/16) (by rfl) (by rfl)
    component57Node45_sound component57Node60_sound

noncomputable def component57Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (5/32), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
theorem component57_sound : Sound component57Box :=
  sound_of_literal_split component57Box component57Node30Box component57Node61Box
    .chi (11/64) (by rfl) (by rfl)
    component57Node30_sound component57Node61_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
