import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch3
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

private noncomputable def leaf3093Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (233/64), chiLo := (3/16), chiHi := (49/256) }

private noncomputable def leaf3093Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742387/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433107968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1803472847/1073741824) }, upper := { exponent := 0, mantissa := (27801/16384) } }, logOuter := sk217LogOuterCertificate, logK := sk217LogKCertificate, logChi := chi187LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870029823/274866215936) } }, logDArg := sk217LogDArgCertificate }

private noncomputable def leaf3093InnerLog : WideLogData :=
  innerPair420Data

set_option maxRecDepth 1000000 in
private theorem leaf3093LocalValidity :
    LeafFacts leaf3093Box leaf3093Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3093Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433107968) }) = true
      norm_num [leaf3093Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3093CertificateValid :
    WideCertificateValid leaf3093Box leaf3093Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk217ValidityFacts chi187ValidityFacts
    leaf3093LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3093CoverageChecked :
    coverageCheck (innerAD leaf3093Box) leaf3093InnerLog = true := by
  rfl'

private theorem leaf3093InnerLogValid :
    leaf3093InnerLog.Valid 8 (innerAD leaf3093Box) :=
  wideLogDataValid_of_cachedCheck endpoint133PositiveFacts
    endpoint20PositiveFacts.valid leaf3093CoverageChecked

private noncomputable def leaf3093InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814657/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3093InputLogOnePlusV_eq :
    leaf3093InputLogOnePlusV = outerEnclosure 24
      (leaf3093Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3093RoundedFacts : LeafRoundedFacts 8
    leaf3093Certificate.logOnePlusV leaf3093InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3093InputLogOnePlusV_eq }

private noncomputable def leaf3093Inputs : Inputs :=
  inputsOfCaches globalInput sk217RoundedInputs
    chi187InputQChi innerPair420Input
    leaf3093InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3093LowerChecked :
    lowerCheck 24 leaf3093Box leaf3093Inputs = true := by
  rfl'

private theorem leaf3093CoversExact : CoversExact 8
    leaf3093Box leaf3093Certificate leaf3093InnerLog leaf3093Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk217RoundedFacts chi187RoundedFacts
    innerPair420RoundedFacts leaf3093RoundedFacts (by rfl)

private theorem leaf3093FlatSound : Sound leaf3093Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3093CertificateValid
    leaf3093InnerLogValid leaf3093CoversExact leaf3093LowerChecked

private noncomputable def leaf3094Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (233/64), kHi := (117/32), chiLo := (3/16), chiHi := (49/256) }

private noncomputable def leaf3094Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742389/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486616576) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1806618381/1073741824) }, upper := { exponent := 0, mantissa := (13925/8192) } }, logOuter := sk218LogOuterCertificate, logK := sk218LogKCertificate, logChi := chi187LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54974000947/54973233152) } }, logDArg := sk218LogDArgCertificate }

private noncomputable def leaf3094InnerLog : WideLogData :=
  innerPair420Data

set_option maxRecDepth 1000000 in
private theorem leaf3094LocalValidity :
    LeafFacts leaf3094Box leaf3094Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3094Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486616576) }) = true
      norm_num [leaf3094Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3094CertificateValid :
    WideCertificateValid leaf3094Box leaf3094Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk218ValidityFacts chi187ValidityFacts
    leaf3094LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3094CoverageChecked :
    coverageCheck (innerAD leaf3094Box) leaf3094InnerLog = true := by
  rfl'

private theorem leaf3094InnerLogValid :
    leaf3094InnerLog.Valid 8 (innerAD leaf3094Box) :=
  wideLogDataValid_of_cachedCheck endpoint133PositiveFacts
    endpoint20PositiveFacts.valid leaf3094CoverageChecked

private noncomputable def leaf3094InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629315/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3094InputLogOnePlusV_eq :
    leaf3094InputLogOnePlusV = outerEnclosure 24
      (leaf3094Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3094RoundedFacts : LeafRoundedFacts 8
    leaf3094Certificate.logOnePlusV leaf3094InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3094InputLogOnePlusV_eq }

private noncomputable def leaf3094Inputs : Inputs :=
  inputsOfCaches globalInput sk218RoundedInputs
    chi187InputQChi innerPair420Input
    leaf3094InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3094LowerChecked :
    lowerCheck 24 leaf3094Box leaf3094Inputs = true := by
  rfl'

private theorem leaf3094CoversExact : CoversExact 8
    leaf3094Box leaf3094Certificate leaf3094InnerLog leaf3094Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk218RoundedFacts chi187RoundedFacts
    innerPair420RoundedFacts leaf3094RoundedFacts (by rfl)

private theorem leaf3094FlatSound : Sound leaf3094Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3094CertificateValid
    leaf3094InnerLogValid leaf3094CoversExact leaf3094LowerChecked

private noncomputable def leaf3095Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (233/64), chiLo := (49/256), chiHi := (25/128) }

private noncomputable def leaf3095Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742389/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810996224) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1818676269/1073741824) }, upper := { exponent := 0, mantissa := (14017/8192) } }, logOuter := sk217LogOuterCertificate, logK := sk217LogKCertificate, logChi := chi188LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623303509/91621992448) } }, logDArg := sk217LogDArgCertificate }

private noncomputable def leaf3095InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3095LocalValidity :
    LeafFacts leaf3095Box leaf3095Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3095Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810996224) }) = true
      norm_num [leaf3095Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3095CertificateValid :
    WideCertificateValid leaf3095Box leaf3095Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk217ValidityFacts chi188ValidityFacts
    leaf3095LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3095CoverageChecked :
    coverageCheck (innerAD leaf3095Box) leaf3095InnerLog = true := by
  rfl'

private theorem leaf3095InnerLogValid :
    leaf3095InnerLog.Valid 8 (innerAD leaf3095Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3095CoverageChecked

private noncomputable def leaf3095InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629321/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3095InputLogOnePlusV_eq :
    leaf3095InputLogOnePlusV = outerEnclosure 24
      (leaf3095Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3095RoundedFacts : LeafRoundedFacts 8
    leaf3095Certificate.logOnePlusV leaf3095InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3095InputLogOnePlusV_eq }

private noncomputable def leaf3095Inputs : Inputs :=
  inputsOfCaches globalInput sk217RoundedInputs
    chi188InputQChi innerPair64Input
    leaf3095InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3095LowerChecked :
    lowerCheck 24 leaf3095Box leaf3095Inputs = true := by
  rfl'

private theorem leaf3095CoversExact : CoversExact 8
    leaf3095Box leaf3095Certificate leaf3095InnerLog leaf3095Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk217RoundedFacts chi188RoundedFacts
    innerPair64RoundedFacts leaf3095RoundedFacts (by rfl)

private theorem leaf3095FlatSound : Sound leaf3095Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3095CertificateValid
    leaf3095InnerLogValid leaf3095CoversExact leaf3095LowerChecked

private noncomputable def leaf3096Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (233/64), kHi := (117/32), chiLo := (49/256), chiHi := (25/128) }

private noncomputable def leaf3096Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742391/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432963072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1821887335/1073741824) }, upper := { exponent := 0, mantissa := (7021/4096) } }, logOuter := sk218LogOuterCertificate, logK := sk218LogKCertificate, logChi := chi188LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869884927/274865926144) } }, logDArg := sk218LogDArgCertificate }

private noncomputable def leaf3096InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3096LocalValidity :
    LeafFacts leaf3096Box leaf3096Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3096Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432963072) }) = true
      norm_num [leaf3096Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3096CertificateValid :
    WideCertificateValid leaf3096Box leaf3096Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk218ValidityFacts chi188ValidityFacts
    leaf3096LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3096CoverageChecked :
    coverageCheck (innerAD leaf3096Box) leaf3096InnerLog = true := by
  rfl'

private theorem leaf3096InnerLogValid :
    leaf3096InnerLog.Valid 8 (innerAD leaf3096Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3096CoverageChecked

private noncomputable def leaf3096InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814661/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3096InputLogOnePlusV_eq :
    leaf3096InputLogOnePlusV = outerEnclosure 24
      (leaf3096Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3096RoundedFacts : LeafRoundedFacts 8
    leaf3096Certificate.logOnePlusV leaf3096InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3096InputLogOnePlusV_eq }

private noncomputable def leaf3096Inputs : Inputs :=
  inputsOfCaches globalInput sk218RoundedInputs
    chi188InputQChi innerPair64Input
    leaf3096InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3096LowerChecked :
    lowerCheck 24 leaf3096Box leaf3096Inputs = true := by
  rfl'

private theorem leaf3096CoversExact : CoversExact 8
    leaf3096Box leaf3096Certificate leaf3096InnerLog leaf3096Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk218RoundedFacts chi188RoundedFacts
    innerPair64RoundedFacts leaf3096RoundedFacts (by rfl)

private theorem leaf3096FlatSound : Sound leaf3096Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3096CertificateValid
    leaf3096InnerLogValid leaf3096CoversExact leaf3096LowerChecked

private noncomputable def leaf3097Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (235/64), chiLo := (3/16), chiHi := (49/256) }

private noncomputable def leaf3097Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742391/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45811019264) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1809763915/1073741824) }, upper := { exponent := 0, mantissa := (27899/16384) } }, logOuter := sk219LogOuterCertificate, logK := sk219LogKCertificate, logChi := chi187LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623326549/91622038528) } }, logDArg := sk219LogDArgCertificate }

private noncomputable def leaf3097InnerLog : WideLogData :=
  innerPair420Data

set_option maxRecDepth 1000000 in
private theorem leaf3097LocalValidity :
    LeafFacts leaf3097Box leaf3097Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3097Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45811019264) }) = true
      norm_num [leaf3097Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3097CertificateValid :
    WideCertificateValid leaf3097Box leaf3097Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk219ValidityFacts chi187ValidityFacts
    leaf3097LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3097CoverageChecked :
    coverageCheck (innerAD leaf3097Box) leaf3097InnerLog = true := by
  rfl'

private theorem leaf3097InnerLogValid :
    leaf3097InnerLog.Valid 8 (innerAD leaf3097Box) :=
  wideLogDataValid_of_cachedCheck endpoint133PositiveFacts
    endpoint20PositiveFacts.valid leaf3097CoverageChecked

private noncomputable def leaf3097InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629317/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3097InputLogOnePlusV_eq :
    leaf3097InputLogOnePlusV = outerEnclosure 24
      (leaf3097Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3097RoundedFacts : LeafRoundedFacts 8
    leaf3097Certificate.logOnePlusV leaf3097InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3097InputLogOnePlusV_eq }

private noncomputable def leaf3097Inputs : Inputs :=
  inputsOfCaches globalInput sk219RoundedInputs
    chi187InputQChi innerPair420Input
    leaf3097InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3097LowerChecked :
    lowerCheck 24 leaf3097Box leaf3097Inputs = true := by
  rfl'

private theorem leaf3097CoversExact : CoversExact 8
    leaf3097Box leaf3097Certificate leaf3097InnerLog leaf3097Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk219RoundedFacts chi187RoundedFacts
    innerPair420RoundedFacts leaf3097RoundedFacts (by rfl)

private theorem leaf3097FlatSound : Sound leaf3097Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3097CertificateValid
    leaf3097InnerLogValid leaf3097CoversExact leaf3097LowerChecked

private noncomputable def leaf3098Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (235/64), kHi := (59/16), chiLo := (3/16), chiHi := (49/256) }

private noncomputable def leaf3098Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742393/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433032704) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1812909449/1073741824) }, upper := { exponent := 0, mantissa := (6987/4096) } }, logOuter := sk220LogOuterCertificate, logK := sk220LogKCertificate, logChi := chi187LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869954559/274866065408) } }, logDArg := sk220LogDArgCertificate }

private noncomputable def leaf3098InnerLog : WideLogData :=
  innerPair68Data

set_option maxRecDepth 1000000 in
private theorem leaf3098LocalValidity :
    LeafFacts leaf3098Box leaf3098Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3098Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433032704) }) = true
      norm_num [leaf3098Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3098CertificateValid :
    WideCertificateValid leaf3098Box leaf3098Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk220ValidityFacts chi187ValidityFacts
    leaf3098LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3098CoverageChecked :
    coverageCheck (innerAD leaf3098Box) leaf3098InnerLog = true := by
  rfl'

private theorem leaf3098InnerLogValid :
    leaf3098InnerLog.Valid 8 (innerAD leaf3098Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint62PositiveFacts.valid leaf3098CoverageChecked

private noncomputable def leaf3098InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814659/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3098InputLogOnePlusV_eq :
    leaf3098InputLogOnePlusV = outerEnclosure 24
      (leaf3098Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3098RoundedFacts : LeafRoundedFacts 8
    leaf3098Certificate.logOnePlusV leaf3098InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3098InputLogOnePlusV_eq }

private noncomputable def leaf3098Inputs : Inputs :=
  inputsOfCaches globalInput sk220RoundedInputs
    chi187InputQChi innerPair68Input
    leaf3098InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3098LowerChecked :
    lowerCheck 24 leaf3098Box leaf3098Inputs = true := by
  rfl'

private theorem leaf3098CoversExact : CoversExact 8
    leaf3098Box leaf3098Certificate leaf3098InnerLog leaf3098Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk220RoundedFacts chi187RoundedFacts
    innerPair68RoundedFacts leaf3098RoundedFacts (by rfl)

private theorem leaf3098FlatSound : Sound leaf3098Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3098CertificateValid
    leaf3098InnerLogValid leaf3098CoversExact leaf3098LowerChecked

private noncomputable def leaf3099Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (235/64), chiLo := (49/256), chiHi := (25/128) }

private noncomputable def leaf3099Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742393/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432937472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1825098401/1073741824) }, upper := { exponent := 0, mantissa := (14067/8192) } }, logOuter := sk219LogOuterCertificate, logK := sk219LogKCertificate, logChi := chi188LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869859327/274865874944) } }, logDArg := sk219LogDArgCertificate }

private noncomputable def leaf3099InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3099LocalValidity :
    LeafFacts leaf3099Box leaf3099Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3099Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432937472) }) = true
      norm_num [leaf3099Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3099CertificateValid :
    WideCertificateValid leaf3099Box leaf3099Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk219ValidityFacts chi188ValidityFacts
    leaf3099LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3099CoverageChecked :
    coverageCheck (innerAD leaf3099Box) leaf3099InnerLog = true := by
  rfl'

private theorem leaf3099InnerLogValid :
    leaf3099InnerLog.Valid 8 (innerAD leaf3099Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3099CoverageChecked

private noncomputable def leaf3099InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907331/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3099InputLogOnePlusV_eq :
    leaf3099InputLogOnePlusV = outerEnclosure 24
      (leaf3099Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3099RoundedFacts : LeafRoundedFacts 8
    leaf3099Certificate.logOnePlusV leaf3099InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3099InputLogOnePlusV_eq }

private noncomputable def leaf3099Inputs : Inputs :=
  inputsOfCaches globalInput sk219RoundedInputs
    chi188InputQChi innerPair64Input
    leaf3099InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3099LowerChecked :
    lowerCheck 24 leaf3099Box leaf3099Inputs = true := by
  rfl'

private theorem leaf3099CoversExact : CoversExact 8
    leaf3099Box leaf3099Certificate leaf3099InnerLog leaf3099Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk219RoundedFacts chi188RoundedFacts
    innerPair64RoundedFacts leaf3099RoundedFacts (by rfl)

private theorem leaf3099FlatSound : Sound leaf3099Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3099CertificateValid
    leaf3099InnerLogValid leaf3099CoversExact leaf3099LowerChecked

private noncomputable def leaf3100Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (235/64), kHi := (59/16), chiLo := (49/256), chiHi := (25/128) }

private noncomputable def leaf3100Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742395/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810970624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1828309467/1073741824) }, upper := { exponent := 0, mantissa := (3523/2048) } }, logOuter := sk220LogOuterCertificate, logK := sk220LogKCertificate, logChi := chi188LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623277909/91621941248) } }, logDArg := sk220LogDArgCertificate }

private noncomputable def leaf3100InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3100LocalValidity :
    LeafFacts leaf3100Box leaf3100Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3100Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810970624) }) = true
      norm_num [leaf3100Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3100CertificateValid :
    WideCertificateValid leaf3100Box leaf3100Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk220ValidityFacts chi188ValidityFacts
    leaf3100LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3100CoverageChecked :
    coverageCheck (innerAD leaf3100Box) leaf3100InnerLog = true := by
  rfl'

private theorem leaf3100InnerLogValid :
    leaf3100InnerLog.Valid 8 (innerAD leaf3100Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3100CoverageChecked

private noncomputable def leaf3100InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814663/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3100InputLogOnePlusV_eq :
    leaf3100InputLogOnePlusV = outerEnclosure 24
      (leaf3100Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3100RoundedFacts : LeafRoundedFacts 8
    leaf3100Certificate.logOnePlusV leaf3100InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3100InputLogOnePlusV_eq }

private noncomputable def leaf3100Inputs : Inputs :=
  inputsOfCaches globalInput sk220RoundedInputs
    chi188InputQChi innerPair64Input
    leaf3100InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3100LowerChecked :
    lowerCheck 24 leaf3100Box leaf3100Inputs = true := by
  rfl'

private theorem leaf3100CoversExact : CoversExact 8
    leaf3100Box leaf3100Certificate leaf3100InnerLog leaf3100Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk220RoundedFacts chi188RoundedFacts
    innerPair64RoundedFacts leaf3100RoundedFacts (by rfl)

private theorem leaf3100FlatSound : Sound leaf3100Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3100CertificateValid
    leaf3100InnerLogValid leaf3100CoversExact leaf3100LowerChecked

private noncomputable def leaf3101Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (233/64), chiLo := (25/128), chiHi := (51/256) }

private noncomputable def leaf3101Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742391/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432869376) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1833879691/1073741824) }, upper := { exponent := 0, mantissa := (28267/16384) } }, logOuter := sk217LogOuterCertificate, logK := sk217LogKCertificate, logChi := chi193LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869791231/274865738752) } }, logDArg := sk217LogDArgCertificate }

private noncomputable def leaf3101InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3101LocalValidity :
    LeafFacts leaf3101Box leaf3101Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3101Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432869376) }) = true
      norm_num [leaf3101Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3101CertificateValid :
    WideCertificateValid leaf3101Box leaf3101Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk217ValidityFacts chi193ValidityFacts
    leaf3101LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3101CoverageChecked :
    coverageCheck (innerAD leaf3101Box) leaf3101InnerLog = true := by
  rfl'

private theorem leaf3101InnerLogValid :
    leaf3101InnerLog.Valid 8 (innerAD leaf3101Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3101CoverageChecked

private noncomputable def leaf3101InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726833/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf3101InputLogOnePlusV_eq :
    leaf3101InputLogOnePlusV = outerEnclosure 24
      (leaf3101Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3101RoundedFacts : LeafRoundedFacts 8
    leaf3101Certificate.logOnePlusV leaf3101InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3101InputLogOnePlusV_eq }

private noncomputable def leaf3101Inputs : Inputs :=
  inputsOfCaches globalInput sk217RoundedInputs
    chi193InputQChi innerPair64Input
    leaf3101InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3101LowerChecked :
    lowerCheck 24 leaf3101Box leaf3101Inputs = true := by
  rfl'

private theorem leaf3101CoversExact : CoversExact 8
    leaf3101Box leaf3101Certificate leaf3101InnerLog leaf3101Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk217RoundedFacts chi193RoundedFacts
    innerPair64RoundedFacts leaf3101RoundedFacts (by rfl)

private theorem leaf3101FlatSound : Sound leaf3101Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3101CertificateValid
    leaf3101InnerLogValid leaf3101CoversExact leaf3101LowerChecked

private noncomputable def leaf3102Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (233/64), kHi := (117/32), chiLo := (25/128), chiHi := (51/256) }

private noncomputable def leaf3102Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742393/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432843264) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1837156289/1073741824) }, upper := { exponent := 0, mantissa := (14159/8192) } }, logOuter := sk218LogOuterCertificate, logK := sk218LogKCertificate, logChi := chi193LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869765119/274865686528) } }, logDArg := sk218LogDArgCertificate }

private noncomputable def leaf3102InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3102LocalValidity :
    LeafFacts leaf3102Box leaf3102Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3102Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432843264) }) = true
      norm_num [leaf3102Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3102CertificateValid :
    WideCertificateValid leaf3102Box leaf3102Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk218ValidityFacts chi193ValidityFacts
    leaf3102LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3102CoverageChecked :
    coverageCheck (innerAD leaf3102Box) leaf3102InnerLog = true := by
  rfl'

private theorem leaf3102InnerLogValid :
    leaf3102InnerLog.Valid 8 (innerAD leaf3102Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3102CoverageChecked

private noncomputable def leaf3102InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814665/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3102InputLogOnePlusV_eq :
    leaf3102InputLogOnePlusV = outerEnclosure 24
      (leaf3102Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3102RoundedFacts : LeafRoundedFacts 8
    leaf3102Certificate.logOnePlusV leaf3102InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3102InputLogOnePlusV_eq }

private noncomputable def leaf3102Inputs : Inputs :=
  inputsOfCaches globalInput sk218RoundedInputs
    chi193InputQChi innerPair64Input
    leaf3102InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3102LowerChecked :
    lowerCheck 24 leaf3102Box leaf3102Inputs = true := by
  rfl'

private theorem leaf3102CoversExact : CoversExact 8
    leaf3102Box leaf3102Certificate leaf3102InnerLog leaf3102Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk218RoundedFacts chi193RoundedFacts
    innerPair64RoundedFacts leaf3102RoundedFacts (by rfl)

private theorem leaf3102FlatSound : Sound leaf3102Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3102CertificateValid
    leaf3102InnerLogValid leaf3102CoversExact leaf3102LowerChecked

private noncomputable def leaf3103Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (233/64), chiLo := (51/256), chiHi := (13/64) }

private noncomputable def leaf3103Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742393/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486550016) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1849083113/1073741824) }, upper := { exponent := 0, mantissa := (7125/4096) } }, logOuter := sk217LogOuterCertificate, logK := sk217LogKCertificate, logChi := chi194LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973934387/54973100032) } }, logDArg := sk217LogDArgCertificate }

private noncomputable def leaf3103InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3103LocalValidity :
    LeafFacts leaf3103Box leaf3103Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3103Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486550016) }) = true
      norm_num [leaf3103Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3103CertificateValid :
    WideCertificateValid leaf3103Box leaf3103Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk217ValidityFacts chi194ValidityFacts
    leaf3103LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3103CoverageChecked :
    coverageCheck (innerAD leaf3103Box) leaf3103InnerLog = true := by
  rfl'

private theorem leaf3103InnerLogValid :
    leaf3103InnerLog.Valid 8 (innerAD leaf3103Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3103CoverageChecked

private noncomputable def leaf3103InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629335/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3103InputLogOnePlusV_eq :
    leaf3103InputLogOnePlusV = outerEnclosure 24
      (leaf3103Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3103RoundedFacts : LeafRoundedFacts 8
    leaf3103Certificate.logOnePlusV leaf3103InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3103InputLogOnePlusV_eq }

private noncomputable def leaf3103Inputs : Inputs :=
  inputsOfCaches globalInput sk217RoundedInputs
    chi194InputQChi innerPair64Input
    leaf3103InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3103LowerChecked :
    lowerCheck 24 leaf3103Box leaf3103Inputs = true := by
  rfl'

private theorem leaf3103CoversExact : CoversExact 8
    leaf3103Box leaf3103Certificate leaf3103InnerLog leaf3103Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk217RoundedFacts chi194RoundedFacts
    innerPair64RoundedFacts leaf3103RoundedFacts (by rfl)

private theorem leaf3103FlatSound : Sound leaf3103Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3103CertificateValid
    leaf3103InnerLogValid leaf3103CoversExact leaf3103LowerChecked

private noncomputable def leaf3104Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (233/64), kHi := (117/32), chiLo := (51/256), chiHi := (13/64) }

private noncomputable def leaf3104Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742395/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432723456) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1852425243/1073741824) }, upper := { exponent := 0, mantissa := (3569/2048) } }, logOuter := sk218LogOuterCertificate, logK := sk218LogKCertificate, logChi := chi194LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869645311/274865446912) } }, logDArg := sk218LogDArgCertificate }

private noncomputable def leaf3104InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3104LocalValidity :
    LeafFacts leaf3104Box leaf3104Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3104Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432723456) }) = true
      norm_num [leaf3104Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3104CertificateValid :
    WideCertificateValid leaf3104Box leaf3104Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk218ValidityFacts chi194ValidityFacts
    leaf3104LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3104CoverageChecked :
    coverageCheck (innerAD leaf3104Box) leaf3104InnerLog = true := by
  rfl'

private theorem leaf3104InnerLogValid :
    leaf3104InnerLog.Valid 8 (innerAD leaf3104Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3104CoverageChecked

private noncomputable def leaf3104InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629337/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3104InputLogOnePlusV_eq :
    leaf3104InputLogOnePlusV = outerEnclosure 24
      (leaf3104Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3104RoundedFacts : LeafRoundedFacts 8
    leaf3104Certificate.logOnePlusV leaf3104InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3104InputLogOnePlusV_eq }

private noncomputable def leaf3104Inputs : Inputs :=
  inputsOfCaches globalInput sk218RoundedInputs
    chi194InputQChi innerPair64Input
    leaf3104InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3104LowerChecked :
    lowerCheck 24 leaf3104Box leaf3104Inputs = true := by
  rfl'

private theorem leaf3104CoversExact : CoversExact 8
    leaf3104Box leaf3104Certificate leaf3104InnerLog leaf3104Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk218RoundedFacts chi194RoundedFacts
    innerPair64RoundedFacts leaf3104RoundedFacts (by rfl)

private theorem leaf3104FlatSound : Sound leaf3104Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3104CertificateValid
    leaf3104InnerLogValid leaf3104CoversExact leaf3104LowerChecked

private noncomputable def leaf3105Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (235/64), chiLo := (25/128), chiHi := (51/256) }

private noncomputable def leaf3105Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742395/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432817152) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1840432887/1073741824) }, upper := { exponent := 0, mantissa := (28369/16384) } }, logOuter := sk219LogOuterCertificate, logK := sk219LogKCertificate, logChi := chi193LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869739007/274865634304) } }, logDArg := sk219LogDArgCertificate }

private noncomputable def leaf3105InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3105LocalValidity :
    LeafFacts leaf3105Box leaf3105Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3105Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432817152) }) = true
      norm_num [leaf3105Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3105CertificateValid :
    WideCertificateValid leaf3105Box leaf3105Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk219ValidityFacts chi193ValidityFacts
    leaf3105LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3105CoverageChecked :
    coverageCheck (innerAD leaf3105Box) leaf3105InnerLog = true := by
  rfl'

private theorem leaf3105InnerLogValid :
    leaf3105InnerLog.Valid 8 (innerAD leaf3105Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3105CoverageChecked

private noncomputable def leaf3105InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629331/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3105InputLogOnePlusV_eq :
    leaf3105InputLogOnePlusV = outerEnclosure 24
      (leaf3105Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3105RoundedFacts : LeafRoundedFacts 8
    leaf3105Certificate.logOnePlusV leaf3105InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3105InputLogOnePlusV_eq }

private noncomputable def leaf3105Inputs : Inputs :=
  inputsOfCaches globalInput sk219RoundedInputs
    chi193InputQChi innerPair64Input
    leaf3105InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3105LowerChecked :
    lowerCheck 24 leaf3105Box leaf3105Inputs = true := by
  rfl'

private theorem leaf3105CoversExact : CoversExact 8
    leaf3105Box leaf3105Certificate leaf3105InnerLog leaf3105Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk219RoundedFacts chi193RoundedFacts
    innerPair64RoundedFacts leaf3105RoundedFacts (by rfl)

private theorem leaf3105FlatSound : Sound leaf3105Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3105CertificateValid
    leaf3105InnerLogValid leaf3105CoversExact leaf3105LowerChecked

private noncomputable def leaf3106Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (235/64), kHi := (59/16), chiLo := (25/128), chiHi := (51/256) }

private noncomputable def leaf3106Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742397/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486558208) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1843709485/1073741824) }, upper := { exponent := 0, mantissa := (7105/4096) } }, logOuter := sk220LogOuterCertificate, logK := sk220LogKCertificate, logChi := chi193LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973942579/54973116416) } }, logDArg := sk220LogDArgCertificate }

private noncomputable def leaf3106InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3106LocalValidity :
    LeafFacts leaf3106Box leaf3106Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3106Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486558208) }) = true
      norm_num [leaf3106Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3106CertificateValid :
    WideCertificateValid leaf3106Box leaf3106Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk220ValidityFacts chi193ValidityFacts
    leaf3106LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3106CoverageChecked :
    coverageCheck (innerAD leaf3106Box) leaf3106InnerLog = true := by
  rfl'

private theorem leaf3106InnerLogValid :
    leaf3106InnerLog.Valid 8 (innerAD leaf3106Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3106CoverageChecked

private noncomputable def leaf3106InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629333/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3106InputLogOnePlusV_eq :
    leaf3106InputLogOnePlusV = outerEnclosure 24
      (leaf3106Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3106RoundedFacts : LeafRoundedFacts 8
    leaf3106Certificate.logOnePlusV leaf3106InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3106InputLogOnePlusV_eq }

private noncomputable def leaf3106Inputs : Inputs :=
  inputsOfCaches globalInput sk220RoundedInputs
    chi193InputQChi innerPair64Input
    leaf3106InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3106LowerChecked :
    lowerCheck 24 leaf3106Box leaf3106Inputs = true := by
  rfl'

private theorem leaf3106CoversExact : CoversExact 8
    leaf3106Box leaf3106Certificate leaf3106InnerLog leaf3106Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk220RoundedFacts chi193RoundedFacts
    innerPair64RoundedFacts leaf3106RoundedFacts (by rfl)

private theorem leaf3106FlatSound : Sound leaf3106Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3106CertificateValid
    leaf3106InnerLogValid leaf3106CoversExact leaf3106LowerChecked

private noncomputable def leaf3107Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (235/64), chiLo := (51/256), chiHi := (13/64) }

private noncomputable def leaf3107Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742397/1073741824) }, vSqrt := { lower := (8191/8192), upper := (15270769095/15270299648) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1855767373/1073741824) }, upper := { exponent := 0, mantissa := (7151/4096) } }, logOuter := sk219LogOuterCertificate, logK := sk219LogKCertificate, logChi := chi194LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (30541068743/30540599296) } }, logDArg := sk219LogDArgCertificate }

private noncomputable def leaf3107InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3107LocalValidity :
    LeafFacts leaf3107Box leaf3107Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3107Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (15270769095/15270299648) }) = true
      norm_num [leaf3107Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3107CertificateValid :
    WideCertificateValid leaf3107Box leaf3107Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk219ValidityFacts chi194ValidityFacts
    leaf3107LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3107CoverageChecked :
    coverageCheck (innerAD leaf3107Box) leaf3107InnerLog = true := by
  rfl'

private theorem leaf3107InnerLogValid :
    leaf3107InnerLog.Valid 8 (innerAD leaf3107Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3107CoverageChecked

private noncomputable def leaf3107InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629339/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3107InputLogOnePlusV_eq :
    leaf3107InputLogOnePlusV = outerEnclosure 24
      (leaf3107Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3107RoundedFacts : LeafRoundedFacts 8
    leaf3107Certificate.logOnePlusV leaf3107InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3107InputLogOnePlusV_eq }

private noncomputable def leaf3107Inputs : Inputs :=
  inputsOfCaches globalInput sk219RoundedInputs
    chi194InputQChi innerPair64Input
    leaf3107InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3107LowerChecked :
    lowerCheck 24 leaf3107Box leaf3107Inputs = true := by
  rfl'

private theorem leaf3107CoversExact : CoversExact 8
    leaf3107Box leaf3107Certificate leaf3107InnerLog leaf3107Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk219RoundedFacts chi194RoundedFacts
    innerPair64RoundedFacts leaf3107RoundedFacts (by rfl)

private theorem leaf3107FlatSound : Sound leaf3107Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3107CertificateValid
    leaf3107InnerLogValid leaf3107CoversExact leaf3107LowerChecked

private noncomputable def leaf3108Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (235/64), kHi := (59/16), chiLo := (51/256), chiHi := (13/64) }

private noncomputable def leaf3108Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742399/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432670208) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1859109503/1073741824) }, upper := { exponent := 0, mantissa := (1791/1024) } }, logOuter := sk220LogOuterCertificate, logK := sk220LogKCertificate, logChi := chi194LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869592063/274865340416) } }, logDArg := sk220LogDArgCertificate }

private noncomputable def leaf3108InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3108LocalValidity :
    LeafFacts leaf3108Box leaf3108Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3108Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432670208) }) = true
      norm_num [leaf3108Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3108CertificateValid :
    WideCertificateValid leaf3108Box leaf3108Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk220ValidityFacts chi194ValidityFacts
    leaf3108LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3108CoverageChecked :
    coverageCheck (innerAD leaf3108Box) leaf3108InnerLog = true := by
  rfl'

private theorem leaf3108InnerLogValid :
    leaf3108InnerLog.Valid 8 (innerAD leaf3108Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3108CoverageChecked

private noncomputable def leaf3108InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907335/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3108InputLogOnePlusV_eq :
    leaf3108InputLogOnePlusV = outerEnclosure 24
      (leaf3108Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3108RoundedFacts : LeafRoundedFacts 8
    leaf3108Certificate.logOnePlusV leaf3108InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3108InputLogOnePlusV_eq }

private noncomputable def leaf3108Inputs : Inputs :=
  inputsOfCaches globalInput sk220RoundedInputs
    chi194InputQChi innerPair64Input
    leaf3108InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3108LowerChecked :
    lowerCheck 24 leaf3108Box leaf3108Inputs = true := by
  rfl'

private theorem leaf3108CoversExact : CoversExact 8
    leaf3108Box leaf3108Certificate leaf3108InnerLog leaf3108Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk220RoundedFacts chi194RoundedFacts
    innerPair64RoundedFacts leaf3108RoundedFacts (by rfl)

private theorem leaf3108FlatSound : Sound leaf3108Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3108CertificateValid
    leaf3108InnerLogValid leaf3108CoversExact leaf3108LowerChecked

private noncomputable def leaf3109Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (237/64), chiLo := (3/16), chiHi := (49/256) }

private noncomputable def leaf3109Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742395/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433007616) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1816054983/1073741824) }, upper := { exponent := 0, mantissa := (27997/16384) } }, logOuter := sk221LogOuterCertificate, logK := sk221LogKCertificate, logChi := chi187LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869929471/274866015232) } }, logDArg := sk221LogDArgCertificate }

private noncomputable def leaf3109InnerLog : WideLogData :=
  innerPair68Data

set_option maxRecDepth 1000000 in
private theorem leaf3109LocalValidity :
    LeafFacts leaf3109Box leaf3109Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3109Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433007616) }) = true
      norm_num [leaf3109Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3109CertificateValid :
    WideCertificateValid leaf3109Box leaf3109Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk221ValidityFacts chi187ValidityFacts
    leaf3109LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3109CoverageChecked :
    coverageCheck (innerAD leaf3109Box) leaf3109InnerLog = true := by
  rfl'

private theorem leaf3109InnerLogValid :
    leaf3109InnerLog.Valid 8 (innerAD leaf3109Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint62PositiveFacts.valid leaf3109CoverageChecked

private noncomputable def leaf3109InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453665/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3109InputLogOnePlusV_eq :
    leaf3109InputLogOnePlusV = outerEnclosure 24
      (leaf3109Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3109RoundedFacts : LeafRoundedFacts 8
    leaf3109Certificate.logOnePlusV leaf3109InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3109InputLogOnePlusV_eq }

private noncomputable def leaf3109Inputs : Inputs :=
  inputsOfCaches globalInput sk221RoundedInputs
    chi187InputQChi innerPair68Input
    leaf3109InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3109LowerChecked :
    lowerCheck 24 leaf3109Box leaf3109Inputs = true := by
  rfl'

private theorem leaf3109CoversExact : CoversExact 8
    leaf3109Box leaf3109Certificate leaf3109InnerLog leaf3109Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk221RoundedFacts chi187RoundedFacts
    innerPair68RoundedFacts leaf3109RoundedFacts (by rfl)

private theorem leaf3109FlatSound : Sound leaf3109Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3109CertificateValid
    leaf3109InnerLogValid leaf3109CoversExact leaf3109LowerChecked

private noncomputable def leaf3110Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (237/64), kHi := (119/32), chiLo := (3/16), chiHi := (49/256) }

private noncomputable def leaf3110Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742397/1073741824) }, vSqrt := { lower := (8191/8192), upper := (5090256365/5090110464) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1819200517/1073741824) }, upper := { exponent := 0, mantissa := (14023/8192) } }, logOuter := sk222LogOuterCertificate, logK := sk222LogKCertificate, logChi := chi187LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (10180366829/10180220928) } }, logDArg := sk222LogDArgCertificate }

private noncomputable def leaf3110InnerLog : WideLogData :=
  innerPair68Data

set_option maxRecDepth 1000000 in
private theorem leaf3110LocalValidity :
    LeafFacts leaf3110Box leaf3110Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3110Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5090256365/5090110464) }) = true
      norm_num [leaf3110Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3110CertificateValid :
    WideCertificateValid leaf3110Box leaf3110Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk222ValidityFacts chi187ValidityFacts
    leaf3110LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3110CoverageChecked :
    coverageCheck (innerAD leaf3110Box) leaf3110InnerLog = true := by
  rfl'

private theorem leaf3110InnerLogValid :
    leaf3110InnerLog.Valid 8 (innerAD leaf3110Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint62PositiveFacts.valid leaf3110CoverageChecked

private noncomputable def leaf3110InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629321/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3110InputLogOnePlusV_eq :
    leaf3110InputLogOnePlusV = outerEnclosure 24
      (leaf3110Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3110RoundedFacts : LeafRoundedFacts 8
    leaf3110Certificate.logOnePlusV leaf3110InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3110InputLogOnePlusV_eq }

private noncomputable def leaf3110Inputs : Inputs :=
  inputsOfCaches globalInput sk222RoundedInputs
    chi187InputQChi innerPair68Input
    leaf3110InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3110LowerChecked :
    lowerCheck 24 leaf3110Box leaf3110Inputs = true := by
  rfl'

private theorem leaf3110CoversExact : CoversExact 8
    leaf3110Box leaf3110Certificate leaf3110InnerLog leaf3110Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk222RoundedFacts chi187RoundedFacts
    innerPair68RoundedFacts leaf3110RoundedFacts (by rfl)

private theorem leaf3110FlatSound : Sound leaf3110Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3110CertificateValid
    leaf3110InnerLogValid leaf3110CoversExact leaf3110LowerChecked

private noncomputable def leaf3111Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (237/64), chiLo := (49/256), chiHi := (25/128) }

private noncomputable def leaf3111Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742397/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432886272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1831520533/1073741824) }, upper := { exponent := 0, mantissa := (14117/8192) } }, logOuter := sk221LogOuterCertificate, logK := sk221LogKCertificate, logChi := chi188LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869808127/274865772544) } }, logDArg := sk221LogDArgCertificate }

private noncomputable def leaf3111InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3111LocalValidity :
    LeafFacts leaf3111Box leaf3111Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3111Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432886272) }) = true
      norm_num [leaf3111Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3111CertificateValid :
    WideCertificateValid leaf3111Box leaf3111Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk221ValidityFacts chi188ValidityFacts
    leaf3111LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3111CoverageChecked :
    coverageCheck (innerAD leaf3111Box) leaf3111InnerLog = true := by
  rfl'

private theorem leaf3111InnerLogValid :
    leaf3111InnerLog.Valid 8 (innerAD leaf3111Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3111CoverageChecked

private noncomputable def leaf3111InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629327/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3111InputLogOnePlusV_eq :
    leaf3111InputLogOnePlusV = outerEnclosure 24
      (leaf3111Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3111RoundedFacts : LeafRoundedFacts 8
    leaf3111Certificate.logOnePlusV leaf3111InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3111InputLogOnePlusV_eq }

private noncomputable def leaf3111Inputs : Inputs :=
  inputsOfCaches globalInput sk221RoundedInputs
    chi188InputQChi innerPair64Input
    leaf3111InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3111LowerChecked :
    lowerCheck 24 leaf3111Box leaf3111Inputs = true := by
  rfl'

private theorem leaf3111CoversExact : CoversExact 8
    leaf3111Box leaf3111Certificate leaf3111InnerLog leaf3111Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk221RoundedFacts chi188RoundedFacts
    innerPair64RoundedFacts leaf3111RoundedFacts (by rfl)

private theorem leaf3111FlatSound : Sound leaf3111Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3111CertificateValid
    leaf3111InnerLogValid leaf3111CoversExact leaf3111LowerChecked

private noncomputable def leaf3112Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (237/64), kHi := (119/32), chiLo := (49/256), chiHi := (25/128) }

private noncomputable def leaf3112Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742399/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432860672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1834731599/1073741824) }, upper := { exponent := 0, mantissa := (7071/4096) } }, logOuter := sk222LogOuterCertificate, logK := sk222LogKCertificate, logChi := chi188LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869782527/274865721344) } }, logDArg := sk222LogDArgCertificate }

private noncomputable def leaf3112InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3112LocalValidity :
    LeafFacts leaf3112Box leaf3112Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3112Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432860672) }) = true
      norm_num [leaf3112Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3112CertificateValid :
    WideCertificateValid leaf3112Box leaf3112Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk222ValidityFacts chi188ValidityFacts
    leaf3112LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3112CoverageChecked :
    coverageCheck (innerAD leaf3112Box) leaf3112InnerLog = true := by
  rfl'

private theorem leaf3112InnerLogValid :
    leaf3112InnerLog.Valid 8 (innerAD leaf3112Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3112CoverageChecked

private noncomputable def leaf3112InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629329/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3112InputLogOnePlusV_eq :
    leaf3112InputLogOnePlusV = outerEnclosure 24
      (leaf3112Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3112RoundedFacts : LeafRoundedFacts 8
    leaf3112Certificate.logOnePlusV leaf3112InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3112InputLogOnePlusV_eq }

private noncomputable def leaf3112Inputs : Inputs :=
  inputsOfCaches globalInput sk222RoundedInputs
    chi188InputQChi innerPair64Input
    leaf3112InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3112LowerChecked :
    lowerCheck 24 leaf3112Box leaf3112Inputs = true := by
  rfl'

private theorem leaf3112CoversExact : CoversExact 8
    leaf3112Box leaf3112Certificate leaf3112InnerLog leaf3112Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk222RoundedFacts chi188RoundedFacts
    innerPair64RoundedFacts leaf3112RoundedFacts (by rfl)

private theorem leaf3112FlatSound : Sound leaf3112Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3112CertificateValid
    leaf3112InnerLogValid leaf3112CoversExact leaf3112LowerChecked

private noncomputable def leaf3113Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (239/64), chiLo := (3/16), chiHi := (49/256) }

private noncomputable def leaf3113Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742399/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486591488) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1822346051/1073741824) }, upper := { exponent := 0, mantissa := (28095/16384) } }, logOuter := sk223LogOuterCertificate, logK := sk223LogKCertificate, logChi := chi187LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973975859/54973182976) } }, logDArg := sk223LogDArgCertificate }

private noncomputable def leaf3113InnerLog : WideLogData :=
  innerPair68Data

set_option maxRecDepth 1000000 in
private theorem leaf3113LocalValidity :
    LeafFacts leaf3113Box leaf3113Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3113Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486591488) }) = true
      norm_num [leaf3113Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3113CertificateValid :
    WideCertificateValid leaf3113Box leaf3113Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk223ValidityFacts chi187ValidityFacts
    leaf3113LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3113CoverageChecked :
    coverageCheck (innerAD leaf3113Box) leaf3113InnerLog = true := by
  rfl'

private theorem leaf3113InnerLogValid :
    leaf3113InnerLog.Valid 8 (innerAD leaf3113Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint62PositiveFacts.valid leaf3113CoverageChecked

private noncomputable def leaf3113InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629323/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3113InputLogOnePlusV_eq :
    leaf3113InputLogOnePlusV = outerEnclosure 24
      (leaf3113Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3113RoundedFacts : LeafRoundedFacts 8
    leaf3113Certificate.logOnePlusV leaf3113InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3113InputLogOnePlusV_eq }

private noncomputable def leaf3113Inputs : Inputs :=
  inputsOfCaches globalInput sk223RoundedInputs
    chi187InputQChi innerPair68Input
    leaf3113InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3113LowerChecked :
    lowerCheck 24 leaf3113Box leaf3113Inputs = true := by
  rfl'

private theorem leaf3113CoversExact : CoversExact 8
    leaf3113Box leaf3113Certificate leaf3113InnerLog leaf3113Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk223RoundedFacts chi187RoundedFacts
    innerPair68RoundedFacts leaf3113RoundedFacts (by rfl)

private theorem leaf3113FlatSound : Sound leaf3113Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3113CertificateValid
    leaf3113InnerLogValid leaf3113CoversExact leaf3113LowerChecked

private noncomputable def leaf3114Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (239/64), kHi := (15/4), chiLo := (3/16), chiHi := (49/256) }

private noncomputable def leaf3114Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742401/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432932352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1825491585/1073741824) }, upper := { exponent := 0, mantissa := (1759/1024) } }, logOuter := sk224LogOuterCertificate, logK := sk224LogKCertificate, logChi := chi187LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869854207/274865864704) } }, logDArg := sk224LogDArgCertificate }

private noncomputable def leaf3114InnerLog : WideLogData :=
  innerPair68Data

set_option maxRecDepth 1000000 in
private theorem leaf3114LocalValidity :
    LeafFacts leaf3114Box leaf3114Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3114Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432932352) }) = true
      norm_num [leaf3114Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3114CertificateValid :
    WideCertificateValid leaf3114Box leaf3114Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk224ValidityFacts chi187ValidityFacts
    leaf3114LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3114CoverageChecked :
    coverageCheck (innerAD leaf3114Box) leaf3114InnerLog = true := by
  rfl'

private theorem leaf3114InnerLogValid :
    leaf3114InnerLog.Valid 8 (innerAD leaf3114Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint62PositiveFacts.valid leaf3114CoverageChecked

private noncomputable def leaf3114InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907331/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3114InputLogOnePlusV_eq :
    leaf3114InputLogOnePlusV = outerEnclosure 24
      (leaf3114Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3114RoundedFacts : LeafRoundedFacts 8
    leaf3114Certificate.logOnePlusV leaf3114InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3114InputLogOnePlusV_eq }

private noncomputable def leaf3114Inputs : Inputs :=
  inputsOfCaches globalInput sk224RoundedInputs
    chi187InputQChi innerPair68Input
    leaf3114InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3114LowerChecked :
    lowerCheck 24 leaf3114Box leaf3114Inputs = true := by
  rfl'

private theorem leaf3114CoversExact : CoversExact 8
    leaf3114Box leaf3114Certificate leaf3114InnerLog leaf3114Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk224RoundedFacts chi187RoundedFacts
    innerPair68RoundedFacts leaf3114RoundedFacts (by rfl)

private theorem leaf3114FlatSound : Sound leaf3114Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3114CertificateValid
    leaf3114InnerLogValid leaf3114CoversExact leaf3114LowerChecked

private noncomputable def leaf3115Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (239/64), chiLo := (49/256), chiHi := (25/128) }

private noncomputable def leaf3115Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742401/1073741824) }, vSqrt := { lower := (8191/8192), upper := (898280535/898253824) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1837942665/1073741824) }, upper := { exponent := 0, mantissa := (14167/8192) } }, logOuter := sk223LogOuterCertificate, logK := sk223LogKCertificate, logChi := chi188LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (1796534359/1796507648) } }, logDArg := sk223LogDArgCertificate }

private noncomputable def leaf3115InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3115LocalValidity :
    LeafFacts leaf3115Box leaf3115Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3115Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (898280535/898253824) }) = true
      norm_num [leaf3115Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3115CertificateValid :
    WideCertificateValid leaf3115Box leaf3115Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk223ValidityFacts chi188ValidityFacts
    leaf3115LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3115CoverageChecked :
    coverageCheck (innerAD leaf3115Box) leaf3115InnerLog = true := by
  rfl'

private theorem leaf3115InnerLogValid :
    leaf3115InnerLog.Valid 8 (innerAD leaf3115Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3115CoverageChecked

private noncomputable def leaf3115InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814665/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3115InputLogOnePlusV_eq :
    leaf3115InputLogOnePlusV = outerEnclosure 24
      (leaf3115Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3115RoundedFacts : LeafRoundedFacts 8
    leaf3115Certificate.logOnePlusV leaf3115InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3115InputLogOnePlusV_eq }

private noncomputable def leaf3115Inputs : Inputs :=
  inputsOfCaches globalInput sk223RoundedInputs
    chi188InputQChi innerPair64Input
    leaf3115InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3115LowerChecked :
    lowerCheck 24 leaf3115Box leaf3115Inputs = true := by
  rfl'

private theorem leaf3115CoversExact : CoversExact 8
    leaf3115Box leaf3115Certificate leaf3115InnerLog leaf3115Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk223RoundedFacts chi188RoundedFacts
    innerPair64RoundedFacts leaf3115RoundedFacts (by rfl)

private theorem leaf3115FlatSound : Sound leaf3115Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3115CertificateValid
    leaf3115InnerLogValid leaf3115CoversExact leaf3115LowerChecked

private noncomputable def leaf3116Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (239/64), kHi := (15/4), chiLo := (49/256), chiHi := (25/128) }

private noncomputable def leaf3116Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742403/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432809472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1841153731/1073741824) }, upper := { exponent := 0, mantissa := (887/512) } }, logOuter := sk224LogOuterCertificate, logK := sk224LogKCertificate, logChi := chi188LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869731327/274865618944) } }, logDArg := sk224LogDArgCertificate }

private noncomputable def leaf3116InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3116LocalValidity :
    LeafFacts leaf3116Box leaf3116Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3116Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432809472) }) = true
      norm_num [leaf3116Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3116CertificateValid :
    WideCertificateValid leaf3116Box leaf3116Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk224ValidityFacts chi188ValidityFacts
    leaf3116LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3116CoverageChecked :
    coverageCheck (innerAD leaf3116Box) leaf3116InnerLog = true := by
  rfl'

private theorem leaf3116InnerLogValid :
    leaf3116InnerLog.Valid 8 (innerAD leaf3116Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3116CoverageChecked

private noncomputable def leaf3116InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907333/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3116InputLogOnePlusV_eq :
    leaf3116InputLogOnePlusV = outerEnclosure 24
      (leaf3116Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3116RoundedFacts : LeafRoundedFacts 8
    leaf3116Certificate.logOnePlusV leaf3116InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3116InputLogOnePlusV_eq }

private noncomputable def leaf3116Inputs : Inputs :=
  inputsOfCaches globalInput sk224RoundedInputs
    chi188InputQChi innerPair64Input
    leaf3116InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3116LowerChecked :
    lowerCheck 24 leaf3116Box leaf3116Inputs = true := by
  rfl'

private theorem leaf3116CoversExact : CoversExact 8
    leaf3116Box leaf3116Certificate leaf3116InnerLog leaf3116Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk224RoundedFacts chi188RoundedFacts
    innerPair64RoundedFacts leaf3116RoundedFacts (by rfl)

private theorem leaf3116FlatSound : Sound leaf3116Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3116CertificateValid
    leaf3116InnerLogValid leaf3116CoversExact leaf3116LowerChecked

private noncomputable def leaf3117Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (237/64), chiLo := (25/128), chiHi := (51/256) }

private noncomputable def leaf3117Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742399/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432764928) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1846986083/1073741824) }, upper := { exponent := 0, mantissa := (28471/16384) } }, logOuter := sk221LogOuterCertificate, logK := sk221LogKCertificate, logChi := chi193LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869686783/274865529856) } }, logDArg := sk221LogDArgCertificate }

private noncomputable def leaf3117InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3117LocalValidity :
    LeafFacts leaf3117Box leaf3117Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3117Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432764928) }) = true
      norm_num [leaf3117Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3117CertificateValid :
    WideCertificateValid leaf3117Box leaf3117Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk221ValidityFacts chi193ValidityFacts
    leaf3117LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3117CoverageChecked :
    coverageCheck (innerAD leaf3117Box) leaf3117InnerLog = true := by
  rfl'

private theorem leaf3117InnerLogValid :
    leaf3117InnerLog.Valid 8 (innerAD leaf3117Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3117CoverageChecked

private noncomputable def leaf3117InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814667/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3117InputLogOnePlusV_eq :
    leaf3117InputLogOnePlusV = outerEnclosure 24
      (leaf3117Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3117RoundedFacts : LeafRoundedFacts 8
    leaf3117Certificate.logOnePlusV leaf3117InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3117InputLogOnePlusV_eq }

private noncomputable def leaf3117Inputs : Inputs :=
  inputsOfCaches globalInput sk221RoundedInputs
    chi193InputQChi innerPair64Input
    leaf3117InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3117LowerChecked :
    lowerCheck 24 leaf3117Box leaf3117Inputs = true := by
  rfl'

private theorem leaf3117CoversExact : CoversExact 8
    leaf3117Box leaf3117Certificate leaf3117InnerLog leaf3117Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk221RoundedFacts chi193RoundedFacts
    innerPair64RoundedFacts leaf3117RoundedFacts (by rfl)

private theorem leaf3117FlatSound : Sound leaf3117Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3117CertificateValid
    leaf3117InnerLogValid leaf3117CoversExact leaf3117LowerChecked

private noncomputable def leaf3118Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (237/64), kHi := (119/32), chiLo := (25/128), chiHi := (51/256) }

private noncomputable def leaf3118Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742401/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432738816) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1850262681/1073741824) }, upper := { exponent := 0, mantissa := (14261/8192) } }, logOuter := sk222LogOuterCertificate, logK := sk222LogKCertificate, logChi := chi193LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869660671/274865477632) } }, logDArg := sk222LogDArgCertificate }

private noncomputable def leaf3118InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3118LocalValidity :
    LeafFacts leaf3118Box leaf3118Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3118Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432738816) }) = true
      norm_num [leaf3118Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3118CertificateValid :
    WideCertificateValid leaf3118Box leaf3118Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk222ValidityFacts chi193ValidityFacts
    leaf3118LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3118CoverageChecked :
    coverageCheck (innerAD leaf3118Box) leaf3118InnerLog = true := by
  rfl'

private theorem leaf3118InnerLogValid :
    leaf3118InnerLog.Valid 8 (innerAD leaf3118Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3118CoverageChecked

private noncomputable def leaf3118InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453667/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3118InputLogOnePlusV_eq :
    leaf3118InputLogOnePlusV = outerEnclosure 24
      (leaf3118Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3118RoundedFacts : LeafRoundedFacts 8
    leaf3118Certificate.logOnePlusV leaf3118InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3118InputLogOnePlusV_eq }

private noncomputable def leaf3118Inputs : Inputs :=
  inputsOfCaches globalInput sk222RoundedInputs
    chi193InputQChi innerPair64Input
    leaf3118InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3118LowerChecked :
    lowerCheck 24 leaf3118Box leaf3118Inputs = true := by
  rfl'

private theorem leaf3118CoversExact : CoversExact 8
    leaf3118Box leaf3118Certificate leaf3118InnerLog leaf3118Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk222RoundedFacts chi193RoundedFacts
    innerPair64RoundedFacts leaf3118RoundedFacts (by rfl)

private theorem leaf3118FlatSound : Sound leaf3118Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3118CertificateValid
    leaf3118InnerLogValid leaf3118CoversExact leaf3118LowerChecked

private noncomputable def leaf3119Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (237/64), chiLo := (51/256), chiHi := (13/64) }

private noncomputable def leaf3119Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742401/1073741824) }, vSqrt := { lower := (8191/8192), upper := (8084524815/8084273152) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1862451633/1073741824) }, upper := { exponent := 0, mantissa := (7177/4096) } }, logOuter := sk221LogOuterCertificate, logK := sk221LogKCertificate, logChi := chi194LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16168797967/16168546304) } }, logDArg := sk221LogDArgCertificate }

private noncomputable def leaf3119InnerLog : WideLogData :=
  innerPair430Data

set_option maxRecDepth 1000000 in
private theorem leaf3119LocalValidity :
    LeafFacts leaf3119Box leaf3119Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3119Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8084524815/8084273152) }) = true
      norm_num [leaf3119Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3119CertificateValid :
    WideCertificateValid leaf3119Box leaf3119Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk221ValidityFacts chi194ValidityFacts
    leaf3119LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3119CoverageChecked :
    coverageCheck (innerAD leaf3119Box) leaf3119InnerLog = true := by
  rfl'

private theorem leaf3119InnerLogValid :
    leaf3119InnerLog.Valid 8 (innerAD leaf3119Box) :=
  wideLogDataValid_of_cachedCheck endpoint139PositiveFacts
    endpoint63PositiveFacts.valid leaf3119CoverageChecked

private noncomputable def leaf3119InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814671/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3119InputLogOnePlusV_eq :
    leaf3119InputLogOnePlusV = outerEnclosure 24
      (leaf3119Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3119RoundedFacts : LeafRoundedFacts 8
    leaf3119Certificate.logOnePlusV leaf3119InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3119InputLogOnePlusV_eq }

private noncomputable def leaf3119Inputs : Inputs :=
  inputsOfCaches globalInput sk221RoundedInputs
    chi194InputQChi innerPair430Input
    leaf3119InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3119LowerChecked :
    lowerCheck 24 leaf3119Box leaf3119Inputs = true := by
  rfl'

private theorem leaf3119CoversExact : CoversExact 8
    leaf3119Box leaf3119Certificate leaf3119InnerLog leaf3119Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk221RoundedFacts chi194RoundedFacts
    innerPair430RoundedFacts leaf3119RoundedFacts (by rfl)

private theorem leaf3119FlatSound : Sound leaf3119Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3119CertificateValid
    leaf3119InnerLogValid leaf3119CoversExact leaf3119LowerChecked

private noncomputable def leaf3120Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (237/64), kHi := (119/32), chiLo := (51/256), chiHi := (13/64) }

private noncomputable def leaf3120Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742403/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9162461457/9162174464) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1865793763/1073741824) }, upper := { exponent := 0, mantissa := (3595/2048) } }, logOuter := sk222LogOuterCertificate, logK := sk222LogKCertificate, logChi := chi194LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (18324635921/18324348928) } }, logDArg := sk222LogDArgCertificate }

private noncomputable def leaf3120InnerLog : WideLogData :=
  innerPair430Data

set_option maxRecDepth 1000000 in
private theorem leaf3120LocalValidity :
    LeafFacts leaf3120Box leaf3120Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3120Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9162461457/9162174464) }) = true
      norm_num [leaf3120Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3120CertificateValid :
    WideCertificateValid leaf3120Box leaf3120Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk222ValidityFacts chi194ValidityFacts
    leaf3120LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3120CoverageChecked :
    coverageCheck (innerAD leaf3120Box) leaf3120InnerLog = true := by
  rfl'

private theorem leaf3120InnerLogValid :
    leaf3120InnerLog.Valid 8 (innerAD leaf3120Box) :=
  wideLogDataValid_of_cachedCheck endpoint139PositiveFacts
    endpoint63PositiveFacts.valid leaf3120CoverageChecked

private noncomputable def leaf3120InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (363417/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf3120InputLogOnePlusV_eq :
    leaf3120InputLogOnePlusV = outerEnclosure 24
      (leaf3120Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3120RoundedFacts : LeafRoundedFacts 8
    leaf3120Certificate.logOnePlusV leaf3120InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3120InputLogOnePlusV_eq }

private noncomputable def leaf3120Inputs : Inputs :=
  inputsOfCaches globalInput sk222RoundedInputs
    chi194InputQChi innerPair430Input
    leaf3120InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3120LowerChecked :
    lowerCheck 24 leaf3120Box leaf3120Inputs = true := by
  rfl'

private theorem leaf3120CoversExact : CoversExact 8
    leaf3120Box leaf3120Certificate leaf3120InnerLog leaf3120Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk222RoundedFacts chi194RoundedFacts
    innerPair430RoundedFacts leaf3120RoundedFacts (by rfl)

private theorem leaf3120FlatSound : Sound leaf3120Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3120CertificateValid
    leaf3120InnerLogValid leaf3120CoversExact leaf3120LowerChecked

private noncomputable def leaf3121Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (239/64), chiLo := (25/128), chiHi := (51/256) }

private noncomputable def leaf3121Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742403/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432712704) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1853539279/1073741824) }, upper := { exponent := 0, mantissa := (28573/16384) } }, logOuter := sk223LogOuterCertificate, logK := sk223LogKCertificate, logChi := chi193LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869634559/274865425408) } }, logDArg := sk223LogDArgCertificate }

private noncomputable def leaf3121InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3121LocalValidity :
    LeafFacts leaf3121Box leaf3121Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3121Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432712704) }) = true
      norm_num [leaf3121Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3121CertificateValid :
    WideCertificateValid leaf3121Box leaf3121Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk223ValidityFacts chi193ValidityFacts
    leaf3121LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3121CoverageChecked :
    coverageCheck (innerAD leaf3121Box) leaf3121InnerLog = true := by
  rfl'

private theorem leaf3121InnerLogValid :
    leaf3121InnerLog.Valid 8 (innerAD leaf3121Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3121CoverageChecked

private noncomputable def leaf3121InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814669/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3121InputLogOnePlusV_eq :
    leaf3121InputLogOnePlusV = outerEnclosure 24
      (leaf3121Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3121RoundedFacts : LeafRoundedFacts 8
    leaf3121Certificate.logOnePlusV leaf3121InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3121InputLogOnePlusV_eq }

private noncomputable def leaf3121Inputs : Inputs :=
  inputsOfCaches globalInput sk223RoundedInputs
    chi193InputQChi innerPair64Input
    leaf3121InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3121LowerChecked :
    lowerCheck 24 leaf3121Box leaf3121Inputs = true := by
  rfl'

private theorem leaf3121CoversExact : CoversExact 8
    leaf3121Box leaf3121Certificate leaf3121InnerLog leaf3121Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk223RoundedFacts chi193RoundedFacts
    innerPair64RoundedFacts leaf3121RoundedFacts (by rfl)

private theorem leaf3121FlatSound : Sound leaf3121Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3121CertificateValid
    leaf3121InnerLogValid leaf3121CoversExact leaf3121LowerChecked

private noncomputable def leaf3122Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (239/64), kHi := (15/4), chiLo := (25/128), chiHi := (51/256) }

private noncomputable def leaf3122Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742405/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432686592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1856815877/1073741824) }, upper := { exponent := 0, mantissa := (1789/1024) } }, logOuter := sk224LogOuterCertificate, logK := sk224LogKCertificate, logChi := chi193LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869608447/274865373184) } }, logDArg := sk224LogDArgCertificate }

private noncomputable def leaf3122InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3122LocalValidity :
    LeafFacts leaf3122Box leaf3122Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3122Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432686592) }) = true
      norm_num [leaf3122Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3122CertificateValid :
    WideCertificateValid leaf3122Box leaf3122Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk224ValidityFacts chi193ValidityFacts
    leaf3122LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3122CoverageChecked :
    coverageCheck (innerAD leaf3122Box) leaf3122InnerLog = true := by
  rfl'

private theorem leaf3122InnerLogValid :
    leaf3122InnerLog.Valid 8 (innerAD leaf3122Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3122CoverageChecked

private noncomputable def leaf3122InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629339/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3122InputLogOnePlusV_eq :
    leaf3122InputLogOnePlusV = outerEnclosure 24
      (leaf3122Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3122RoundedFacts : LeafRoundedFacts 8
    leaf3122Certificate.logOnePlusV leaf3122InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3122InputLogOnePlusV_eq }

private noncomputable def leaf3122Inputs : Inputs :=
  inputsOfCaches globalInput sk224RoundedInputs
    chi193InputQChi innerPair64Input
    leaf3122InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3122LowerChecked :
    lowerCheck 24 leaf3122Box leaf3122Inputs = true := by
  rfl'

private theorem leaf3122CoversExact : CoversExact 8
    leaf3122Box leaf3122Certificate leaf3122InnerLog leaf3122Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk224RoundedFacts chi193RoundedFacts
    innerPair64RoundedFacts leaf3122RoundedFacts (by rfl)

private theorem leaf3122FlatSound : Sound leaf3122Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3122CertificateValid
    leaf3122InnerLogValid leaf3122CoversExact leaf3122LowerChecked

private noncomputable def leaf3123Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (239/64), chiLo := (51/256), chiHi := (13/64) }

private noncomputable def leaf3123Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742405/1073741824) }, vSqrt := { lower := (8191/8192), upper := (3196207485/3196106752) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1869135893/1073741824) }, upper := { exponent := 0, mantissa := (7203/4096) } }, logOuter := sk223LogOuterCertificate, logK := sk223LogKCertificate, logChi := chi194LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (6392314237/6392213504) } }, logDArg := sk223LogDArgCertificate }

private noncomputable def leaf3123InnerLog : WideLogData :=
  innerPair430Data

set_option maxRecDepth 1000000 in
private theorem leaf3123LocalValidity :
    LeafFacts leaf3123Box leaf3123Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3123Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (3196207485/3196106752) }) = true
      norm_num [leaf3123Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3123CertificateValid :
    WideCertificateValid leaf3123Box leaf3123Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk223ValidityFacts chi194ValidityFacts
    leaf3123LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3123CoverageChecked :
    coverageCheck (innerAD leaf3123Box) leaf3123InnerLog = true := by
  rfl'

private theorem leaf3123InnerLogValid :
    leaf3123InnerLog.Valid 8 (innerAD leaf3123Box) :=
  wideLogDataValid_of_cachedCheck endpoint139PositiveFacts
    endpoint63PositiveFacts.valid leaf3123CoverageChecked

private noncomputable def leaf3123InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629345/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3123InputLogOnePlusV_eq :
    leaf3123InputLogOnePlusV = outerEnclosure 24
      (leaf3123Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3123RoundedFacts : LeafRoundedFacts 8
    leaf3123Certificate.logOnePlusV leaf3123InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3123InputLogOnePlusV_eq }

private noncomputable def leaf3123Inputs : Inputs :=
  inputsOfCaches globalInput sk223RoundedInputs
    chi194InputQChi innerPair430Input
    leaf3123InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3123LowerChecked :
    lowerCheck 24 leaf3123Box leaf3123Inputs = true := by
  rfl'

private theorem leaf3123CoversExact : CoversExact 8
    leaf3123Box leaf3123Certificate leaf3123InnerLog leaf3123Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk223RoundedFacts chi194RoundedFacts
    innerPair430RoundedFacts leaf3123RoundedFacts (by rfl)

private theorem leaf3123FlatSound : Sound leaf3123Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3123CertificateValid
    leaf3123InnerLogValid leaf3123CoversExact leaf3123LowerChecked

private noncomputable def leaf3124Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (239/64), kHi := (15/4), chiLo := (51/256), chiHi := (13/64) }

private noncomputable def leaf3124Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742407/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432563712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1872478023/1073741824) }, upper := { exponent := 0, mantissa := (451/256) } }, logOuter := sk224LogOuterCertificate, logK := sk224LogKCertificate, logChi := chi194LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869485567/274865127424) } }, logDArg := sk224LogDArgCertificate }

private noncomputable def leaf3124InnerLog : WideLogData :=
  innerPair430Data

set_option maxRecDepth 1000000 in
private theorem leaf3124LocalValidity :
    LeafFacts leaf3124Box leaf3124Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3124Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432563712) }) = true
      norm_num [leaf3124Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3124CertificateValid :
    WideCertificateValid leaf3124Box leaf3124Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk224ValidityFacts chi194ValidityFacts
    leaf3124LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3124CoverageChecked :
    coverageCheck (innerAD leaf3124Box) leaf3124InnerLog = true := by
  rfl'

private theorem leaf3124InnerLogValid :
    leaf3124InnerLog.Valid 8 (innerAD leaf3124Box) :=
  wideLogDataValid_of_cachedCheck endpoint139PositiveFacts
    endpoint63PositiveFacts.valid leaf3124CoverageChecked

private noncomputable def leaf3124InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629347/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3124InputLogOnePlusV_eq :
    leaf3124InputLogOnePlusV = outerEnclosure 24
      (leaf3124Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3124RoundedFacts : LeafRoundedFacts 8
    leaf3124Certificate.logOnePlusV leaf3124InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3124InputLogOnePlusV_eq }

private noncomputable def leaf3124Inputs : Inputs :=
  inputsOfCaches globalInput sk224RoundedInputs
    chi194InputQChi innerPair430Input
    leaf3124InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3124LowerChecked :
    lowerCheck 24 leaf3124Box leaf3124Inputs = true := by
  rfl'

private theorem leaf3124CoversExact : CoversExact 8
    leaf3124Box leaf3124Certificate leaf3124InnerLog leaf3124Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk224RoundedFacts chi194RoundedFacts
    innerPair430RoundedFacts leaf3124RoundedFacts (by rfl)

private theorem leaf3124FlatSound : Sound leaf3124Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3124CertificateValid
    leaf3124InnerLogValid leaf3124CoversExact leaf3124LowerChecked

private noncomputable def leaf3125Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (233/64), chiLo := (13/64), chiHi := (53/256) }

private noncomputable def leaf3125Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742395/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810876928) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1864286535/1073741824) }, upper := { exponent := 0, mantissa := (28733/16384) } }, logOuter := sk217LogOuterCertificate, logK := sk217LogKCertificate, logChi := chi195LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623184213/91621753856) } }, logDArg := sk217LogDArgCertificate }

private noncomputable def leaf3125InnerLog : WideLogData :=
  innerPair430Data

set_option maxRecDepth 1000000 in
private theorem leaf3125LocalValidity :
    LeafFacts leaf3125Box leaf3125Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3125Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810876928) }) = true
      norm_num [leaf3125Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3125CertificateValid :
    WideCertificateValid leaf3125Box leaf3125Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk217ValidityFacts chi195ValidityFacts
    leaf3125LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3125CoverageChecked :
    coverageCheck (innerAD leaf3125Box) leaf3125InnerLog = true := by
  rfl'

private theorem leaf3125InnerLogValid :
    leaf3125InnerLog.Valid 8 (innerAD leaf3125Box) :=
  wideLogDataValid_of_cachedCheck endpoint139PositiveFacts
    endpoint63PositiveFacts.valid leaf3125CoverageChecked

private noncomputable def leaf3125InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629343/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3125InputLogOnePlusV_eq :
    leaf3125InputLogOnePlusV = outerEnclosure 24
      (leaf3125Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3125RoundedFacts : LeafRoundedFacts 8
    leaf3125Certificate.logOnePlusV leaf3125InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3125InputLogOnePlusV_eq }

private noncomputable def leaf3125Inputs : Inputs :=
  inputsOfCaches globalInput sk217RoundedInputs
    chi195InputQChi innerPair430Input
    leaf3125InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3125LowerChecked :
    lowerCheck 24 leaf3125Box leaf3125Inputs = true := by
  rfl'

private theorem leaf3125CoversExact : CoversExact 8
    leaf3125Box leaf3125Certificate leaf3125InnerLog leaf3125Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk217RoundedFacts chi195RoundedFacts
    innerPair430RoundedFacts leaf3125RoundedFacts (by rfl)

private theorem leaf3125FlatSound : Sound leaf3125Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3125CertificateValid
    leaf3125InnerLogValid leaf3125CoversExact leaf3125LowerChecked

private noncomputable def leaf3126Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (233/64), kHi := (117/32), chiLo := (13/64), chiHi := (53/256) }

private noncomputable def leaf3126Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742397/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432603648) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1867694197/1073741824) }, upper := { exponent := 0, mantissa := (14393/8192) } }, logOuter := sk218LogOuterCertificate, logK := sk218LogKCertificate, logChi := chi195LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869525503/274865207296) } }, logDArg := sk218LogDArgCertificate }

private noncomputable def leaf3126InnerLog : WideLogData :=
  innerPair430Data

set_option maxRecDepth 1000000 in
private theorem leaf3126LocalValidity :
    LeafFacts leaf3126Box leaf3126Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3126Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432603648) }) = true
      norm_num [leaf3126Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3126CertificateValid :
    WideCertificateValid leaf3126Box leaf3126Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk218ValidityFacts chi195ValidityFacts
    leaf3126LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3126CoverageChecked :
    coverageCheck (innerAD leaf3126Box) leaf3126InnerLog = true := by
  rfl'

private theorem leaf3126InnerLogValid :
    leaf3126InnerLog.Valid 8 (innerAD leaf3126Box) :=
  wideLogDataValid_of_cachedCheck endpoint139PositiveFacts
    endpoint63PositiveFacts.valid leaf3126CoverageChecked

private noncomputable def leaf3126InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (363417/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf3126InputLogOnePlusV_eq :
    leaf3126InputLogOnePlusV = outerEnclosure 24
      (leaf3126Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3126RoundedFacts : LeafRoundedFacts 8
    leaf3126Certificate.logOnePlusV leaf3126InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3126InputLogOnePlusV_eq }

private noncomputable def leaf3126Inputs : Inputs :=
  inputsOfCaches globalInput sk218RoundedInputs
    chi195InputQChi innerPair430Input
    leaf3126InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3126LowerChecked :
    lowerCheck 24 leaf3126Box leaf3126Inputs = true := by
  rfl'

private theorem leaf3126CoversExact : CoversExact 8
    leaf3126Box leaf3126Certificate leaf3126InnerLog leaf3126Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk218RoundedFacts chi195RoundedFacts
    innerPair430RoundedFacts leaf3126RoundedFacts (by rfl)

private theorem leaf3126FlatSound : Sound leaf3126Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3126CertificateValid
    leaf3126InnerLogValid leaf3126CoversExact leaf3126LowerChecked

private noncomputable def leaf3127Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (233/64), chiLo := (53/256), chiHi := (27/128) }

private noncomputable def leaf3127Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742397/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432511488) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1879489957/1073741824) }, upper := { exponent := 0, mantissa := (14483/8192) } }, logOuter := sk217LogOuterCertificate, logK := sk217LogKCertificate, logChi := chi196LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869433343/274865022976) } }, logDArg := sk217LogDArgCertificate }

private noncomputable def leaf3127InnerLog : WideLogData :=
  innerPair78Data

set_option maxRecDepth 1000000 in
private theorem leaf3127LocalValidity :
    LeafFacts leaf3127Box leaf3127Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3127Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432511488) }) = true
      norm_num [leaf3127Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3127CertificateValid :
    WideCertificateValid leaf3127Box leaf3127Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk217ValidityFacts chi196ValidityFacts
    leaf3127LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3127CoverageChecked :
    coverageCheck (innerAD leaf3127Box) leaf3127InnerLog = true := by
  rfl'

private theorem leaf3127InnerLogValid :
    leaf3127InnerLog.Valid 8 (innerAD leaf3127Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint68PositiveFacts.valid leaf3127CoverageChecked

private noncomputable def leaf3127InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814675/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3127InputLogOnePlusV_eq :
    leaf3127InputLogOnePlusV = outerEnclosure 24
      (leaf3127Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3127RoundedFacts : LeafRoundedFacts 8
    leaf3127Certificate.logOnePlusV leaf3127InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3127InputLogOnePlusV_eq }

private noncomputable def leaf3127Inputs : Inputs :=
  inputsOfCaches globalInput sk217RoundedInputs
    chi196InputQChi innerPair78Input
    leaf3127InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3127LowerChecked :
    lowerCheck 24 leaf3127Box leaf3127Inputs = true := by
  rfl'

private theorem leaf3127CoversExact : CoversExact 8
    leaf3127Box leaf3127Certificate leaf3127InnerLog leaf3127Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk217RoundedFacts chi196RoundedFacts
    innerPair78RoundedFacts leaf3127RoundedFacts (by rfl)

private theorem leaf3127FlatSound : Sound leaf3127Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3127CertificateValid
    leaf3127InnerLogValid leaf3127CoversExact leaf3127LowerChecked

private noncomputable def leaf3128Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (233/64), kHi := (117/32), chiLo := (53/256), chiHi := (27/128) }

private noncomputable def leaf3128Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742399/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486496768) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1882963151/1073741824) }, upper := { exponent := 0, mantissa := (7255/4096) } }, logOuter := sk218LogOuterCertificate, logK := sk218LogKCertificate, logChi := chi196LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973881139/54972993536) } }, logDArg := sk218LogDArgCertificate }

private noncomputable def leaf3128InnerLog : WideLogData :=
  innerPair78Data

set_option maxRecDepth 1000000 in
private theorem leaf3128LocalValidity :
    LeafFacts leaf3128Box leaf3128Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3128Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486496768) }) = true
      norm_num [leaf3128Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3128CertificateValid :
    WideCertificateValid leaf3128Box leaf3128Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk218ValidityFacts chi196ValidityFacts
    leaf3128LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3128CoverageChecked :
    coverageCheck (innerAD leaf3128Box) leaf3128InnerLog = true := by
  rfl'

private theorem leaf3128InnerLogValid :
    leaf3128InnerLog.Valid 8 (innerAD leaf3128Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint68PositiveFacts.valid leaf3128CoverageChecked

private noncomputable def leaf3128InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453669/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3128InputLogOnePlusV_eq :
    leaf3128InputLogOnePlusV = outerEnclosure 24
      (leaf3128Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3128RoundedFacts : LeafRoundedFacts 8
    leaf3128Certificate.logOnePlusV leaf3128InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3128InputLogOnePlusV_eq }

private noncomputable def leaf3128Inputs : Inputs :=
  inputsOfCaches globalInput sk218RoundedInputs
    chi196InputQChi innerPair78Input
    leaf3128InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3128LowerChecked :
    lowerCheck 24 leaf3128Box leaf3128Inputs = true := by
  rfl'

private theorem leaf3128CoversExact : CoversExact 8
    leaf3128Box leaf3128Certificate leaf3128InnerLog leaf3128Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk218RoundedFacts chi196RoundedFacts
    innerPair78RoundedFacts leaf3128RoundedFacts (by rfl)

private theorem leaf3128FlatSound : Sound leaf3128Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3128CertificateValid
    leaf3128InnerLogValid leaf3128CoversExact leaf3128LowerChecked

private noncomputable def leaf3129Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (235/64), chiLo := (13/64), chiHi := (53/256) }

private noncomputable def leaf3129Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742399/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432576512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1871101859/1073741824) }, upper := { exponent := 0, mantissa := (28839/16384) } }, logOuter := sk219LogOuterCertificate, logK := sk219LogKCertificate, logChi := chi195LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869498367/274865153024) } }, logDArg := sk219LogDArgCertificate }

private noncomputable def leaf3129InnerLog : WideLogData :=
  innerPair430Data

set_option maxRecDepth 1000000 in
private theorem leaf3129LocalValidity :
    LeafFacts leaf3129Box leaf3129Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3129Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432576512) }) = true
      norm_num [leaf3129Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3129CertificateValid :
    WideCertificateValid leaf3129Box leaf3129Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk219ValidityFacts chi195ValidityFacts
    leaf3129LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3129CoverageChecked :
    coverageCheck (innerAD leaf3129Box) leaf3129InnerLog = true := by
  rfl'

private theorem leaf3129InnerLogValid :
    leaf3129InnerLog.Valid 8 (innerAD leaf3129Box) :=
  wideLogDataValid_of_cachedCheck endpoint139PositiveFacts
    endpoint63PositiveFacts.valid leaf3129CoverageChecked

private noncomputable def leaf3129InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814673/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3129InputLogOnePlusV_eq :
    leaf3129InputLogOnePlusV = outerEnclosure 24
      (leaf3129Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3129RoundedFacts : LeafRoundedFacts 8
    leaf3129Certificate.logOnePlusV leaf3129InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3129InputLogOnePlusV_eq }

private noncomputable def leaf3129Inputs : Inputs :=
  inputsOfCaches globalInput sk219RoundedInputs
    chi195InputQChi innerPair430Input
    leaf3129InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3129LowerChecked :
    lowerCheck 24 leaf3129Box leaf3129Inputs = true := by
  rfl'

private theorem leaf3129CoversExact : CoversExact 8
    leaf3129Box leaf3129Certificate leaf3129InnerLog leaf3129Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk219RoundedFacts chi195RoundedFacts
    innerPair430RoundedFacts leaf3129RoundedFacts (by rfl)

private theorem leaf3129FlatSound : Sound leaf3129Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3129CertificateValid
    leaf3129InnerLogValid leaf3129CoversExact leaf3129LowerChecked

private noncomputable def leaf3130Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (235/64), kHi := (59/16), chiLo := (13/64), chiHi := (53/256) }

private noncomputable def leaf3130Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742401/1073741824) }, vSqrt := { lower := (8191/8192), upper := (15270769095/15270283264) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1874509521/1073741824) }, upper := { exponent := 0, mantissa := (7223/4096) } }, logOuter := sk220LogOuterCertificate, logK := sk220LogKCertificate, logChi := chi195LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (30541052359/30540566528) } }, logDArg := sk220LogDArgCertificate }

private noncomputable def leaf3130InnerLog : WideLogData :=
  innerPair430Data

set_option maxRecDepth 1000000 in
private theorem leaf3130LocalValidity :
    LeafFacts leaf3130Box leaf3130Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3130Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (15270769095/15270283264) }) = true
      norm_num [leaf3130Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3130CertificateValid :
    WideCertificateValid leaf3130Box leaf3130Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk220ValidityFacts chi195ValidityFacts
    leaf3130LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3130CoverageChecked :
    coverageCheck (innerAD leaf3130Box) leaf3130InnerLog = true := by
  rfl'

private theorem leaf3130InnerLogValid :
    leaf3130InnerLog.Valid 8 (innerAD leaf3130Box) :=
  wideLogDataValid_of_cachedCheck endpoint139PositiveFacts
    endpoint63PositiveFacts.valid leaf3130CoverageChecked

private noncomputable def leaf3130InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907337/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3130InputLogOnePlusV_eq :
    leaf3130InputLogOnePlusV = outerEnclosure 24
      (leaf3130Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3130RoundedFacts : LeafRoundedFacts 8
    leaf3130Certificate.logOnePlusV leaf3130InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3130InputLogOnePlusV_eq }

private noncomputable def leaf3130Inputs : Inputs :=
  inputsOfCaches globalInput sk220RoundedInputs
    chi195InputQChi innerPair430Input
    leaf3130InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3130LowerChecked :
    lowerCheck 24 leaf3130Box leaf3130Inputs = true := by
  rfl'

private theorem leaf3130CoversExact : CoversExact 8
    leaf3130Box leaf3130Certificate leaf3130InnerLog leaf3130Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk220RoundedFacts chi195RoundedFacts
    innerPair430RoundedFacts leaf3130RoundedFacts (by rfl)

private theorem leaf3130FlatSound : Sound leaf3130Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3130CertificateValid
    leaf3130InnerLogValid leaf3130CoversExact leaf3130LowerChecked

private noncomputable def leaf3131Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (235/64), chiLo := (53/256), chiHi := (27/128) }

private noncomputable def leaf3131Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742401/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432456192) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1886436345/1073741824) }, upper := { exponent := 0, mantissa := (14537/8192) } }, logOuter := sk219LogOuterCertificate, logK := sk219LogKCertificate, logChi := chi196LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869378047/274864912384) } }, logDArg := sk219LogDArgCertificate }

private noncomputable def leaf3131InnerLog : WideLogData :=
  innerPair78Data

set_option maxRecDepth 1000000 in
private theorem leaf3131LocalValidity :
    LeafFacts leaf3131Box leaf3131Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3131Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432456192) }) = true
      norm_num [leaf3131Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3131CertificateValid :
    WideCertificateValid leaf3131Box leaf3131Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk219ValidityFacts chi196ValidityFacts
    leaf3131LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3131CoverageChecked :
    coverageCheck (innerAD leaf3131Box) leaf3131InnerLog = true := by
  rfl'

private theorem leaf3131InnerLogValid :
    leaf3131InnerLog.Valid 8 (innerAD leaf3131Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint68PositiveFacts.valid leaf3131CoverageChecked

private noncomputable def leaf3131InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629353/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3131InputLogOnePlusV_eq :
    leaf3131InputLogOnePlusV = outerEnclosure 24
      (leaf3131Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3131RoundedFacts : LeafRoundedFacts 8
    leaf3131Certificate.logOnePlusV leaf3131InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3131InputLogOnePlusV_eq }

private noncomputable def leaf3131Inputs : Inputs :=
  inputsOfCaches globalInput sk219RoundedInputs
    chi196InputQChi innerPair78Input
    leaf3131InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3131LowerChecked :
    lowerCheck 24 leaf3131Box leaf3131Inputs = true := by
  rfl'

private theorem leaf3131CoversExact : CoversExact 8
    leaf3131Box leaf3131Certificate leaf3131InnerLog leaf3131Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk219RoundedFacts chi196RoundedFacts
    innerPair78RoundedFacts leaf3131RoundedFacts (by rfl)

private theorem leaf3131FlatSound : Sound leaf3131Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3131CertificateValid
    leaf3131InnerLogValid leaf3131CoversExact leaf3131LowerChecked

private noncomputable def leaf3132Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (235/64), kHi := (59/16), chiLo := (53/256), chiHi := (27/128) }

private noncomputable def leaf3132Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742403/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432428544) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1889909539/1073741824) }, upper := { exponent := 0, mantissa := (3641/2048) } }, logOuter := sk220LogOuterCertificate, logK := sk220LogKCertificate, logChi := chi196LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869350399/274864857088) } }, logDArg := sk220LogDArgCertificate }

private noncomputable def leaf3132InnerLog : WideLogData :=
  innerPair78Data

set_option maxRecDepth 1000000 in
private theorem leaf3132LocalValidity :
    LeafFacts leaf3132Box leaf3132Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3132Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432428544) }) = true
      norm_num [leaf3132Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3132CertificateValid :
    WideCertificateValid leaf3132Box leaf3132Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk220ValidityFacts chi196ValidityFacts
    leaf3132LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3132CoverageChecked :
    coverageCheck (innerAD leaf3132Box) leaf3132InnerLog = true := by
  rfl'

private theorem leaf3132InnerLogValid :
    leaf3132InnerLog.Valid 8 (innerAD leaf3132Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint68PositiveFacts.valid leaf3132CoverageChecked

private noncomputable def leaf3132InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629355/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3132InputLogOnePlusV_eq :
    leaf3132InputLogOnePlusV = outerEnclosure 24
      (leaf3132Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3132RoundedFacts : LeafRoundedFacts 8
    leaf3132Certificate.logOnePlusV leaf3132InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3132InputLogOnePlusV_eq }

private noncomputable def leaf3132Inputs : Inputs :=
  inputsOfCaches globalInput sk220RoundedInputs
    chi196InputQChi innerPair78Input
    leaf3132InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3132LowerChecked :
    lowerCheck 24 leaf3132Box leaf3132Inputs = true := by
  rfl'

private theorem leaf3132CoversExact : CoversExact 8
    leaf3132Box leaf3132Certificate leaf3132InnerLog leaf3132Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk220RoundedFacts chi196RoundedFacts
    innerPair78RoundedFacts leaf3132RoundedFacts (by rfl)

private theorem leaf3132FlatSound : Sound leaf3132Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3132CertificateValid
    leaf3132InnerLogValid leaf3132CoversExact leaf3132LowerChecked

private noncomputable def leaf3133Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (233/64), chiLo := (27/128), chiHi := (55/256) }

private noncomputable def leaf3133Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742399/1073741824) }, vSqrt := { lower := (8191/8192), upper := (3196207485/3196102144) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1894693379/1073741824) }, upper := { exponent := 0, mantissa := (29199/16384) } }, logOuter := sk217LogOuterCertificate, logK := sk217LogKCertificate, logChi := chi197LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (6392309629/6392204288) } }, logDArg := sk217LogDArgCertificate }

private noncomputable def leaf3133InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3133LocalValidity :
    LeafFacts leaf3133Box leaf3133Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3133Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (3196207485/3196102144) }) = true
      norm_num [leaf3133Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3133CertificateValid :
    WideCertificateValid leaf3133Box leaf3133Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk217ValidityFacts chi197ValidityFacts
    leaf3133LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3133CoverageChecked :
    coverageCheck (innerAD leaf3133Box) leaf3133InnerLog = true := by
  rfl'

private theorem leaf3133InnerLogValid :
    leaf3133InnerLog.Valid 8 (innerAD leaf3133Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3133CoverageChecked

private noncomputable def leaf3133InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629357/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3133InputLogOnePlusV_eq :
    leaf3133InputLogOnePlusV = outerEnclosure 24
      (leaf3133Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3133RoundedFacts : LeafRoundedFacts 8
    leaf3133Certificate.logOnePlusV leaf3133InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3133InputLogOnePlusV_eq }

private noncomputable def leaf3133Inputs : Inputs :=
  inputsOfCaches globalInput sk217RoundedInputs
    chi197InputQChi innerPair71Input
    leaf3133InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3133LowerChecked :
    lowerCheck 24 leaf3133Box leaf3133Inputs = true := by
  rfl'

private theorem leaf3133CoversExact : CoversExact 8
    leaf3133Box leaf3133Certificate leaf3133InnerLog leaf3133Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk217RoundedFacts chi197RoundedFacts
    innerPair71RoundedFacts leaf3133RoundedFacts (by rfl)

private theorem leaf3133FlatSound : Sound leaf3133Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3133CertificateValid
    leaf3133InnerLogValid leaf3133CoversExact leaf3133LowerChecked

private noncomputable def leaf3134Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (233/64), kHi := (117/32), chiLo := (27/128), chiHi := (55/256) }

private noncomputable def leaf3134Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742401/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432364032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1898232105/1073741824) }, upper := { exponent := 0, mantissa := (14627/8192) } }, logOuter := sk218LogOuterCertificate, logK := sk218LogKCertificate, logChi := chi197LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869285887/274864728064) } }, logDArg := sk218LogDArgCertificate }

private noncomputable def leaf3134InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3134LocalValidity :
    LeafFacts leaf3134Box leaf3134Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3134Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432364032) }) = true
      norm_num [leaf3134Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3134CertificateValid :
    WideCertificateValid leaf3134Box leaf3134Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk218ValidityFacts chi197ValidityFacts
    leaf3134LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3134CoverageChecked :
    coverageCheck (innerAD leaf3134Box) leaf3134InnerLog = true := by
  rfl'

private theorem leaf3134InnerLogValid :
    leaf3134InnerLog.Valid 8 (innerAD leaf3134Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3134CoverageChecked

private noncomputable def leaf3134InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629359/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3134InputLogOnePlusV_eq :
    leaf3134InputLogOnePlusV = outerEnclosure 24
      (leaf3134Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3134RoundedFacts : LeafRoundedFacts 8
    leaf3134Certificate.logOnePlusV leaf3134InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3134InputLogOnePlusV_eq }

private noncomputable def leaf3134Inputs : Inputs :=
  inputsOfCaches globalInput sk218RoundedInputs
    chi197InputQChi innerPair71Input
    leaf3134InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3134LowerChecked :
    lowerCheck 24 leaf3134Box leaf3134Inputs = true := by
  rfl'

private theorem leaf3134CoversExact : CoversExact 8
    leaf3134Box leaf3134Certificate leaf3134InnerLog leaf3134Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk218RoundedFacts chi197RoundedFacts
    innerPair71RoundedFacts leaf3134RoundedFacts (by rfl)

private theorem leaf3134FlatSound : Sound leaf3134Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3134CertificateValid
    leaf3134InnerLogValid leaf3134CoversExact leaf3134LowerChecked

private noncomputable def leaf3135Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (233/64), chiLo := (55/256), chiHi := (7/32) }

private noncomputable def leaf3135Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742401/1073741824) }, vSqrt := { lower := (8191/8192), upper := (15270769095/15270252544) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1909896801/1073741824) }, upper := { exponent := 0, mantissa := (3679/2048) } }, logOuter := sk217LogOuterCertificate, logK := sk217LogKCertificate, logChi := chi198LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (30541021639/30540505088) } }, logDArg := sk217LogDArgCertificate }

private noncomputable def leaf3135InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3135LocalValidity :
    LeafFacts leaf3135Box leaf3135Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3135Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (15270769095/15270252544) }) = true
      norm_num [leaf3135Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3135CertificateValid :
    WideCertificateValid leaf3135Box leaf3135Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk217ValidityFacts chi198ValidityFacts
    leaf3135LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3135CoverageChecked :
    coverageCheck (innerAD leaf3135Box) leaf3135InnerLog = true := by
  rfl'

private theorem leaf3135InnerLogValid :
    leaf3135InnerLog.Valid 8 (innerAD leaf3135Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3135CoverageChecked

private noncomputable def leaf3135InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629365/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3135InputLogOnePlusV_eq :
    leaf3135InputLogOnePlusV = outerEnclosure 24
      (leaf3135Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3135RoundedFacts : LeafRoundedFacts 8
    leaf3135Certificate.logOnePlusV leaf3135InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3135InputLogOnePlusV_eq }

private noncomputable def leaf3135Inputs : Inputs :=
  inputsOfCaches globalInput sk217RoundedInputs
    chi198InputQChi innerPair71Input
    leaf3135InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3135LowerChecked :
    lowerCheck 24 leaf3135Box leaf3135Inputs = true := by
  rfl'

private theorem leaf3135CoversExact : CoversExact 8
    leaf3135Box leaf3135Certificate leaf3135InnerLog leaf3135Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk217RoundedFacts chi198RoundedFacts
    innerPair71RoundedFacts leaf3135RoundedFacts (by rfl)

private theorem leaf3135FlatSound : Sound leaf3135Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3135CertificateValid
    leaf3135InnerLogValid leaf3135CoversExact leaf3135LowerChecked

private noncomputable def leaf3136Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (233/64), kHi := (117/32), chiLo := (55/256), chiHi := (7/32) }

private noncomputable def leaf3136Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742403/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432244224) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1913501059/1073741824) }, upper := { exponent := 0, mantissa := (1843/1024) } }, logOuter := sk218LogOuterCertificate, logK := sk218LogKCertificate, logChi := chi198LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869166079/274864488448) } }, logDArg := sk218LogDArgCertificate }

private noncomputable def leaf3136InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3136LocalValidity :
    LeafFacts leaf3136Box leaf3136Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3136Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432244224) }) = true
      norm_num [leaf3136Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3136CertificateValid :
    WideCertificateValid leaf3136Box leaf3136Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk218ValidityFacts chi198ValidityFacts
    leaf3136LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3136CoverageChecked :
    coverageCheck (innerAD leaf3136Box) leaf3136InnerLog = true := by
  rfl'

private theorem leaf3136InnerLogValid :
    leaf3136InnerLog.Valid 8 (innerAD leaf3136Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3136CoverageChecked

private noncomputable def leaf3136InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814683/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3136InputLogOnePlusV_eq :
    leaf3136InputLogOnePlusV = outerEnclosure 24
      (leaf3136Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3136RoundedFacts : LeafRoundedFacts 8
    leaf3136Certificate.logOnePlusV leaf3136InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3136InputLogOnePlusV_eq }

private noncomputable def leaf3136Inputs : Inputs :=
  inputsOfCaches globalInput sk218RoundedInputs
    chi198InputQChi innerPair71Input
    leaf3136InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3136LowerChecked :
    lowerCheck 24 leaf3136Box leaf3136Inputs = true := by
  rfl'

private theorem leaf3136CoversExact : CoversExact 8
    leaf3136Box leaf3136Certificate leaf3136InnerLog leaf3136Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk218RoundedFacts chi198RoundedFacts
    innerPair71RoundedFacts leaf3136RoundedFacts (by rfl)

private theorem leaf3136FlatSound : Sound leaf3136Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3136CertificateValid
    leaf3136InnerLogValid leaf3136CoversExact leaf3136LowerChecked

private noncomputable def leaf3137Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (235/64), chiLo := (27/128), chiHi := (55/256) }

private noncomputable def leaf3137Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742403/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810778624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1901770831/1073741824) }, upper := { exponent := 0, mantissa := (29309/16384) } }, logOuter := sk219LogOuterCertificate, logK := sk219LogKCertificate, logChi := chi197LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623085909/91621557248) } }, logDArg := sk219LogDArgCertificate }

private noncomputable def leaf3137InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3137LocalValidity :
    LeafFacts leaf3137Box leaf3137Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3137Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810778624) }) = true
      norm_num [leaf3137Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3137CertificateValid :
    WideCertificateValid leaf3137Box leaf3137Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk219ValidityFacts chi197ValidityFacts
    leaf3137LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3137CoverageChecked :
    coverageCheck (innerAD leaf3137Box) leaf3137InnerLog = true := by
  rfl'

private theorem leaf3137InnerLogValid :
    leaf3137InnerLog.Valid 8 (innerAD leaf3137Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3137CoverageChecked

private noncomputable def leaf3137InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629361/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3137InputLogOnePlusV_eq :
    leaf3137InputLogOnePlusV = outerEnclosure 24
      (leaf3137Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3137RoundedFacts : LeafRoundedFacts 8
    leaf3137Certificate.logOnePlusV leaf3137InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3137InputLogOnePlusV_eq }

private noncomputable def leaf3137Inputs : Inputs :=
  inputsOfCaches globalInput sk219RoundedInputs
    chi197InputQChi innerPair71Input
    leaf3137InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3137LowerChecked :
    lowerCheck 24 leaf3137Box leaf3137Inputs = true := by
  rfl'

private theorem leaf3137CoversExact : CoversExact 8
    leaf3137Box leaf3137Certificate leaf3137InnerLog leaf3137Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk219RoundedFacts chi197RoundedFacts
    innerPair71RoundedFacts leaf3137RoundedFacts (by rfl)

private theorem leaf3137FlatSound : Sound leaf3137Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3137CertificateValid
    leaf3137InnerLogValid leaf3137CoversExact leaf3137LowerChecked

private noncomputable def leaf3138Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (235/64), kHi := (59/16), chiLo := (27/128), chiHi := (55/256) }

private noncomputable def leaf3138Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742405/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432307712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1905309557/1073741824) }, upper := { exponent := 0, mantissa := (7341/4096) } }, logOuter := sk220LogOuterCertificate, logK := sk220LogKCertificate, logChi := chi197LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869229567/274864615424) } }, logDArg := sk220LogDArgCertificate }

private noncomputable def leaf3138InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3138LocalValidity :
    LeafFacts leaf3138Box leaf3138Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3138Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432307712) }) = true
      norm_num [leaf3138Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3138CertificateValid :
    WideCertificateValid leaf3138Box leaf3138Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk220ValidityFacts chi197ValidityFacts
    leaf3138LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3138CoverageChecked :
    coverageCheck (innerAD leaf3138Box) leaf3138InnerLog = true := by
  rfl'

private theorem leaf3138InnerLogValid :
    leaf3138InnerLog.Valid 8 (innerAD leaf3138Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3138CoverageChecked

private noncomputable def leaf3138InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814681/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3138InputLogOnePlusV_eq :
    leaf3138InputLogOnePlusV = outerEnclosure 24
      (leaf3138Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3138RoundedFacts : LeafRoundedFacts 8
    leaf3138Certificate.logOnePlusV leaf3138InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3138InputLogOnePlusV_eq }

private noncomputable def leaf3138Inputs : Inputs :=
  inputsOfCaches globalInput sk220RoundedInputs
    chi197InputQChi innerPair71Input
    leaf3138InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3138LowerChecked :
    lowerCheck 24 leaf3138Box leaf3138Inputs = true := by
  rfl'

private theorem leaf3138CoversExact : CoversExact 8
    leaf3138Box leaf3138Certificate leaf3138InnerLog leaf3138Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk220RoundedFacts chi197RoundedFacts
    innerPair71RoundedFacts leaf3138RoundedFacts (by rfl)

private theorem leaf3138FlatSound : Sound leaf3138Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3138CertificateValid
    leaf3138InnerLogValid leaf3138CoversExact leaf3138LowerChecked

private noncomputable def leaf3139Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (235/64), chiLo := (55/256), chiHi := (7/32) }

private noncomputable def leaf3139Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742405/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432215552) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1917105317/1073741824) }, upper := { exponent := 0, mantissa := (3693/2048) } }, logOuter := sk219LogOuterCertificate, logK := sk219LogKCertificate, logChi := chi198LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869137407/274864431104) } }, logDArg := sk219LogDArgCertificate }

private noncomputable def leaf3139InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3139LocalValidity :
    LeafFacts leaf3139Box leaf3139Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3139Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432215552) }) = true
      norm_num [leaf3139Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3139CertificateValid :
    WideCertificateValid leaf3139Box leaf3139Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk219ValidityFacts chi198ValidityFacts
    leaf3139LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3139CoverageChecked :
    coverageCheck (innerAD leaf3139Box) leaf3139InnerLog = true := by
  rfl'

private theorem leaf3139InnerLogValid :
    leaf3139InnerLog.Valid 8 (innerAD leaf3139Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3139CoverageChecked

private noncomputable def leaf3139InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453671/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3139InputLogOnePlusV_eq :
    leaf3139InputLogOnePlusV = outerEnclosure 24
      (leaf3139Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3139RoundedFacts : LeafRoundedFacts 8
    leaf3139Certificate.logOnePlusV leaf3139InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3139InputLogOnePlusV_eq }

private noncomputable def leaf3139Inputs : Inputs :=
  inputsOfCaches globalInput sk219RoundedInputs
    chi198InputQChi innerPair71Input
    leaf3139InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3139LowerChecked :
    lowerCheck 24 leaf3139Box leaf3139Inputs = true := by
  rfl'

private theorem leaf3139CoversExact : CoversExact 8
    leaf3139Box leaf3139Certificate leaf3139InnerLog leaf3139Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk219RoundedFacts chi198RoundedFacts
    innerPair71RoundedFacts leaf3139RoundedFacts (by rfl)

private theorem leaf3139FlatSound : Sound leaf3139Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3139CertificateValid
    leaf3139InnerLogValid leaf3139CoversExact leaf3139LowerChecked

private noncomputable def leaf3140Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (235/64), kHi := (59/16), chiLo := (55/256), chiHi := (7/32) }

private noncomputable def leaf3140Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742407/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9162461457/9162145792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1920709575/1073741824) }, upper := { exponent := 0, mantissa := (925/512) } }, logOuter := sk220LogOuterCertificate, logK := sk220LogKCertificate, logChi := chi198LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (18324607249/18324291584) } }, logDArg := sk220LogDArgCertificate }

private noncomputable def leaf3140InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3140LocalValidity :
    LeafFacts leaf3140Box leaf3140Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3140Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9162461457/9162145792) }) = true
      norm_num [leaf3140Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3140CertificateValid :
    WideCertificateValid leaf3140Box leaf3140Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk220ValidityFacts chi198ValidityFacts
    leaf3140LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3140CoverageChecked :
    coverageCheck (innerAD leaf3140Box) leaf3140InnerLog = true := by
  rfl'

private theorem leaf3140InnerLogValid :
    leaf3140InnerLog.Valid 8 (innerAD leaf3140Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3140CoverageChecked

private noncomputable def leaf3140InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814685/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3140InputLogOnePlusV_eq :
    leaf3140InputLogOnePlusV = outerEnclosure 24
      (leaf3140Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3140RoundedFacts : LeafRoundedFacts 8
    leaf3140Certificate.logOnePlusV leaf3140InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3140InputLogOnePlusV_eq }

private noncomputable def leaf3140Inputs : Inputs :=
  inputsOfCaches globalInput sk220RoundedInputs
    chi198InputQChi innerPair71Input
    leaf3140InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3140LowerChecked :
    lowerCheck 24 leaf3140Box leaf3140Inputs = true := by
  rfl'

private theorem leaf3140CoversExact : CoversExact 8
    leaf3140Box leaf3140Certificate leaf3140InnerLog leaf3140Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk220RoundedFacts chi198RoundedFacts
    innerPair71RoundedFacts leaf3140RoundedFacts (by rfl)

private theorem leaf3140FlatSound : Sound leaf3140Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3140CertificateValid
    leaf3140InnerLogValid leaf3140CoversExact leaf3140LowerChecked

private noncomputable def leaf3141Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (237/64), chiLo := (13/64), chiHi := (53/256) }

private noncomputable def leaf3141Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742403/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486504448) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1877917183/1073741824) }, upper := { exponent := 0, mantissa := (28945/16384) } }, logOuter := sk221LogOuterCertificate, logK := sk221LogKCertificate, logChi := chi195LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973888819/54973008896) } }, logDArg := sk221LogDArgCertificate }

private noncomputable def leaf3141InnerLog : WideLogData :=
  innerPair431Data

set_option maxRecDepth 1000000 in
private theorem leaf3141LocalValidity :
    LeafFacts leaf3141Box leaf3141Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3141Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486504448) }) = true
      norm_num [leaf3141Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3141CertificateValid :
    WideCertificateValid leaf3141Box leaf3141Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk221ValidityFacts chi195ValidityFacts
    leaf3141LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3141CoverageChecked :
    coverageCheck (innerAD leaf3141Box) leaf3141InnerLog = true := by
  rfl'

private theorem leaf3141InnerLogValid :
    leaf3141InnerLog.Valid 8 (innerAD leaf3141Box) :=
  wideLogDataValid_of_cachedCheck endpoint139PositiveFacts
    endpoint68PositiveFacts.valid leaf3141CoverageChecked

private noncomputable def leaf3141InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629349/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3141InputLogOnePlusV_eq :
    leaf3141InputLogOnePlusV = outerEnclosure 24
      (leaf3141Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3141RoundedFacts : LeafRoundedFacts 8
    leaf3141Certificate.logOnePlusV leaf3141InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3141InputLogOnePlusV_eq }

private noncomputable def leaf3141Inputs : Inputs :=
  inputsOfCaches globalInput sk221RoundedInputs
    chi195InputQChi innerPair431Input
    leaf3141InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3141LowerChecked :
    lowerCheck 24 leaf3141Box leaf3141Inputs = true := by
  rfl'

private theorem leaf3141CoversExact : CoversExact 8
    leaf3141Box leaf3141Certificate leaf3141InnerLog leaf3141Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk221RoundedFacts chi195RoundedFacts
    innerPair431RoundedFacts leaf3141RoundedFacts (by rfl)

private theorem leaf3141FlatSound : Sound leaf3141Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3141CertificateValid
    leaf3141InnerLogValid leaf3141CoversExact leaf3141LowerChecked

private noncomputable def leaf3142Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (237/64), kHi := (119/32), chiLo := (13/64), chiHi := (53/256) }

private noncomputable def leaf3142Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742405/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432495104) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1881324845/1073741824) }, upper := { exponent := 0, mantissa := (14499/8192) } }, logOuter := sk222LogOuterCertificate, logK := sk222LogKCertificate, logChi := chi195LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869416959/274864990208) } }, logDArg := sk222LogDArgCertificate }

private noncomputable def leaf3142InnerLog : WideLogData :=
  innerPair78Data

set_option maxRecDepth 1000000 in
private theorem leaf3142LocalValidity :
    LeafFacts leaf3142Box leaf3142Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3142Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432495104) }) = true
      norm_num [leaf3142Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3142CertificateValid :
    WideCertificateValid leaf3142Box leaf3142Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk222ValidityFacts chi195ValidityFacts
    leaf3142LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3142CoverageChecked :
    coverageCheck (innerAD leaf3142Box) leaf3142InnerLog = true := by
  rfl'

private theorem leaf3142InnerLogValid :
    leaf3142InnerLog.Valid 8 (innerAD leaf3142Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint68PositiveFacts.valid leaf3142CoverageChecked

private noncomputable def leaf3142InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629351/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3142InputLogOnePlusV_eq :
    leaf3142InputLogOnePlusV = outerEnclosure 24
      (leaf3142Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3142RoundedFacts : LeafRoundedFacts 8
    leaf3142Certificate.logOnePlusV leaf3142InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3142InputLogOnePlusV_eq }

private noncomputable def leaf3142Inputs : Inputs :=
  inputsOfCaches globalInput sk222RoundedInputs
    chi195InputQChi innerPair78Input
    leaf3142InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3142LowerChecked :
    lowerCheck 24 leaf3142Box leaf3142Inputs = true := by
  rfl'

private theorem leaf3142CoversExact : CoversExact 8
    leaf3142Box leaf3142Certificate leaf3142InnerLog leaf3142Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk222RoundedFacts chi195RoundedFacts
    innerPair78RoundedFacts leaf3142RoundedFacts (by rfl)

private theorem leaf3142FlatSound : Sound leaf3142Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3142CertificateValid
    leaf3142InnerLogValid leaf3142CoversExact leaf3142LowerChecked

private noncomputable def leaf3143Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (237/64), chiLo := (53/256), chiHi := (27/128) }

private noncomputable def leaf3143Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742405/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432400896) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1893382733/1073741824) }, upper := { exponent := 0, mantissa := (14591/8192) } }, logOuter := sk221LogOuterCertificate, logK := sk221LogKCertificate, logChi := chi196LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869322751/274864801792) } }, logDArg := sk221LogDArgCertificate }

private noncomputable def leaf3143InnerLog : WideLogData :=
  innerPair78Data

set_option maxRecDepth 1000000 in
private theorem leaf3143LocalValidity :
    LeafFacts leaf3143Box leaf3143Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3143Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432400896) }) = true
      norm_num [leaf3143Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3143CertificateValid :
    WideCertificateValid leaf3143Box leaf3143Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk221ValidityFacts chi196ValidityFacts
    leaf3143LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3143CoverageChecked :
    coverageCheck (innerAD leaf3143Box) leaf3143InnerLog = true := by
  rfl'

private theorem leaf3143InnerLogValid :
    leaf3143InnerLog.Valid 8 (innerAD leaf3143Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint68PositiveFacts.valid leaf3143CoverageChecked

private noncomputable def leaf3143InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629357/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3143InputLogOnePlusV_eq :
    leaf3143InputLogOnePlusV = outerEnclosure 24
      (leaf3143Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3143RoundedFacts : LeafRoundedFacts 8
    leaf3143Certificate.logOnePlusV leaf3143InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3143InputLogOnePlusV_eq }

private noncomputable def leaf3143Inputs : Inputs :=
  inputsOfCaches globalInput sk221RoundedInputs
    chi196InputQChi innerPair78Input
    leaf3143InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3143LowerChecked :
    lowerCheck 24 leaf3143Box leaf3143Inputs = true := by
  rfl'

private theorem leaf3143CoversExact : CoversExact 8
    leaf3143Box leaf3143Certificate leaf3143InnerLog leaf3143Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk221RoundedFacts chi196RoundedFacts
    innerPair78RoundedFacts leaf3143RoundedFacts (by rfl)

private theorem leaf3143FlatSound : Sound leaf3143Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3143CertificateValid
    leaf3143InnerLogValid leaf3143CoversExact leaf3143LowerChecked

private noncomputable def leaf3144Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (237/64), kHi := (119/32), chiLo := (53/256), chiHi := (27/128) }

private noncomputable def leaf3144Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742407/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432373248) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1896855927/1073741824) }, upper := { exponent := 0, mantissa := (7309/4096) } }, logOuter := sk222LogOuterCertificate, logK := sk222LogKCertificate, logChi := chi196LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869295103/274864746496) } }, logDArg := sk222LogDArgCertificate }

private noncomputable def leaf3144InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3144LocalValidity :
    LeafFacts leaf3144Box leaf3144Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3144Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432373248) }) = true
      norm_num [leaf3144Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3144CertificateValid :
    WideCertificateValid leaf3144Box leaf3144Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk222ValidityFacts chi196ValidityFacts
    leaf3144LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3144CoverageChecked :
    coverageCheck (innerAD leaf3144Box) leaf3144InnerLog = true := by
  rfl'

private theorem leaf3144InnerLogValid :
    leaf3144InnerLog.Valid 8 (innerAD leaf3144Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3144CoverageChecked

private noncomputable def leaf3144InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814679/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3144InputLogOnePlusV_eq :
    leaf3144InputLogOnePlusV = outerEnclosure 24
      (leaf3144Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3144RoundedFacts : LeafRoundedFacts 8
    leaf3144Certificate.logOnePlusV leaf3144InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3144InputLogOnePlusV_eq }

private noncomputable def leaf3144Inputs : Inputs :=
  inputsOfCaches globalInput sk222RoundedInputs
    chi196InputQChi innerPair71Input
    leaf3144InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3144LowerChecked :
    lowerCheck 24 leaf3144Box leaf3144Inputs = true := by
  rfl'

private theorem leaf3144CoversExact : CoversExact 8
    leaf3144Box leaf3144Certificate leaf3144InnerLog leaf3144Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk222RoundedFacts chi196RoundedFacts
    innerPair71RoundedFacts leaf3144RoundedFacts (by rfl)

private theorem leaf3144FlatSound : Sound leaf3144Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3144CertificateValid
    leaf3144InnerLogValid leaf3144CoversExact leaf3144LowerChecked

private noncomputable def leaf3145Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (239/64), chiLo := (13/64), chiHi := (53/256) }

private noncomputable def leaf3145Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742407/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810822656) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1884732507/1073741824) }, upper := { exponent := 0, mantissa := (29051/16384) } }, logOuter := sk223LogOuterCertificate, logK := sk223LogKCertificate, logChi := chi195LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623129941/91621645312) } }, logDArg := sk223LogDArgCertificate }

private noncomputable def leaf3145InnerLog : WideLogData :=
  innerPair78Data

set_option maxRecDepth 1000000 in
private theorem leaf3145LocalValidity :
    LeafFacts leaf3145Box leaf3145Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3145Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810822656) }) = true
      norm_num [leaf3145Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3145CertificateValid :
    WideCertificateValid leaf3145Box leaf3145Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk223ValidityFacts chi195ValidityFacts
    leaf3145LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3145CoverageChecked :
    coverageCheck (innerAD leaf3145Box) leaf3145InnerLog = true := by
  rfl'

private theorem leaf3145InnerLogValid :
    leaf3145InnerLog.Valid 8 (innerAD leaf3145Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint68PositiveFacts.valid leaf3145CoverageChecked

private noncomputable def leaf3145InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629353/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3145InputLogOnePlusV_eq :
    leaf3145InputLogOnePlusV = outerEnclosure 24
      (leaf3145Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3145RoundedFacts : LeafRoundedFacts 8
    leaf3145Certificate.logOnePlusV leaf3145InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3145InputLogOnePlusV_eq }

private noncomputable def leaf3145Inputs : Inputs :=
  inputsOfCaches globalInput sk223RoundedInputs
    chi195InputQChi innerPair78Input
    leaf3145InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3145LowerChecked :
    lowerCheck 24 leaf3145Box leaf3145Inputs = true := by
  rfl'

private theorem leaf3145CoversExact : CoversExact 8
    leaf3145Box leaf3145Certificate leaf3145InnerLog leaf3145Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk223RoundedFacts chi195RoundedFacts
    innerPair78RoundedFacts leaf3145RoundedFacts (by rfl)

private theorem leaf3145FlatSound : Sound leaf3145Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3145CertificateValid
    leaf3145InnerLogValid leaf3145CoversExact leaf3145LowerChecked

private noncomputable def leaf3146Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (239/64), kHi := (15/4), chiLo := (13/64), chiHi := (53/256) }

private noncomputable def leaf3146Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742409/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432440832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1888140169/1073741824) }, upper := { exponent := 0, mantissa := (1819/1024) } }, logOuter := sk224LogOuterCertificate, logK := sk224LogKCertificate, logChi := chi195LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869362687/274864881664) } }, logDArg := sk224LogDArgCertificate }

private noncomputable def leaf3146InnerLog : WideLogData :=
  innerPair78Data

set_option maxRecDepth 1000000 in
private theorem leaf3146LocalValidity :
    LeafFacts leaf3146Box leaf3146Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3146Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432440832) }) = true
      norm_num [leaf3146Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3146CertificateValid :
    WideCertificateValid leaf3146Box leaf3146Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk224ValidityFacts chi195ValidityFacts
    leaf3146LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3146CoverageChecked :
    coverageCheck (innerAD leaf3146Box) leaf3146InnerLog = true := by
  rfl'

private theorem leaf3146InnerLogValid :
    leaf3146InnerLog.Valid 8 (innerAD leaf3146Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint68PositiveFacts.valid leaf3146CoverageChecked

private noncomputable def leaf3146InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814677/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3146InputLogOnePlusV_eq :
    leaf3146InputLogOnePlusV = outerEnclosure 24
      (leaf3146Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3146RoundedFacts : LeafRoundedFacts 8
    leaf3146Certificate.logOnePlusV leaf3146InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3146InputLogOnePlusV_eq }

private noncomputable def leaf3146Inputs : Inputs :=
  inputsOfCaches globalInput sk224RoundedInputs
    chi195InputQChi innerPair78Input
    leaf3146InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3146LowerChecked :
    lowerCheck 24 leaf3146Box leaf3146Inputs = true := by
  rfl'

private theorem leaf3146CoversExact : CoversExact 8
    leaf3146Box leaf3146Certificate leaf3146InnerLog leaf3146Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk224RoundedFacts chi195RoundedFacts
    innerPair78RoundedFacts leaf3146RoundedFacts (by rfl)

private theorem leaf3146FlatSound : Sound leaf3146Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3146CertificateValid
    leaf3146InnerLogValid leaf3146CoversExact leaf3146LowerChecked

private noncomputable def leaf3147Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (239/64), chiLo := (53/256), chiHi := (27/128) }

private noncomputable def leaf3147Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742409/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486469120) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1900329121/1073741824) }, upper := { exponent := 0, mantissa := (14645/8192) } }, logOuter := sk223LogOuterCertificate, logK := sk223LogKCertificate, logChi := chi196LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973853491/54972938240) } }, logDArg := sk223LogDArgCertificate }

private noncomputable def leaf3147InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3147LocalValidity :
    LeafFacts leaf3147Box leaf3147Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3147Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486469120) }) = true
      norm_num [leaf3147Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3147CertificateValid :
    WideCertificateValid leaf3147Box leaf3147Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk223ValidityFacts chi196ValidityFacts
    leaf3147LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3147CoverageChecked :
    coverageCheck (innerAD leaf3147Box) leaf3147InnerLog = true := by
  rfl'

private theorem leaf3147InnerLogValid :
    leaf3147InnerLog.Valid 8 (innerAD leaf3147Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3147CoverageChecked

private noncomputable def leaf3147InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726835/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf3147InputLogOnePlusV_eq :
    leaf3147InputLogOnePlusV = outerEnclosure 24
      (leaf3147Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3147RoundedFacts : LeafRoundedFacts 8
    leaf3147Certificate.logOnePlusV leaf3147InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3147InputLogOnePlusV_eq }

private noncomputable def leaf3147Inputs : Inputs :=
  inputsOfCaches globalInput sk223RoundedInputs
    chi196InputQChi innerPair71Input
    leaf3147InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3147LowerChecked :
    lowerCheck 24 leaf3147Box leaf3147Inputs = true := by
  rfl'

private theorem leaf3147CoversExact : CoversExact 8
    leaf3147Box leaf3147Certificate leaf3147InnerLog leaf3147Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk223RoundedFacts chi196RoundedFacts
    innerPair71RoundedFacts leaf3147RoundedFacts (by rfl)

private theorem leaf3147FlatSound : Sound leaf3147Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3147CertificateValid
    leaf3147InnerLogValid leaf3147CoversExact leaf3147LowerChecked

private noncomputable def leaf3148Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (239/64), kHi := (15/4), chiLo := (53/256), chiHi := (27/128) }

private noncomputable def leaf3148Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742411/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432317952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1903802315/1073741824) }, upper := { exponent := 0, mantissa := (917/512) } }, logOuter := sk224LogOuterCertificate, logK := sk224LogKCertificate, logChi := chi196LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869239807/274864635904) } }, logDArg := sk224LogDArgCertificate }

private noncomputable def leaf3148InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3148LocalValidity :
    LeafFacts leaf3148Box leaf3148Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3148Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432317952) }) = true
      norm_num [leaf3148Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3148CertificateValid :
    WideCertificateValid leaf3148Box leaf3148Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk224ValidityFacts chi196ValidityFacts
    leaf3148LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3148CoverageChecked :
    coverageCheck (innerAD leaf3148Box) leaf3148InnerLog = true := by
  rfl'

private theorem leaf3148InnerLogValid :
    leaf3148InnerLog.Valid 8 (innerAD leaf3148Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3148CoverageChecked

private noncomputable def leaf3148InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814681/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3148InputLogOnePlusV_eq :
    leaf3148InputLogOnePlusV = outerEnclosure 24
      (leaf3148Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3148RoundedFacts : LeafRoundedFacts 8
    leaf3148Certificate.logOnePlusV leaf3148InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3148InputLogOnePlusV_eq }

private noncomputable def leaf3148Inputs : Inputs :=
  inputsOfCaches globalInput sk224RoundedInputs
    chi196InputQChi innerPair71Input
    leaf3148InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3148LowerChecked :
    lowerCheck 24 leaf3148Box leaf3148Inputs = true := by
  rfl'

private theorem leaf3148CoversExact : CoversExact 8
    leaf3148Box leaf3148Certificate leaf3148InnerLog leaf3148Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk224RoundedFacts chi196RoundedFacts
    innerPair71RoundedFacts leaf3148RoundedFacts (by rfl)

private theorem leaf3148FlatSound : Sound leaf3148Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3148CertificateValid
    leaf3148InnerLogValid leaf3148CoversExact leaf3148LowerChecked

private noncomputable def leaf3149Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (237/64), chiLo := (27/128), chiHi := (55/256) }

private noncomputable def leaf3149Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742407/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432279552) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1908848283/1073741824) }, upper := { exponent := 0, mantissa := (29419/16384) } }, logOuter := sk221LogOuterCertificate, logK := sk221LogKCertificate, logChi := chi197LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869201407/274864559104) } }, logDArg := sk221LogDArgCertificate }

private noncomputable def leaf3149InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3149LocalValidity :
    LeafFacts leaf3149Box leaf3149Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3149Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432279552) }) = true
      norm_num [leaf3149Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3149CertificateValid :
    WideCertificateValid leaf3149Box leaf3149Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk221ValidityFacts chi197ValidityFacts
    leaf3149LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3149CoverageChecked :
    coverageCheck (innerAD leaf3149Box) leaf3149InnerLog = true := by
  rfl'

private theorem leaf3149InnerLogValid :
    leaf3149InnerLog.Valid 8 (innerAD leaf3149Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3149CoverageChecked

private noncomputable def leaf3149InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907341/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3149InputLogOnePlusV_eq :
    leaf3149InputLogOnePlusV = outerEnclosure 24
      (leaf3149Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3149RoundedFacts : LeafRoundedFacts 8
    leaf3149Certificate.logOnePlusV leaf3149InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3149InputLogOnePlusV_eq }

private noncomputable def leaf3149Inputs : Inputs :=
  inputsOfCaches globalInput sk221RoundedInputs
    chi197InputQChi innerPair71Input
    leaf3149InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3149LowerChecked :
    lowerCheck 24 leaf3149Box leaf3149Inputs = true := by
  rfl'

private theorem leaf3149CoversExact : CoversExact 8
    leaf3149Box leaf3149Certificate leaf3149InnerLog leaf3149Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk221RoundedFacts chi197RoundedFacts
    innerPair71RoundedFacts leaf3149RoundedFacts (by rfl)

private theorem leaf3149FlatSound : Sound leaf3149Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3149CertificateValid
    leaf3149InnerLogValid leaf3149CoversExact leaf3149LowerChecked

private noncomputable def leaf3150Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (237/64), kHi := (119/32), chiLo := (27/128), chiHi := (55/256) }

private noncomputable def leaf3150Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742409/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810750464) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1912387009/1073741824) }, upper := { exponent := 0, mantissa := (14737/8192) } }, logOuter := sk222LogOuterCertificate, logK := sk222LogKCertificate, logChi := chi197LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623057749/91621500928) } }, logDArg := sk222LogDArgCertificate }

private noncomputable def leaf3150InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3150LocalValidity :
    LeafFacts leaf3150Box leaf3150Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3150Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810750464) }) = true
      norm_num [leaf3150Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3150CertificateValid :
    WideCertificateValid leaf3150Box leaf3150Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk222ValidityFacts chi197ValidityFacts
    leaf3150LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3150CoverageChecked :
    coverageCheck (innerAD leaf3150Box) leaf3150InnerLog = true := by
  rfl'

private theorem leaf3150InnerLogValid :
    leaf3150InnerLog.Valid 8 (innerAD leaf3150Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3150CoverageChecked

private noncomputable def leaf3150InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814683/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3150InputLogOnePlusV_eq :
    leaf3150InputLogOnePlusV = outerEnclosure 24
      (leaf3150Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3150RoundedFacts : LeafRoundedFacts 8
    leaf3150Certificate.logOnePlusV leaf3150InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3150InputLogOnePlusV_eq }

private noncomputable def leaf3150Inputs : Inputs :=
  inputsOfCaches globalInput sk222RoundedInputs
    chi197InputQChi innerPair71Input
    leaf3150InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3150LowerChecked :
    lowerCheck 24 leaf3150Box leaf3150Inputs = true := by
  rfl'

private theorem leaf3150CoversExact : CoversExact 8
    leaf3150Box leaf3150Certificate leaf3150InnerLog leaf3150Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk222RoundedFacts chi197RoundedFacts
    innerPair71RoundedFacts leaf3150RoundedFacts (by rfl)

private theorem leaf3150FlatSound : Sound leaf3150Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3150CertificateValid
    leaf3150InnerLogValid leaf3150CoversExact leaf3150LowerChecked

private noncomputable def leaf3151Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (237/64), chiLo := (55/256), chiHi := (7/32) }

private noncomputable def leaf3151Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742409/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432158208) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1924313833/1073741824) }, upper := { exponent := 0, mantissa := (3707/2048) } }, logOuter := sk221LogOuterCertificate, logK := sk221LogKCertificate, logChi := chi198LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869080063/274864316416) } }, logDArg := sk221LogDArgCertificate }

private noncomputable def leaf3151InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3151LocalValidity :
    LeafFacts leaf3151Box leaf3151Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3151Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432158208) }) = true
      norm_num [leaf3151Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3151CertificateValid :
    WideCertificateValid leaf3151Box leaf3151Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk221ValidityFacts chi198ValidityFacts
    leaf3151LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3151CoverageChecked :
    coverageCheck (innerAD leaf3151Box) leaf3151InnerLog = true := by
  rfl'

private theorem leaf3151InnerLogValid :
    leaf3151InnerLog.Valid 8 (innerAD leaf3151Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3151CoverageChecked

private noncomputable def leaf3151InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907343/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3151InputLogOnePlusV_eq :
    leaf3151InputLogOnePlusV = outerEnclosure 24
      (leaf3151Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3151RoundedFacts : LeafRoundedFacts 8
    leaf3151Certificate.logOnePlusV leaf3151InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3151InputLogOnePlusV_eq }

private noncomputable def leaf3151Inputs : Inputs :=
  inputsOfCaches globalInput sk221RoundedInputs
    chi198InputQChi innerPair71Input
    leaf3151InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3151LowerChecked :
    lowerCheck 24 leaf3151Box leaf3151Inputs = true := by
  rfl'

private theorem leaf3151CoversExact : CoversExact 8
    leaf3151Box leaf3151Certificate leaf3151InnerLog leaf3151Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk221RoundedFacts chi198RoundedFacts
    innerPair71RoundedFacts leaf3151RoundedFacts (by rfl)

private theorem leaf3151FlatSound : Sound leaf3151Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3151CertificateValid
    leaf3151InnerLogValid leaf3151CoversExact leaf3151LowerChecked

private noncomputable def leaf3152Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (237/64), kHi := (119/32), chiLo := (55/256), chiHi := (7/32) }

private noncomputable def leaf3152Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742411/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432129536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1927918091/1073741824) }, upper := { exponent := 0, mantissa := (1857/1024) } }, logOuter := sk222LogOuterCertificate, logK := sk222LogKCertificate, logChi := chi198LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869051391/274864259072) } }, logDArg := sk222LogDArgCertificate }

private noncomputable def leaf3152InnerLog : WideLogData :=
  innerPair226Data

set_option maxRecDepth 1000000 in
private theorem leaf3152LocalValidity :
    LeafFacts leaf3152Box leaf3152Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3152Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432129536) }) = true
      norm_num [leaf3152Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3152CertificateValid :
    WideCertificateValid leaf3152Box leaf3152Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk222ValidityFacts chi198ValidityFacts
    leaf3152LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3152CoverageChecked :
    coverageCheck (innerAD leaf3152Box) leaf3152InnerLog = true := by
  rfl'

private theorem leaf3152InnerLogValid :
    leaf3152InnerLog.Valid 8 (innerAD leaf3152Box) :=
  wideLogDataValid_of_cachedCheck endpoint68PositiveFacts
    endpoint64PositiveFacts.valid leaf3152CoverageChecked

private noncomputable def leaf3152InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629373/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3152InputLogOnePlusV_eq :
    leaf3152InputLogOnePlusV = outerEnclosure 24
      (leaf3152Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3152RoundedFacts : LeafRoundedFacts 8
    leaf3152Certificate.logOnePlusV leaf3152InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3152InputLogOnePlusV_eq }

private noncomputable def leaf3152Inputs : Inputs :=
  inputsOfCaches globalInput sk222RoundedInputs
    chi198InputQChi innerPair226Input
    leaf3152InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3152LowerChecked :
    lowerCheck 24 leaf3152Box leaf3152Inputs = true := by
  rfl'

private theorem leaf3152CoversExact : CoversExact 8
    leaf3152Box leaf3152Certificate leaf3152InnerLog leaf3152Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk222RoundedFacts chi198RoundedFacts
    innerPair226RoundedFacts leaf3152RoundedFacts (by rfl)

private theorem leaf3152FlatSound : Sound leaf3152Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3152CertificateValid
    leaf3152InnerLogValid leaf3152CoversExact leaf3152LowerChecked

private noncomputable def leaf3153Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (239/64), chiLo := (27/128), chiHi := (55/256) }

private noncomputable def leaf3153Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742411/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432223232) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1915925735/1073741824) }, upper := { exponent := 0, mantissa := (29529/16384) } }, logOuter := sk223LogOuterCertificate, logK := sk223LogKCertificate, logChi := chi197LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869145087/274864446464) } }, logDArg := sk223LogDArgCertificate }

private noncomputable def leaf3153InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3153LocalValidity :
    LeafFacts leaf3153Box leaf3153Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3153Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432223232) }) = true
      norm_num [leaf3153Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3153CertificateValid :
    WideCertificateValid leaf3153Box leaf3153Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk223ValidityFacts chi197ValidityFacts
    leaf3153LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3153CoverageChecked :
    coverageCheck (innerAD leaf3153Box) leaf3153InnerLog = true := by
  rfl'

private theorem leaf3153InnerLogValid :
    leaf3153InnerLog.Valid 8 (innerAD leaf3153Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3153CoverageChecked

private noncomputable def leaf3153InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453671/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3153InputLogOnePlusV_eq :
    leaf3153InputLogOnePlusV = outerEnclosure 24
      (leaf3153Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3153RoundedFacts : LeafRoundedFacts 8
    leaf3153Certificate.logOnePlusV leaf3153InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3153InputLogOnePlusV_eq }

private noncomputable def leaf3153Inputs : Inputs :=
  inputsOfCaches globalInput sk223RoundedInputs
    chi197InputQChi innerPair71Input
    leaf3153InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3153LowerChecked :
    lowerCheck 24 leaf3153Box leaf3153Inputs = true := by
  rfl'

private theorem leaf3153CoversExact : CoversExact 8
    leaf3153Box leaf3153Certificate leaf3153InnerLog leaf3153Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk223RoundedFacts chi197RoundedFacts
    innerPair71RoundedFacts leaf3153RoundedFacts (by rfl)

private theorem leaf3153FlatSound : Sound leaf3153Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3153CertificateValid
    leaf3153InnerLogValid leaf3153CoversExact leaf3153LowerChecked

private noncomputable def leaf3154Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (239/64), kHi := (15/4), chiLo := (27/128), chiHi := (55/256) }

private noncomputable def leaf3154Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742413/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432195072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1919464461/1073741824) }, upper := { exponent := 0, mantissa := (1849/1024) } }, logOuter := sk224LogOuterCertificate, logK := sk224LogKCertificate, logChi := chi197LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869116927/274864390144) } }, logDArg := sk224LogDArgCertificate }

private noncomputable def leaf3154InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3154LocalValidity :
    LeafFacts leaf3154Box leaf3154Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3154Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432195072) }) = true
      norm_num [leaf3154Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3154CertificateValid :
    WideCertificateValid leaf3154Box leaf3154Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk224ValidityFacts chi197ValidityFacts
    leaf3154LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3154CoverageChecked :
    coverageCheck (innerAD leaf3154Box) leaf3154InnerLog = true := by
  rfl'

private theorem leaf3154InnerLogValid :
    leaf3154InnerLog.Valid 8 (innerAD leaf3154Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3154CoverageChecked

private noncomputable def leaf3154InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629369/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3154InputLogOnePlusV_eq :
    leaf3154InputLogOnePlusV = outerEnclosure 24
      (leaf3154Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3154RoundedFacts : LeafRoundedFacts 8
    leaf3154Certificate.logOnePlusV leaf3154InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3154InputLogOnePlusV_eq }

private noncomputable def leaf3154Inputs : Inputs :=
  inputsOfCaches globalInput sk224RoundedInputs
    chi197InputQChi innerPair71Input
    leaf3154InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3154LowerChecked :
    lowerCheck 24 leaf3154Box leaf3154Inputs = true := by
  rfl'

private theorem leaf3154CoversExact : CoversExact 8
    leaf3154Box leaf3154Certificate leaf3154InnerLog leaf3154Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk224RoundedFacts chi197RoundedFacts
    innerPair71RoundedFacts leaf3154RoundedFacts (by rfl)

private theorem leaf3154FlatSound : Sound leaf3154Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3154CertificateValid
    leaf3154InnerLogValid leaf3154CoversExact leaf3154LowerChecked

private noncomputable def leaf3155Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (239/64), chiLo := (55/256), chiHi := (7/32) }

private noncomputable def leaf3155Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742413/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810700288) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1931522349/1073741824) }, upper := { exponent := 0, mantissa := (3721/2048) } }, logOuter := sk223LogOuterCertificate, logK := sk223LogKCertificate, logChi := chi198LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623007573/91621400576) } }, logDArg := sk223LogDArgCertificate }

private noncomputable def leaf3155InnerLog : WideLogData :=
  innerPair221Data

set_option maxRecDepth 1000000 in
private theorem leaf3155LocalValidity :
    LeafFacts leaf3155Box leaf3155Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3155Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810700288) }) = true
      norm_num [leaf3155Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3155CertificateValid :
    WideCertificateValid leaf3155Box leaf3155Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk223ValidityFacts chi198ValidityFacts
    leaf3155LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3155CoverageChecked :
    coverageCheck (innerAD leaf3155Box) leaf3155InnerLog = true := by
  rfl'

private theorem leaf3155InnerLogValid :
    leaf3155InnerLog.Valid 8 (innerAD leaf3155Box) :=
  wideLogDataValid_of_cachedCheck endpoint67PositiveFacts
    endpoint64PositiveFacts.valid leaf3155CoverageChecked

private noncomputable def leaf3155InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629375/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3155InputLogOnePlusV_eq :
    leaf3155InputLogOnePlusV = outerEnclosure 24
      (leaf3155Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3155RoundedFacts : LeafRoundedFacts 8
    leaf3155Certificate.logOnePlusV leaf3155InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3155InputLogOnePlusV_eq }

private noncomputable def leaf3155Inputs : Inputs :=
  inputsOfCaches globalInput sk223RoundedInputs
    chi198InputQChi innerPair221Input
    leaf3155InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3155LowerChecked :
    lowerCheck 24 leaf3155Box leaf3155Inputs = true := by
  rfl'

private theorem leaf3155CoversExact : CoversExact 8
    leaf3155Box leaf3155Certificate leaf3155InnerLog leaf3155Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk223RoundedFacts chi198RoundedFacts
    innerPair221RoundedFacts leaf3155RoundedFacts (by rfl)

private theorem leaf3155FlatSound : Sound leaf3155Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3155CertificateValid
    leaf3155InnerLogValid leaf3155CoversExact leaf3155LowerChecked

private noncomputable def leaf3156Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (239/64), kHi := (15/4), chiLo := (55/256), chiHi := (7/32) }

private noncomputable def leaf3156Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742415/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432072192) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1935126607/1073741824) }, upper := { exponent := 0, mantissa := (233/128) } }, logOuter := sk224LogOuterCertificate, logK := sk224LogKCertificate, logChi := chi198LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868994047/274864144384) } }, logDArg := sk224LogDArgCertificate }

private noncomputable def leaf3156InnerLog : WideLogData :=
  innerPair221Data

set_option maxRecDepth 1000000 in
private theorem leaf3156LocalValidity :
    LeafFacts leaf3156Box leaf3156Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3156Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432072192) }) = true
      norm_num [leaf3156Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3156CertificateValid :
    WideCertificateValid leaf3156Box leaf3156Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk224ValidityFacts chi198ValidityFacts
    leaf3156LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3156CoverageChecked :
    coverageCheck (innerAD leaf3156Box) leaf3156InnerLog = true := by
  rfl'

private theorem leaf3156InnerLogValid :
    leaf3156InnerLog.Valid 8 (innerAD leaf3156Box) :=
  wideLogDataValid_of_cachedCheck endpoint67PositiveFacts
    endpoint64PositiveFacts.valid leaf3156CoverageChecked

private noncomputable def leaf3156InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629377/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3156InputLogOnePlusV_eq :
    leaf3156InputLogOnePlusV = outerEnclosure 24
      (leaf3156Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3156RoundedFacts : LeafRoundedFacts 8
    leaf3156Certificate.logOnePlusV leaf3156InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3156InputLogOnePlusV_eq }

private noncomputable def leaf3156Inputs : Inputs :=
  inputsOfCaches globalInput sk224RoundedInputs
    chi198InputQChi innerPair221Input
    leaf3156InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3156LowerChecked :
    lowerCheck 24 leaf3156Box leaf3156Inputs = true := by
  rfl'

private theorem leaf3156CoversExact : CoversExact 8
    leaf3156Box leaf3156Certificate leaf3156InnerLog leaf3156Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk224RoundedFacts chi198RoundedFacts
    innerPair221RoundedFacts leaf3156RoundedFacts (by rfl)

private theorem leaf3156FlatSound : Sound leaf3156Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3156CertificateValid
    leaf3156InnerLogValid leaf3156CoversExact leaf3156LowerChecked

private noncomputable def component65Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (3/16), chiHi := (49/256) }

set_option maxRecDepth 1000000 in
private theorem component65Node0_sound : Sound component65Node0Box :=
  sound_of_literal_split component65Node0Box leaf3093Box leaf3094Box
    .k (233/64) (by rfl) (by rfl)
    leaf3093FlatSound leaf3094FlatSound

private noncomputable def component65Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (49/256), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component65Node1_sound : Sound component65Node1Box :=
  sound_of_literal_split component65Node1Box leaf3095Box leaf3096Box
    .k (233/64) (by rfl) (by rfl)
    leaf3095FlatSound leaf3096FlatSound

private noncomputable def component65Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (3/16), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component65Node2_sound : Sound component65Node2Box :=
  sound_of_literal_split component65Node2Box component65Node0Box component65Node1Box
    .chi (49/256) (by rfl) (by rfl)
    component65Node0_sound component65Node1_sound

private noncomputable def component65Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (3/16), chiHi := (49/256) }

set_option maxRecDepth 1000000 in
private theorem component65Node3_sound : Sound component65Node3Box :=
  sound_of_literal_split component65Node3Box leaf3097Box leaf3098Box
    .k (235/64) (by rfl) (by rfl)
    leaf3097FlatSound leaf3098FlatSound

private noncomputable def component65Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (49/256), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component65Node4_sound : Sound component65Node4Box :=
  sound_of_literal_split component65Node4Box leaf3099Box leaf3100Box
    .k (235/64) (by rfl) (by rfl)
    leaf3099FlatSound leaf3100FlatSound

private noncomputable def component65Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (3/16), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component65Node5_sound : Sound component65Node5Box :=
  sound_of_literal_split component65Node5Box component65Node3Box component65Node4Box
    .chi (49/256) (by rfl) (by rfl)
    component65Node3_sound component65Node4_sound

private noncomputable def component65Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (3/16), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component65Node6_sound : Sound component65Node6Box :=
  sound_of_literal_split component65Node6Box component65Node2Box component65Node5Box
    .k (117/32) (by rfl) (by rfl)
    component65Node2_sound component65Node5_sound

private noncomputable def component65Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (25/128), chiHi := (51/256) }

set_option maxRecDepth 1000000 in
private theorem component65Node7_sound : Sound component65Node7Box :=
  sound_of_literal_split component65Node7Box leaf3101Box leaf3102Box
    .k (233/64) (by rfl) (by rfl)
    leaf3101FlatSound leaf3102FlatSound

private noncomputable def component65Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (51/256), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component65Node8_sound : Sound component65Node8Box :=
  sound_of_literal_split component65Node8Box leaf3103Box leaf3104Box
    .k (233/64) (by rfl) (by rfl)
    leaf3103FlatSound leaf3104FlatSound

private noncomputable def component65Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component65Node9_sound : Sound component65Node9Box :=
  sound_of_literal_split component65Node9Box component65Node7Box component65Node8Box
    .chi (51/256) (by rfl) (by rfl)
    component65Node7_sound component65Node8_sound

private noncomputable def component65Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (25/128), chiHi := (51/256) }

set_option maxRecDepth 1000000 in
private theorem component65Node10_sound : Sound component65Node10Box :=
  sound_of_literal_split component65Node10Box leaf3105Box leaf3106Box
    .k (235/64) (by rfl) (by rfl)
    leaf3105FlatSound leaf3106FlatSound

private noncomputable def component65Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (51/256), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component65Node11_sound : Sound component65Node11Box :=
  sound_of_literal_split component65Node11Box leaf3107Box leaf3108Box
    .k (235/64) (by rfl) (by rfl)
    leaf3107FlatSound leaf3108FlatSound

private noncomputable def component65Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component65Node12_sound : Sound component65Node12Box :=
  sound_of_literal_split component65Node12Box component65Node10Box component65Node11Box
    .chi (51/256) (by rfl) (by rfl)
    component65Node10_sound component65Node11_sound

private noncomputable def component65Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component65Node13_sound : Sound component65Node13Box :=
  sound_of_literal_split component65Node13Box component65Node9Box component65Node12Box
    .k (117/32) (by rfl) (by rfl)
    component65Node9_sound component65Node12_sound

private noncomputable def component65Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component65Node14_sound : Sound component65Node14Box :=
  sound_of_literal_split component65Node14Box component65Node6Box component65Node13Box
    .chi (25/128) (by rfl) (by rfl)
    component65Node6_sound component65Node13_sound

private noncomputable def component65Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (3/16), chiHi := (49/256) }

set_option maxRecDepth 1000000 in
private theorem component65Node15_sound : Sound component65Node15Box :=
  sound_of_literal_split component65Node15Box leaf3109Box leaf3110Box
    .k (237/64) (by rfl) (by rfl)
    leaf3109FlatSound leaf3110FlatSound

private noncomputable def component65Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (49/256), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component65Node16_sound : Sound component65Node16Box :=
  sound_of_literal_split component65Node16Box leaf3111Box leaf3112Box
    .k (237/64) (by rfl) (by rfl)
    leaf3111FlatSound leaf3112FlatSound

private noncomputable def component65Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (3/16), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component65Node17_sound : Sound component65Node17Box :=
  sound_of_literal_split component65Node17Box component65Node15Box component65Node16Box
    .chi (49/256) (by rfl) (by rfl)
    component65Node15_sound component65Node16_sound

private noncomputable def component65Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (3/16), chiHi := (49/256) }

set_option maxRecDepth 1000000 in
private theorem component65Node18_sound : Sound component65Node18Box :=
  sound_of_literal_split component65Node18Box leaf3113Box leaf3114Box
    .k (239/64) (by rfl) (by rfl)
    leaf3113FlatSound leaf3114FlatSound

private noncomputable def component65Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (49/256), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component65Node19_sound : Sound component65Node19Box :=
  sound_of_literal_split component65Node19Box leaf3115Box leaf3116Box
    .k (239/64) (by rfl) (by rfl)
    leaf3115FlatSound leaf3116FlatSound

private noncomputable def component65Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (3/16), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component65Node20_sound : Sound component65Node20Box :=
  sound_of_literal_split component65Node20Box component65Node18Box component65Node19Box
    .chi (49/256) (by rfl) (by rfl)
    component65Node18_sound component65Node19_sound

private noncomputable def component65Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (3/16), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component65Node21_sound : Sound component65Node21Box :=
  sound_of_literal_split component65Node21Box component65Node17Box component65Node20Box
    .k (119/32) (by rfl) (by rfl)
    component65Node17_sound component65Node20_sound

private noncomputable def component65Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (25/128), chiHi := (51/256) }

set_option maxRecDepth 1000000 in
private theorem component65Node22_sound : Sound component65Node22Box :=
  sound_of_literal_split component65Node22Box leaf3117Box leaf3118Box
    .k (237/64) (by rfl) (by rfl)
    leaf3117FlatSound leaf3118FlatSound

private noncomputable def component65Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (51/256), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component65Node23_sound : Sound component65Node23Box :=
  sound_of_literal_split component65Node23Box leaf3119Box leaf3120Box
    .k (237/64) (by rfl) (by rfl)
    leaf3119FlatSound leaf3120FlatSound

private noncomputable def component65Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component65Node24_sound : Sound component65Node24Box :=
  sound_of_literal_split component65Node24Box component65Node22Box component65Node23Box
    .chi (51/256) (by rfl) (by rfl)
    component65Node22_sound component65Node23_sound

private noncomputable def component65Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (25/128), chiHi := (51/256) }

set_option maxRecDepth 1000000 in
private theorem component65Node25_sound : Sound component65Node25Box :=
  sound_of_literal_split component65Node25Box leaf3121Box leaf3122Box
    .k (239/64) (by rfl) (by rfl)
    leaf3121FlatSound leaf3122FlatSound

private noncomputable def component65Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (51/256), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component65Node26_sound : Sound component65Node26Box :=
  sound_of_literal_split component65Node26Box leaf3123Box leaf3124Box
    .k (239/64) (by rfl) (by rfl)
    leaf3123FlatSound leaf3124FlatSound

private noncomputable def component65Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component65Node27_sound : Sound component65Node27Box :=
  sound_of_literal_split component65Node27Box component65Node25Box component65Node26Box
    .chi (51/256) (by rfl) (by rfl)
    component65Node25_sound component65Node26_sound

private noncomputable def component65Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component65Node28_sound : Sound component65Node28Box :=
  sound_of_literal_split component65Node28Box component65Node24Box component65Node27Box
    .k (119/32) (by rfl) (by rfl)
    component65Node24_sound component65Node27_sound

private noncomputable def component65Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component65Node29_sound : Sound component65Node29Box :=
  sound_of_literal_split component65Node29Box component65Node21Box component65Node28Box
    .chi (25/128) (by rfl) (by rfl)
    component65Node21_sound component65Node28_sound

private noncomputable def component65Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component65Node30_sound : Sound component65Node30Box :=
  sound_of_literal_split component65Node30Box component65Node14Box component65Node29Box
    .k (59/16) (by rfl) (by rfl)
    component65Node14_sound component65Node29_sound

private noncomputable def component65Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (13/64), chiHi := (53/256) }

set_option maxRecDepth 1000000 in
private theorem component65Node31_sound : Sound component65Node31Box :=
  sound_of_literal_split component65Node31Box leaf3125Box leaf3126Box
    .k (233/64) (by rfl) (by rfl)
    leaf3125FlatSound leaf3126FlatSound

private noncomputable def component65Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (53/256), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component65Node32_sound : Sound component65Node32Box :=
  sound_of_literal_split component65Node32Box leaf3127Box leaf3128Box
    .k (233/64) (by rfl) (by rfl)
    leaf3127FlatSound leaf3128FlatSound

private noncomputable def component65Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component65Node33_sound : Sound component65Node33Box :=
  sound_of_literal_split component65Node33Box component65Node31Box component65Node32Box
    .chi (53/256) (by rfl) (by rfl)
    component65Node31_sound component65Node32_sound

private noncomputable def component65Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (13/64), chiHi := (53/256) }

set_option maxRecDepth 1000000 in
private theorem component65Node34_sound : Sound component65Node34Box :=
  sound_of_literal_split component65Node34Box leaf3129Box leaf3130Box
    .k (235/64) (by rfl) (by rfl)
    leaf3129FlatSound leaf3130FlatSound

private noncomputable def component65Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (53/256), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component65Node35_sound : Sound component65Node35Box :=
  sound_of_literal_split component65Node35Box leaf3131Box leaf3132Box
    .k (235/64) (by rfl) (by rfl)
    leaf3131FlatSound leaf3132FlatSound

private noncomputable def component65Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component65Node36_sound : Sound component65Node36Box :=
  sound_of_literal_split component65Node36Box component65Node34Box component65Node35Box
    .chi (53/256) (by rfl) (by rfl)
    component65Node34_sound component65Node35_sound

private noncomputable def component65Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component65Node37_sound : Sound component65Node37Box :=
  sound_of_literal_split component65Node37Box component65Node33Box component65Node36Box
    .k (117/32) (by rfl) (by rfl)
    component65Node33_sound component65Node36_sound

private noncomputable def component65Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (27/128), chiHi := (55/256) }

set_option maxRecDepth 1000000 in
private theorem component65Node38_sound : Sound component65Node38Box :=
  sound_of_literal_split component65Node38Box leaf3133Box leaf3134Box
    .k (233/64) (by rfl) (by rfl)
    leaf3133FlatSound leaf3134FlatSound

private noncomputable def component65Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (55/256), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component65Node39_sound : Sound component65Node39Box :=
  sound_of_literal_split component65Node39Box leaf3135Box leaf3136Box
    .k (233/64) (by rfl) (by rfl)
    leaf3135FlatSound leaf3136FlatSound

private noncomputable def component65Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (27/128), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component65Node40_sound : Sound component65Node40Box :=
  sound_of_literal_split component65Node40Box component65Node38Box component65Node39Box
    .chi (55/256) (by rfl) (by rfl)
    component65Node38_sound component65Node39_sound

private noncomputable def component65Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (27/128), chiHi := (55/256) }

set_option maxRecDepth 1000000 in
private theorem component65Node41_sound : Sound component65Node41Box :=
  sound_of_literal_split component65Node41Box leaf3137Box leaf3138Box
    .k (235/64) (by rfl) (by rfl)
    leaf3137FlatSound leaf3138FlatSound

private noncomputable def component65Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (55/256), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component65Node42_sound : Sound component65Node42Box :=
  sound_of_literal_split component65Node42Box leaf3139Box leaf3140Box
    .k (235/64) (by rfl) (by rfl)
    leaf3139FlatSound leaf3140FlatSound

private noncomputable def component65Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (27/128), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component65Node43_sound : Sound component65Node43Box :=
  sound_of_literal_split component65Node43Box component65Node41Box component65Node42Box
    .chi (55/256) (by rfl) (by rfl)
    component65Node41_sound component65Node42_sound

private noncomputable def component65Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (27/128), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component65Node44_sound : Sound component65Node44Box :=
  sound_of_literal_split component65Node44Box component65Node40Box component65Node43Box
    .k (117/32) (by rfl) (by rfl)
    component65Node40_sound component65Node43_sound

private noncomputable def component65Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component65Node45_sound : Sound component65Node45Box :=
  sound_of_literal_split component65Node45Box component65Node37Box component65Node44Box
    .chi (27/128) (by rfl) (by rfl)
    component65Node37_sound component65Node44_sound

private noncomputable def component65Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (13/64), chiHi := (53/256) }

set_option maxRecDepth 1000000 in
private theorem component65Node46_sound : Sound component65Node46Box :=
  sound_of_literal_split component65Node46Box leaf3141Box leaf3142Box
    .k (237/64) (by rfl) (by rfl)
    leaf3141FlatSound leaf3142FlatSound

private noncomputable def component65Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (53/256), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component65Node47_sound : Sound component65Node47Box :=
  sound_of_literal_split component65Node47Box leaf3143Box leaf3144Box
    .k (237/64) (by rfl) (by rfl)
    leaf3143FlatSound leaf3144FlatSound

private noncomputable def component65Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component65Node48_sound : Sound component65Node48Box :=
  sound_of_literal_split component65Node48Box component65Node46Box component65Node47Box
    .chi (53/256) (by rfl) (by rfl)
    component65Node46_sound component65Node47_sound

private noncomputable def component65Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (13/64), chiHi := (53/256) }

set_option maxRecDepth 1000000 in
private theorem component65Node49_sound : Sound component65Node49Box :=
  sound_of_literal_split component65Node49Box leaf3145Box leaf3146Box
    .k (239/64) (by rfl) (by rfl)
    leaf3145FlatSound leaf3146FlatSound

private noncomputable def component65Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (53/256), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component65Node50_sound : Sound component65Node50Box :=
  sound_of_literal_split component65Node50Box leaf3147Box leaf3148Box
    .k (239/64) (by rfl) (by rfl)
    leaf3147FlatSound leaf3148FlatSound

private noncomputable def component65Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component65Node51_sound : Sound component65Node51Box :=
  sound_of_literal_split component65Node51Box component65Node49Box component65Node50Box
    .chi (53/256) (by rfl) (by rfl)
    component65Node49_sound component65Node50_sound

private noncomputable def component65Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component65Node52_sound : Sound component65Node52Box :=
  sound_of_literal_split component65Node52Box component65Node48Box component65Node51Box
    .k (119/32) (by rfl) (by rfl)
    component65Node48_sound component65Node51_sound

private noncomputable def component65Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (27/128), chiHi := (55/256) }

set_option maxRecDepth 1000000 in
private theorem component65Node53_sound : Sound component65Node53Box :=
  sound_of_literal_split component65Node53Box leaf3149Box leaf3150Box
    .k (237/64) (by rfl) (by rfl)
    leaf3149FlatSound leaf3150FlatSound

private noncomputable def component65Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (55/256), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component65Node54_sound : Sound component65Node54Box :=
  sound_of_literal_split component65Node54Box leaf3151Box leaf3152Box
    .k (237/64) (by rfl) (by rfl)
    leaf3151FlatSound leaf3152FlatSound

private noncomputable def component65Node55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (27/128), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component65Node55_sound : Sound component65Node55Box :=
  sound_of_literal_split component65Node55Box component65Node53Box component65Node54Box
    .chi (55/256) (by rfl) (by rfl)
    component65Node53_sound component65Node54_sound

private noncomputable def component65Node56Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (27/128), chiHi := (55/256) }

set_option maxRecDepth 1000000 in
private theorem component65Node56_sound : Sound component65Node56Box :=
  sound_of_literal_split component65Node56Box leaf3153Box leaf3154Box
    .k (239/64) (by rfl) (by rfl)
    leaf3153FlatSound leaf3154FlatSound

private noncomputable def component65Node57Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (55/256), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component65Node57_sound : Sound component65Node57Box :=
  sound_of_literal_split component65Node57Box leaf3155Box leaf3156Box
    .k (239/64) (by rfl) (by rfl)
    leaf3155FlatSound leaf3156FlatSound

private noncomputable def component65Node58Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (27/128), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component65Node58_sound : Sound component65Node58Box :=
  sound_of_literal_split component65Node58Box component65Node56Box component65Node57Box
    .chi (55/256) (by rfl) (by rfl)
    component65Node56_sound component65Node57_sound

private noncomputable def component65Node59Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (27/128), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component65Node59_sound : Sound component65Node59Box :=
  sound_of_literal_split component65Node59Box component65Node55Box component65Node58Box
    .k (119/32) (by rfl) (by rfl)
    component65Node55_sound component65Node58_sound

private noncomputable def component65Node60Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component65Node60_sound : Sound component65Node60Box :=
  sound_of_literal_split component65Node60Box component65Node52Box component65Node59Box
    .chi (27/128) (by rfl) (by rfl)
    component65Node52_sound component65Node59_sound

private noncomputable def component65Node61Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component65Node61_sound : Sound component65Node61Box :=
  sound_of_literal_split component65Node61Box component65Node45Box component65Node60Box
    .k (59/16) (by rfl) (by rfl)
    component65Node45_sound component65Node60_sound

noncomputable def component65Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (3/16), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
theorem component65_sound : Sound component65Box :=
  sound_of_literal_split component65Box component65Node30Box component65Node61Box
    .chi (13/64) (by rfl) (by rfl)
    component65Node30_sound component65Node61_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
