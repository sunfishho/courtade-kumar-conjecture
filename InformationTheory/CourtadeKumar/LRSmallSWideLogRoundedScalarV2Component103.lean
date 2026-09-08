import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch8
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch9
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

private noncomputable def leaf5055Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (249/64), chiLo := (1/4), chiHi := (65/256) }

private noncomputable def leaf5055Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742451/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430666752) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2113832335/1073741824) }, upper := { exponent := 0, mantissa := (32569/16384) } }, logOuter := sk233LogOuterCertificate, logK := sk233LogKCertificate, logChi := chi277LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867588607/274861333504) } }, logDArg := sk233LogDArgCertificate }

private noncomputable def leaf5055InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf5055LocalValidity :
    LeafFacts leaf5055Box leaf5055Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5055Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430666752) }) = true
      norm_num [leaf5055Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5055CertificateValid :
    WideCertificateValid leaf5055Box leaf5055Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk233ValidityFacts chi277ValidityFacts
    leaf5055LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5055CoverageChecked :
    coverageCheck (innerAD leaf5055Box) leaf5055InnerLog = true := by
  rfl'

private theorem leaf5055InnerLogValid :
    leaf5055InnerLog.Valid 8 (innerAD leaf5055Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf5055CoverageChecked

private noncomputable def leaf5055InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629463/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5055InputLogOnePlusV_eq :
    leaf5055InputLogOnePlusV = outerEnclosure 24
      (leaf5055Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5055RoundedFacts : LeafRoundedFacts 8
    leaf5055Certificate.logOnePlusV leaf5055InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5055InputLogOnePlusV_eq }

private noncomputable def leaf5055Inputs : Inputs :=
  inputsOfCaches globalInput sk233RoundedInputs
    chi277InputQChi innerPair108Input
    leaf5055InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5055LowerChecked :
    lowerCheck 24 leaf5055Box leaf5055Inputs = true := by
  rfl'

private theorem leaf5055CoversExact : CoversExact 8
    leaf5055Box leaf5055Certificate leaf5055InnerLog leaf5055Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk233RoundedFacts chi277RoundedFacts
    innerPair108RoundedFacts leaf5055RoundedFacts (by rfl)

private theorem leaf5055FlatSound : Sound leaf5055Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5055CertificateValid
    leaf5055InnerLogValid leaf5055CoversExact leaf5055LowerChecked

private noncomputable def leaf5056Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (249/64), kHi := (125/32), chiLo := (1/4), chiHi := (65/256) }

private noncomputable def leaf5056Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742453/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430633472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2118026381/1073741824) }, upper := { exponent := 0, mantissa := (16317/8192) } }, logOuter := sk234LogOuterCertificate, logK := sk234LogKCertificate, logChi := chi277LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867555327/274861266944) } }, logDArg := sk234LogDArgCertificate }

private noncomputable def leaf5056InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf5056LocalValidity :
    LeafFacts leaf5056Box leaf5056Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5056Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430633472) }) = true
      norm_num [leaf5056Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5056CertificateValid :
    WideCertificateValid leaf5056Box leaf5056Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk234ValidityFacts chi277ValidityFacts
    leaf5056LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5056CoverageChecked :
    coverageCheck (innerAD leaf5056Box) leaf5056InnerLog = true := by
  rfl'

private theorem leaf5056InnerLogValid :
    leaf5056InnerLog.Valid 8 (innerAD leaf5056Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf5056CoverageChecked

private noncomputable def leaf5056InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629465/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5056InputLogOnePlusV_eq :
    leaf5056InputLogOnePlusV = outerEnclosure 24
      (leaf5056Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5056RoundedFacts : LeafRoundedFacts 8
    leaf5056Certificate.logOnePlusV leaf5056InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5056InputLogOnePlusV_eq }

private noncomputable def leaf5056Inputs : Inputs :=
  inputsOfCaches globalInput sk234RoundedInputs
    chi277InputQChi innerPair108Input
    leaf5056InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5056LowerChecked :
    lowerCheck 24 leaf5056Box leaf5056Inputs = true := by
  rfl'

private theorem leaf5056CoversExact : CoversExact 8
    leaf5056Box leaf5056Certificate leaf5056InnerLog leaf5056Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk234RoundedFacts chi277RoundedFacts
    innerPair108RoundedFacts leaf5056RoundedFacts (by rfl)

private theorem leaf5056FlatSound : Sound leaf5056Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5056CertificateValid
    leaf5056InnerLogValid leaf5056CoversExact leaf5056LowerChecked

private noncomputable def leaf5057Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (249/64), chiLo := (65/256), chiHi := (33/128) }

private noncomputable def leaf5057Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742453/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715269632) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2130084269/1073741824) }, upper := { exponent := 1, mantissa := (16409/16384) } }, logOuter := sk233LogOuterCertificate, logK := sk233LogKCertificate, logChi := chi278LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432681983/137430539264) } }, logDArg := sk233LogDArgCertificate }

private noncomputable def leaf5057InnerLog : WideLogData :=
  innerPair321Data

set_option maxRecDepth 1000000 in
private theorem leaf5057LocalValidity :
    LeafFacts leaf5057Box leaf5057Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5057Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715269632) }) = true
      norm_num [leaf5057Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5057CertificateValid :
    WideCertificateValid leaf5057Box leaf5057Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk233ValidityFacts chi278ValidityFacts
    leaf5057LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5057CoverageChecked :
    coverageCheck (innerAD leaf5057Box) leaf5057InnerLog = true := by
  rfl'

private theorem leaf5057InnerLogValid :
    leaf5057InnerLog.Valid 8 (innerAD leaf5057Box) :=
  wideLogDataValid_of_cachedCheck endpoint85PositiveFacts
    endpoint283PositiveFacts.valid leaf5057CoverageChecked

private noncomputable def leaf5057InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814671/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5057InputLogOnePlusV_eq :
    leaf5057InputLogOnePlusV = outerEnclosure 24
      (leaf5057Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5057RoundedFacts : LeafRoundedFacts 8
    leaf5057Certificate.logOnePlusV leaf5057InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5057InputLogOnePlusV_eq }

private noncomputable def leaf5057Inputs : Inputs :=
  inputsOfCaches globalInput sk233RoundedInputs
    chi278InputQChi innerPair321Input
    leaf5057InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5057LowerChecked :
    lowerCheck 24 leaf5057Box leaf5057Inputs = true := by
  rfl'

private theorem leaf5057CoversExact : CoversExact 8
    leaf5057Box leaf5057Certificate leaf5057InnerLog leaf5057Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk233RoundedFacts chi278RoundedFacts
    innerPair321RoundedFacts leaf5057RoundedFacts (by rfl)

private theorem leaf5057FlatSound : Sound leaf5057Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5057CertificateValid
    leaf5057InnerLogValid leaf5057CoversExact leaf5057LowerChecked

private noncomputable def leaf5058Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (249/64), kHi := (125/32), chiLo := (65/256), chiHi := (33/128) }

private noncomputable def leaf5058Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742455/1073741824) }, vSqrt := { lower := (8191/8192), upper := (2216690721/2216621056) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2134343847/1073741824) }, upper := { exponent := 1, mantissa := (8221/8192) } }, logOuter := sk234LogOuterCertificate, logK := sk234LogKCertificate, logChi := chi278LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (4433311777/4433242112) } }, logDArg := sk234LogDArgCertificate }

private noncomputable def leaf5058InnerLog : WideLogData :=
  innerPair533Data

set_option maxRecDepth 1000000 in
private theorem leaf5058LocalValidity :
    LeafFacts leaf5058Box leaf5058Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5058Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (2216690721/2216621056) }) = true
      norm_num [leaf5058Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5058CertificateValid :
    WideCertificateValid leaf5058Box leaf5058Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk234ValidityFacts chi278ValidityFacts
    leaf5058LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5058CoverageChecked :
    coverageCheck (innerAD leaf5058Box) leaf5058InnerLog = true := by
  rfl'

private theorem leaf5058InnerLogValid :
    leaf5058InnerLog.Valid 8 (innerAD leaf5058Box) :=
  wideLogDataValid_of_cachedCheck endpoint267PositiveFacts
    endpoint283PositiveFacts.valid leaf5058CoverageChecked

private noncomputable def leaf5058InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (363417/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf5058InputLogOnePlusV_eq :
    leaf5058InputLogOnePlusV = outerEnclosure 24
      (leaf5058Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5058RoundedFacts : LeafRoundedFacts 8
    leaf5058Certificate.logOnePlusV leaf5058InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5058InputLogOnePlusV_eq }

private noncomputable def leaf5058Inputs : Inputs :=
  inputsOfCaches globalInput sk234RoundedInputs
    chi278InputQChi innerPair533Input
    leaf5058InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5058LowerChecked :
    lowerCheck 24 leaf5058Box leaf5058Inputs = true := by
  rfl'

private theorem leaf5058CoversExact : CoversExact 8
    leaf5058Box leaf5058Certificate leaf5058InnerLog leaf5058Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk234RoundedFacts chi278RoundedFacts
    innerPair533RoundedFacts leaf5058RoundedFacts (by rfl)

private theorem leaf5058FlatSound : Sound leaf5058Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5058CertificateValid
    leaf5058InnerLogValid leaf5058CoversExact leaf5058LowerChecked

private noncomputable def leaf5059Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (251/64), chiLo := (1/4), chiHi := (65/256) }

private noncomputable def leaf5059Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742455/1073741824) }, vSqrt := { lower := (8191/8192), upper := (7635268039/7635033344) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2122220427/1073741824) }, upper := { exponent := 0, mantissa := (32699/16384) } }, logOuter := sk235LogOuterCertificate, logK := sk235LogKCertificate, logChi := chi277LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (15270301383/15270066688) } }, logDArg := sk235LogDArgCertificate }

private noncomputable def leaf5059InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf5059LocalValidity :
    LeafFacts leaf5059Box leaf5059Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5059Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (7635268039/7635033344) }) = true
      norm_num [leaf5059Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5059CertificateValid :
    WideCertificateValid leaf5059Box leaf5059Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk235ValidityFacts chi277ValidityFacts
    leaf5059LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5059CoverageChecked :
    coverageCheck (innerAD leaf5059Box) leaf5059InnerLog = true := by
  rfl'

private theorem leaf5059InnerLogValid :
    leaf5059InnerLog.Valid 8 (innerAD leaf5059Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf5059CoverageChecked

private noncomputable def leaf5059InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629339/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5059InputLogOnePlusV_eq :
    leaf5059InputLogOnePlusV = outerEnclosure 24
      (leaf5059Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5059RoundedFacts : LeafRoundedFacts 8
    leaf5059Certificate.logOnePlusV leaf5059InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5059InputLogOnePlusV_eq }

private noncomputable def leaf5059Inputs : Inputs :=
  inputsOfCaches globalInput sk235RoundedInputs
    chi277InputQChi innerPair108Input
    leaf5059InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5059LowerChecked :
    lowerCheck 24 leaf5059Box leaf5059Inputs = true := by
  rfl'

private theorem leaf5059CoversExact : CoversExact 8
    leaf5059Box leaf5059Certificate leaf5059InnerLog leaf5059Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk235RoundedFacts chi277RoundedFacts
    innerPair108RoundedFacts leaf5059RoundedFacts (by rfl)

private theorem leaf5059FlatSound : Sound leaf5059Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5059CertificateValid
    leaf5059InnerLogValid leaf5059CoversExact leaf5059LowerChecked

private noncomputable def leaf5060Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (1/4), chiHi := (65/256) }

private noncomputable def leaf5060Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742457/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715283456) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2126414473/1073741824) }, upper := { exponent := 0, mantissa := (8191/4096) } }, logOuter := sk236LogOuterCertificate, logK := sk236LogKCertificate, logChi := chi277LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432695807/137430566912) } }, logDArg := sk236LogDArgCertificate }

private noncomputable def leaf5060InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf5060LocalValidity :
    LeafFacts leaf5060Box leaf5060Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5060Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715283456) }) = true
      norm_num [leaf5060Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5060CertificateValid :
    WideCertificateValid leaf5060Box leaf5060Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk236ValidityFacts chi277ValidityFacts
    leaf5060LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5060CoverageChecked :
    coverageCheck (innerAD leaf5060Box) leaf5060InnerLog = true := by
  rfl'

private theorem leaf5060InnerLogValid :
    leaf5060InnerLog.Valid 8 (innerAD leaf5060Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf5060CoverageChecked

private noncomputable def leaf5060InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629341/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5060InputLogOnePlusV_eq :
    leaf5060InputLogOnePlusV = outerEnclosure 24
      (leaf5060Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5060RoundedFacts : LeafRoundedFacts 8
    leaf5060Certificate.logOnePlusV leaf5060InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5060InputLogOnePlusV_eq }

private noncomputable def leaf5060Inputs : Inputs :=
  inputsOfCaches globalInput sk236RoundedInputs
    chi277InputQChi innerPair108Input
    leaf5060InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5060LowerChecked :
    lowerCheck 24 leaf5060Box leaf5060Inputs = true := by
  rfl'

private theorem leaf5060CoversExact : CoversExact 8
    leaf5060Box leaf5060Certificate leaf5060InnerLog leaf5060Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk236RoundedFacts chi277RoundedFacts
    innerPair108RoundedFacts leaf5060RoundedFacts (by rfl)

private theorem leaf5060FlatSound : Sound leaf5060Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5060CertificateValid
    leaf5060InnerLogValid leaf5060CoversExact leaf5060LowerChecked

private noncomputable def leaf5061Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (251/64), chiLo := (65/256), chiHi := (33/128) }

private noncomputable def leaf5061Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742457/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715235840) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2138603425/1073741824) }, upper := { exponent := 1, mantissa := (16475/16384) } }, logOuter := sk235LogOuterCertificate, logK := sk235LogKCertificate, logChi := chi278LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432648191/137430471680) } }, logDArg := sk235LogDArgCertificate }

private noncomputable def leaf5061InnerLog : WideLogData :=
  innerPair533Data

set_option maxRecDepth 1000000 in
private theorem leaf5061LocalValidity :
    LeafFacts leaf5061Box leaf5061Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5061Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715235840) }) = true
      norm_num [leaf5061Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5061CertificateValid :
    WideCertificateValid leaf5061Box leaf5061Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk235ValidityFacts chi278ValidityFacts
    leaf5061LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5061CoverageChecked :
    coverageCheck (innerAD leaf5061Box) leaf5061InnerLog = true := by
  rfl'

private theorem leaf5061InnerLogValid :
    leaf5061InnerLog.Valid 8 (innerAD leaf5061Box) :=
  wideLogDataValid_of_cachedCheck endpoint267PositiveFacts
    endpoint283PositiveFacts.valid leaf5061CoverageChecked

private noncomputable def leaf5061InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814673/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5061InputLogOnePlusV_eq :
    leaf5061InputLogOnePlusV = outerEnclosure 24
      (leaf5061Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5061RoundedFacts : LeafRoundedFacts 8
    leaf5061Certificate.logOnePlusV leaf5061InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5061InputLogOnePlusV_eq }

private noncomputable def leaf5061Inputs : Inputs :=
  inputsOfCaches globalInput sk235RoundedInputs
    chi278InputQChi innerPair533Input
    leaf5061InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5061LowerChecked :
    lowerCheck 24 leaf5061Box leaf5061Inputs = true := by
  rfl'

private theorem leaf5061CoversExact : CoversExact 8
    leaf5061Box leaf5061Certificate leaf5061InnerLog leaf5061Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk235RoundedFacts chi278RoundedFacts
    innerPair533RoundedFacts leaf5061RoundedFacts (by rfl)

private theorem leaf5061FlatSound : Sound leaf5061Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5061CertificateValid
    leaf5061InnerLogValid leaf5061CoversExact leaf5061LowerChecked

private noncomputable def leaf5062Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (65/256), chiHi := (33/128) }

private noncomputable def leaf5062Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742459/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715218944) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2142863003/1073741824) }, upper := { exponent := 1, mantissa := (4127/4096) } }, logOuter := sk236LogOuterCertificate, logK := sk236LogKCertificate, logChi := chi278LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432631295/137430437888) } }, logDArg := sk236LogDArgCertificate }

private noncomputable def leaf5062InnerLog : WideLogData :=
  innerPair533Data

set_option maxRecDepth 1000000 in
private theorem leaf5062LocalValidity :
    LeafFacts leaf5062Box leaf5062Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5062Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715218944) }) = true
      norm_num [leaf5062Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5062CertificateValid :
    WideCertificateValid leaf5062Box leaf5062Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk236ValidityFacts chi278ValidityFacts
    leaf5062LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5062CoverageChecked :
    coverageCheck (innerAD leaf5062Box) leaf5062InnerLog = true := by
  rfl'

private theorem leaf5062InnerLogValid :
    leaf5062InnerLog.Valid 8 (innerAD leaf5062Box) :=
  wideLogDataValid_of_cachedCheck endpoint267PositiveFacts
    endpoint283PositiveFacts.valid leaf5062CoverageChecked

private noncomputable def leaf5062InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629349/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5062InputLogOnePlusV_eq :
    leaf5062InputLogOnePlusV = outerEnclosure 24
      (leaf5062Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5062RoundedFacts : LeafRoundedFacts 8
    leaf5062Certificate.logOnePlusV leaf5062InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5062InputLogOnePlusV_eq }

private noncomputable def leaf5062Inputs : Inputs :=
  inputsOfCaches globalInput sk236RoundedInputs
    chi278InputQChi innerPair533Input
    leaf5062InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5062LowerChecked :
    lowerCheck 24 leaf5062Box leaf5062Inputs = true := by
  rfl'

private theorem leaf5062CoversExact : CoversExact 8
    leaf5062Box leaf5062Certificate leaf5062InnerLog leaf5062Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk236RoundedFacts chi278RoundedFacts
    innerPair533RoundedFacts leaf5062RoundedFacts (by rfl)

private theorem leaf5062FlatSound : Sound leaf5062Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5062CertificateValid
    leaf5062InnerLogValid leaf5062CoversExact leaf5062LowerChecked

private noncomputable def leaf5063Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (249/64), chiLo := (33/128), chiHi := (67/256) }

private noncomputable def leaf5063Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742455/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9816773193/9816457984) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2146336203/1073741824) }, upper := { exponent := 1, mantissa := (33067/32768) } }, logOuter := sk233LogOuterCertificate, logK := sk233LogKCertificate, logChi := chi275LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (19633231177/19632915968) } }, logDArg := sk233LogDArgCertificate }

private noncomputable def leaf5063InnerLog : WideLogData :=
  innerPair531Data

set_option maxRecDepth 1000000 in
private theorem leaf5063LocalValidity :
    LeafFacts leaf5063Box leaf5063Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5063Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9816773193/9816457984) }) = true
      norm_num [leaf5063Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5063CertificateValid :
    WideCertificateValid leaf5063Box leaf5063Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk233ValidityFacts chi275ValidityFacts
    leaf5063LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5063CoverageChecked :
    coverageCheck (innerAD leaf5063Box) leaf5063InnerLog = true := by
  rfl'

private theorem leaf5063InnerLogValid :
    leaf5063InnerLog.Valid 8 (innerAD leaf5063Box) :=
  wideLogDataValid_of_cachedCheck endpoint267PositiveFacts
    endpoint82PositiveFacts.valid leaf5063CoverageChecked

private noncomputable def leaf5063InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814675/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5063InputLogOnePlusV_eq :
    leaf5063InputLogOnePlusV = outerEnclosure 24
      (leaf5063Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5063RoundedFacts : LeafRoundedFacts 8
    leaf5063Certificate.logOnePlusV leaf5063InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5063InputLogOnePlusV_eq }

private noncomputable def leaf5063Inputs : Inputs :=
  inputsOfCaches globalInput sk233RoundedInputs
    chi275InputQChi innerPair531Input
    leaf5063InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5063LowerChecked :
    lowerCheck 24 leaf5063Box leaf5063Inputs = true := by
  rfl'

private theorem leaf5063CoversExact : CoversExact 8
    leaf5063Box leaf5063Certificate leaf5063InnerLog leaf5063Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk233RoundedFacts chi275RoundedFacts
    innerPair531RoundedFacts leaf5063RoundedFacts (by rfl)

private theorem leaf5063FlatSound : Sound leaf5063Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5063CertificateValid
    leaf5063InnerLogValid leaf5063CoversExact leaf5063LowerChecked

private noncomputable def leaf5064Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (249/64), kHi := (125/32), chiLo := (33/128), chiHi := (67/256) }

private noncomputable def leaf5064Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742457/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22905062912) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2150661313/2147483648) }, upper := { exponent := 1, mantissa := (16567/16384) } }, logOuter := sk234LogOuterCertificate, logK := sk234LogKCertificate, logChi := chi275LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810867029/45810125824) } }, logDArg := sk234LogDArgCertificate }

private noncomputable def leaf5064InnerLog : WideLogData :=
  innerPair119Data

set_option maxRecDepth 1000000 in
private theorem leaf5064LocalValidity :
    LeafFacts leaf5064Box leaf5064Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5064Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22905062912) }) = true
      norm_num [leaf5064Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5064CertificateValid :
    WideCertificateValid leaf5064Box leaf5064Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk234ValidityFacts chi275ValidityFacts
    leaf5064LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5064CoverageChecked :
    coverageCheck (innerAD leaf5064Box) leaf5064InnerLog = true := by
  rfl'

private theorem leaf5064InnerLogValid :
    leaf5064InnerLog.Valid 8 (innerAD leaf5064Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint82PositiveFacts.valid leaf5064CoverageChecked

private noncomputable def leaf5064InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453669/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5064InputLogOnePlusV_eq :
    leaf5064InputLogOnePlusV = outerEnclosure 24
      (leaf5064Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5064RoundedFacts : LeafRoundedFacts 8
    leaf5064Certificate.logOnePlusV leaf5064InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5064InputLogOnePlusV_eq }

private noncomputable def leaf5064Inputs : Inputs :=
  inputsOfCaches globalInput sk234RoundedInputs
    chi275InputQChi innerPair119Input
    leaf5064InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5064LowerChecked :
    lowerCheck 24 leaf5064Box leaf5064Inputs = true := by
  rfl'

private theorem leaf5064CoversExact : CoversExact 8
    leaf5064Box leaf5064Certificate leaf5064InnerLog leaf5064Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk234RoundedFacts chi275RoundedFacts
    innerPair119RoundedFacts leaf5064RoundedFacts (by rfl)

private theorem leaf5064FlatSound : Sound leaf5064Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5064CertificateValid
    leaf5064InnerLogValid leaf5064CoversExact leaf5064LowerChecked

private noncomputable def leaf5065Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (249/64), chiLo := (67/256), chiHi := (17/64) }

private noncomputable def leaf5065Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742457/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715142144) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2162588137/2147483648) }, upper := { exponent := 1, mantissa := (8329/8192) } }, logOuter := sk233LogOuterCertificate, logK := sk233LogKCertificate, logChi := chi276LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432554495/137430284288) } }, logDArg := sk233LogDArgCertificate }

private noncomputable def leaf5065InnerLog : WideLogData :=
  innerPair121Data

set_option maxRecDepth 1000000 in
private theorem leaf5065LocalValidity :
    LeafFacts leaf5065Box leaf5065Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5065Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715142144) }) = true
      norm_num [leaf5065Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5065CertificateValid :
    WideCertificateValid leaf5065Box leaf5065Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk233ValidityFacts chi276ValidityFacts
    leaf5065LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5065CoverageChecked :
    coverageCheck (innerAD leaf5065Box) leaf5065InnerLog = true := by
  rfl'

private theorem leaf5065InnerLogValid :
    leaf5065InnerLog.Valid 8 (innerAD leaf5065Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint87PositiveFacts.valid leaf5065CoverageChecked

private noncomputable def leaf5065InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814679/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5065InputLogOnePlusV_eq :
    leaf5065InputLogOnePlusV = outerEnclosure 24
      (leaf5065Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5065RoundedFacts : LeafRoundedFacts 8
    leaf5065Certificate.logOnePlusV leaf5065InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5065InputLogOnePlusV_eq }

private noncomputable def leaf5065Inputs : Inputs :=
  inputsOfCaches globalInput sk233RoundedInputs
    chi276InputQChi innerPair121Input
    leaf5065InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5065LowerChecked :
    lowerCheck 24 leaf5065Box leaf5065Inputs = true := by
  rfl'

private theorem leaf5065CoversExact : CoversExact 8
    leaf5065Box leaf5065Certificate leaf5065InnerLog leaf5065Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk233RoundedFacts chi276RoundedFacts
    innerPair121RoundedFacts leaf5065RoundedFacts (by rfl)

private theorem leaf5065FlatSound : Sound leaf5065Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5065CertificateValid
    leaf5065InnerLogValid leaf5065CoversExact leaf5065LowerChecked

private noncomputable def leaf5066Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (249/64), kHi := (125/32), chiLo := (67/256), chiHi := (17/64) }

private noncomputable def leaf5066Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742459/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715124736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2166978779/2147483648) }, upper := { exponent := 1, mantissa := (4173/4096) } }, logOuter := sk234LogOuterCertificate, logK := sk234LogKCertificate, logChi := chi276LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432537087/137430249472) } }, logDArg := sk234LogDArgCertificate }

private noncomputable def leaf5066InnerLog : WideLogData :=
  innerPair548Data

set_option maxRecDepth 1000000 in
private theorem leaf5066LocalValidity :
    LeafFacts leaf5066Box leaf5066Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5066Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715124736) }) = true
      norm_num [leaf5066Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5066CertificateValid :
    WideCertificateValid leaf5066Box leaf5066Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk234ValidityFacts chi276ValidityFacts
    leaf5066LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5066CoverageChecked :
    coverageCheck (innerAD leaf5066Box) leaf5066InnerLog = true := by
  rfl'

private theorem leaf5066InnerLogValid :
    leaf5066InnerLog.Valid 8 (innerAD leaf5066Box) :=
  wideLogDataValid_of_cachedCheck endpoint283PositiveFacts
    endpoint87PositiveFacts.valid leaf5066CoverageChecked

private noncomputable def leaf5066InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726835/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf5066InputLogOnePlusV_eq :
    leaf5066InputLogOnePlusV = outerEnclosure 24
      (leaf5066Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5066RoundedFacts : LeafRoundedFacts 8
    leaf5066Certificate.logOnePlusV leaf5066InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5066InputLogOnePlusV_eq }

private noncomputable def leaf5066Inputs : Inputs :=
  inputsOfCaches globalInput sk234RoundedInputs
    chi276InputQChi innerPair548Input
    leaf5066InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5066LowerChecked :
    lowerCheck 24 leaf5066Box leaf5066Inputs = true := by
  rfl'

private theorem leaf5066CoversExact : CoversExact 8
    leaf5066Box leaf5066Certificate leaf5066InnerLog leaf5066Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk234RoundedFacts chi276RoundedFacts
    innerPair548RoundedFacts leaf5066RoundedFacts (by rfl)

private theorem leaf5066FlatSound : Sound leaf5066Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5066CertificateValid
    leaf5066InnerLogValid leaf5066CoversExact leaf5066LowerChecked

private noncomputable def leaf5067Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (251/64), chiLo := (33/128), chiHi := (67/256) }

private noncomputable def leaf5067Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742459/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715171584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2154986423/2147483648) }, upper := { exponent := 1, mantissa := (33201/32768) } }, logOuter := sk235LogOuterCertificate, logK := sk235LogKCertificate, logChi := chi275LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432583935/137430343168) } }, logDArg := sk235LogDArgCertificate }

private noncomputable def leaf5067InnerLog : WideLogData :=
  innerPair119Data

set_option maxRecDepth 1000000 in
private theorem leaf5067LocalValidity :
    LeafFacts leaf5067Box leaf5067Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5067Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715171584) }) = true
      norm_num [leaf5067Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5067CertificateValid :
    WideCertificateValid leaf5067Box leaf5067Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk235ValidityFacts chi275ValidityFacts
    leaf5067LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5067CoverageChecked :
    coverageCheck (innerAD leaf5067Box) leaf5067InnerLog = true := by
  rfl'

private theorem leaf5067InnerLogValid :
    leaf5067InnerLog.Valid 8 (innerAD leaf5067Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint82PositiveFacts.valid leaf5067CoverageChecked

private noncomputable def leaf5067InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814677/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5067InputLogOnePlusV_eq :
    leaf5067InputLogOnePlusV = outerEnclosure 24
      (leaf5067Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5067RoundedFacts : LeafRoundedFacts 8
    leaf5067Certificate.logOnePlusV leaf5067InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5067InputLogOnePlusV_eq }

private noncomputable def leaf5067Inputs : Inputs :=
  inputsOfCaches globalInput sk235RoundedInputs
    chi275InputQChi innerPair119Input
    leaf5067InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5067LowerChecked :
    lowerCheck 24 leaf5067Box leaf5067Inputs = true := by
  rfl'

private theorem leaf5067CoversExact : CoversExact 8
    leaf5067Box leaf5067Certificate leaf5067InnerLog leaf5067Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk235RoundedFacts chi275RoundedFacts
    innerPair119RoundedFacts leaf5067RoundedFacts (by rfl)

private theorem leaf5067FlatSound : Sound leaf5067Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5067CertificateValid
    leaf5067InnerLogValid leaf5067CoversExact leaf5067LowerChecked

private noncomputable def leaf5068Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (33/128), chiHi := (67/256) }

private noncomputable def leaf5068Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742461/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715154432) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2159311533/2147483648) }, upper := { exponent := 1, mantissa := (8317/8192) } }, logOuter := sk236LogOuterCertificate, logK := sk236LogKCertificate, logChi := chi275LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432566783/137430308864) } }, logDArg := sk236LogDArgCertificate }

private noncomputable def leaf5068InnerLog : WideLogData :=
  innerPair119Data

set_option maxRecDepth 1000000 in
private theorem leaf5068LocalValidity :
    LeafFacts leaf5068Box leaf5068Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5068Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715154432) }) = true
      norm_num [leaf5068Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5068CertificateValid :
    WideCertificateValid leaf5068Box leaf5068Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk236ValidityFacts chi275ValidityFacts
    leaf5068LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5068CoverageChecked :
    coverageCheck (innerAD leaf5068Box) leaf5068InnerLog = true := by
  rfl'

private theorem leaf5068InnerLogValid :
    leaf5068InnerLog.Valid 8 (innerAD leaf5068Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint82PositiveFacts.valid leaf5068CoverageChecked

private noncomputable def leaf5068InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907339/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5068InputLogOnePlusV_eq :
    leaf5068InputLogOnePlusV = outerEnclosure 24
      (leaf5068Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5068RoundedFacts : LeafRoundedFacts 8
    leaf5068Certificate.logOnePlusV leaf5068InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5068InputLogOnePlusV_eq }

private noncomputable def leaf5068Inputs : Inputs :=
  inputsOfCaches globalInput sk236RoundedInputs
    chi275InputQChi innerPair119Input
    leaf5068InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5068LowerChecked :
    lowerCheck 24 leaf5068Box leaf5068Inputs = true := by
  rfl'

private theorem leaf5068CoversExact : CoversExact 8
    leaf5068Box leaf5068Certificate leaf5068InnerLog leaf5068Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk236RoundedFacts chi275RoundedFacts
    innerPair119RoundedFacts leaf5068RoundedFacts (by rfl)

private theorem leaf5068FlatSound : Sound leaf5068Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5068CertificateValid
    leaf5068InnerLogValid leaf5068CoversExact leaf5068LowerChecked

private noncomputable def leaf5069Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (251/64), chiLo := (67/256), chiHi := (17/64) }

private noncomputable def leaf5069Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742461/1073741824) }, vSqrt := { lower := (8191/8192), upper := (3272257731/3272147968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2171369421/2147483648) }, upper := { exponent := 1, mantissa := (8363/8192) } }, logOuter := sk235LogOuterCertificate, logK := sk235LogKCertificate, logChi := chi276LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (6544405699/6544295936) } }, logDArg := sk235LogDArgCertificate }

private noncomputable def leaf5069InnerLog : WideLogData :=
  innerPair548Data

set_option maxRecDepth 1000000 in
private theorem leaf5069LocalValidity :
    LeafFacts leaf5069Box leaf5069Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5069Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (3272257731/3272147968) }) = true
      norm_num [leaf5069Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5069CertificateValid :
    WideCertificateValid leaf5069Box leaf5069Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk235ValidityFacts chi276ValidityFacts
    leaf5069LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5069CoverageChecked :
    coverageCheck (innerAD leaf5069Box) leaf5069InnerLog = true := by
  rfl'

private theorem leaf5069InnerLogValid :
    leaf5069InnerLog.Valid 8 (innerAD leaf5069Box) :=
  wideLogDataValid_of_cachedCheck endpoint283PositiveFacts
    endpoint87PositiveFacts.valid leaf5069CoverageChecked

private noncomputable def leaf5069InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814681/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5069InputLogOnePlusV_eq :
    leaf5069InputLogOnePlusV = outerEnclosure 24
      (leaf5069Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5069RoundedFacts : LeafRoundedFacts 8
    leaf5069Certificate.logOnePlusV leaf5069InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5069InputLogOnePlusV_eq }

private noncomputable def leaf5069Inputs : Inputs :=
  inputsOfCaches globalInput sk235RoundedInputs
    chi276InputQChi innerPair548Input
    leaf5069InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5069LowerChecked :
    lowerCheck 24 leaf5069Box leaf5069Inputs = true := by
  rfl'

private theorem leaf5069CoversExact : CoversExact 8
    leaf5069Box leaf5069Certificate leaf5069InnerLog leaf5069Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk235RoundedFacts chi276RoundedFacts
    innerPair548RoundedFacts leaf5069RoundedFacts (by rfl)

private theorem leaf5069FlatSound : Sound leaf5069Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5069CertificateValid
    leaf5069InnerLogValid leaf5069CoversExact leaf5069LowerChecked

private noncomputable def leaf5070Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (67/256), chiHi := (17/64) }

private noncomputable def leaf5070Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742463/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715089920) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2175760063/2147483648) }, upper := { exponent := 1, mantissa := (2095/2048) } }, logOuter := sk236LogOuterCertificate, logK := sk236LogKCertificate, logChi := chi276LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432502271/137430179840) } }, logDArg := sk236LogDArgCertificate }

private noncomputable def leaf5070InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf5070LocalValidity :
    LeafFacts leaf5070Box leaf5070Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5070Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715089920) }) = true
      norm_num [leaf5070Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5070CertificateValid :
    WideCertificateValid leaf5070Box leaf5070Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk236ValidityFacts chi276ValidityFacts
    leaf5070LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5070CoverageChecked :
    coverageCheck (innerAD leaf5070Box) leaf5070InnerLog = true := by
  rfl'

private theorem leaf5070InnerLogValid :
    leaf5070InnerLog.Valid 8 (innerAD leaf5070Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf5070CoverageChecked

private noncomputable def leaf5070InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907341/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5070InputLogOnePlusV_eq :
    leaf5070InputLogOnePlusV = outerEnclosure 24
      (leaf5070Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5070RoundedFacts : LeafRoundedFacts 8
    leaf5070Certificate.logOnePlusV leaf5070InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5070InputLogOnePlusV_eq }

private noncomputable def leaf5070Inputs : Inputs :=
  inputsOfCaches globalInput sk236RoundedInputs
    chi276InputQChi innerPair116Input
    leaf5070InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5070LowerChecked :
    lowerCheck 24 leaf5070Box leaf5070Inputs = true := by
  rfl'

private theorem leaf5070CoversExact : CoversExact 8
    leaf5070Box leaf5070Certificate leaf5070InnerLog leaf5070Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk236RoundedFacts chi276RoundedFacts
    innerPair116RoundedFacts leaf5070RoundedFacts (by rfl)

private theorem leaf5070FlatSound : Sound leaf5070Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5070CertificateValid
    leaf5070InnerLogValid leaf5070CoversExact leaf5070LowerChecked

private noncomputable def leaf5071Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (1/4), chiHi := (65/256) }

private noncomputable def leaf5071Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742459/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9816773193/9816466688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2130608519/1073741824) }, upper := { exponent := 1, mantissa := (32829/32768) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi277LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (19633239881/19632933376) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf5071InnerLog : WideLogData :=
  innerPair542Data

set_option maxRecDepth 1000000 in
private theorem leaf5071LocalValidity :
    LeafFacts leaf5071Box leaf5071Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5071Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9816773193/9816466688) }) = true
      norm_num [leaf5071Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5071CertificateValid :
    WideCertificateValid leaf5071Box leaf5071Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi277ValidityFacts
    leaf5071LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5071CoverageChecked :
    coverageCheck (innerAD leaf5071Box) leaf5071InnerLog = true := by
  rfl'

private theorem leaf5071InnerLogValid :
    leaf5071InnerLog.Valid 8 (innerAD leaf5071Box) :=
  wideLogDataValid_of_cachedCheck endpoint276PositiveFacts
    endpoint320PositiveFacts.valid leaf5071CoverageChecked

private noncomputable def leaf5071InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629343/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5071InputLogOnePlusV_eq :
    leaf5071InputLogOnePlusV = outerEnclosure 24
      (leaf5071Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5071RoundedFacts : LeafRoundedFacts 8
    leaf5071Certificate.logOnePlusV leaf5071InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5071InputLogOnePlusV_eq }

private noncomputable def leaf5071Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi277InputQChi innerPair542Input
    leaf5071InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5071LowerChecked :
    lowerCheck 24 leaf5071Box leaf5071Inputs = true := by
  rfl'

private theorem leaf5071CoversExact : CoversExact 8
    leaf5071Box leaf5071Certificate leaf5071InnerLog leaf5071Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi277RoundedFacts
    innerPair542RoundedFacts leaf5071RoundedFacts (by rfl)

private theorem leaf5071FlatSound : Sound leaf5071Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5071CertificateValid
    leaf5071InnerLogValid leaf5071CoversExact leaf5071LowerChecked

private noncomputable def leaf5072Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (1/4), chiHi := (65/256) }

private noncomputable def leaf5072Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742461/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22905083392) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2134802565/1073741824) }, upper := { exponent := 1, mantissa := (16447/16384) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi277LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810887509/45810166784) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf5072InnerLog : WideLogData :=
  innerPair534Data

set_option maxRecDepth 1000000 in
private theorem leaf5072LocalValidity :
    LeafFacts leaf5072Box leaf5072Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5072Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22905083392) }) = true
      norm_num [leaf5072Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5072CertificateValid :
    WideCertificateValid leaf5072Box leaf5072Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi277ValidityFacts
    leaf5072LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5072CoverageChecked :
    coverageCheck (innerAD leaf5072Box) leaf5072InnerLog = true := by
  rfl'

private theorem leaf5072InnerLogValid :
    leaf5072InnerLog.Valid 8 (innerAD leaf5072Box) :=
  wideLogDataValid_of_cachedCheck endpoint267PositiveFacts
    endpoint361PositiveFacts.valid leaf5072CoverageChecked

private noncomputable def leaf5072InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629345/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5072InputLogOnePlusV_eq :
    leaf5072InputLogOnePlusV = outerEnclosure 24
      (leaf5072Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5072RoundedFacts : LeafRoundedFacts 8
    leaf5072Certificate.logOnePlusV leaf5072InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5072InputLogOnePlusV_eq }

private noncomputable def leaf5072Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi277InputQChi innerPair534Input
    leaf5072InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5072LowerChecked :
    lowerCheck 24 leaf5072Box leaf5072Inputs = true := by
  rfl'

private theorem leaf5072CoversExact : CoversExact 8
    leaf5072Box leaf5072Certificate leaf5072InnerLog leaf5072Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi277RoundedFacts
    innerPair534RoundedFacts leaf5072RoundedFacts (by rfl)

private theorem leaf5072FlatSound : Sound leaf5072Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5072CertificateValid
    leaf5072InnerLogValid leaf5072CoversExact leaf5072LowerChecked

private noncomputable def leaf5073Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (65/256), chiHi := (33/128) }

private noncomputable def leaf5073Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742461/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715202048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2147122581/1073741824) }, upper := { exponent := 1, mantissa := (16541/16384) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi278LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432614399/137430404096) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf5073InnerLog : WideLogData :=
  innerPair630Data

set_option maxRecDepth 1000000 in
private theorem leaf5073LocalValidity :
    LeafFacts leaf5073Box leaf5073Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5073Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715202048) }) = true
      norm_num [leaf5073Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5073CertificateValid :
    WideCertificateValid leaf5073Box leaf5073Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi278ValidityFacts
    leaf5073LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5073CoverageChecked :
    coverageCheck (innerAD leaf5073Box) leaf5073InnerLog = true := by
  rfl'

private theorem leaf5073InnerLogValid :
    leaf5073InnerLog.Valid 8 (innerAD leaf5073Box) :=
  wideLogDataValid_of_cachedCheck endpoint362PositiveFacts
    endpoint322PositiveFacts.valid leaf5073CoverageChecked

private noncomputable def leaf5073InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629351/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5073InputLogOnePlusV_eq :
    leaf5073InputLogOnePlusV = outerEnclosure 24
      (leaf5073Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5073RoundedFacts : LeafRoundedFacts 8
    leaf5073Certificate.logOnePlusV leaf5073InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5073InputLogOnePlusV_eq }

private noncomputable def leaf5073Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi278InputQChi innerPair630Input
    leaf5073InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5073LowerChecked :
    lowerCheck 24 leaf5073Box leaf5073Inputs = true := by
  rfl'

private theorem leaf5073CoversExact : CoversExact 8
    leaf5073Box leaf5073Certificate leaf5073InnerLog leaf5073Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi278RoundedFacts
    innerPair630RoundedFacts leaf5073RoundedFacts (by rfl)

private theorem leaf5073FlatSound : Sound leaf5073Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5073CertificateValid
    leaf5073InnerLogValid leaf5073CoversExact leaf5073LowerChecked

private noncomputable def leaf5074Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (65/256), chiHi := (33/128) }

private noncomputable def leaf5074Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742463/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715185152) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2151382159/2147483648) }, upper := { exponent := 1, mantissa := (8287/8192) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi278LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432597503/137430370304) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf5074InnerLog : WideLogData :=
  innerPair119Data

set_option maxRecDepth 1000000 in
private theorem leaf5074LocalValidity :
    LeafFacts leaf5074Box leaf5074Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5074Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715185152) }) = true
      norm_num [leaf5074Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5074CertificateValid :
    WideCertificateValid leaf5074Box leaf5074Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi278ValidityFacts
    leaf5074LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5074CoverageChecked :
    coverageCheck (innerAD leaf5074Box) leaf5074InnerLog = true := by
  rfl'

private theorem leaf5074InnerLogValid :
    leaf5074InnerLog.Valid 8 (innerAD leaf5074Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint82PositiveFacts.valid leaf5074CoverageChecked

private noncomputable def leaf5074InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629353/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5074InputLogOnePlusV_eq :
    leaf5074InputLogOnePlusV = outerEnclosure 24
      (leaf5074Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5074RoundedFacts : LeafRoundedFacts 8
    leaf5074Certificate.logOnePlusV leaf5074InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5074InputLogOnePlusV_eq }

private noncomputable def leaf5074Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi278InputQChi innerPair119Input
    leaf5074InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5074LowerChecked :
    lowerCheck 24 leaf5074Box leaf5074Inputs = true := by
  rfl'

private theorem leaf5074CoversExact : CoversExact 8
    leaf5074Box leaf5074Certificate leaf5074InnerLog leaf5074Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi278RoundedFacts
    innerPair119RoundedFacts leaf5074RoundedFacts (by rfl)

private theorem leaf5074FlatSound : Sound leaf5074Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5074CertificateValid
    leaf5074InnerLogValid leaf5074CoversExact leaf5074LowerChecked

private noncomputable def leaf5075Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (1/4), chiHi := (65/256) }

private noncomputable def leaf5075Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742463/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715233536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2138996611/1073741824) }, upper := { exponent := 1, mantissa := (32959/32768) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi277LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432645887/137430467072) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf5075InnerLog : WideLogData :=
  innerPair533Data

set_option maxRecDepth 1000000 in
private theorem leaf5075LocalValidity :
    LeafFacts leaf5075Box leaf5075Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5075Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715233536) }) = true
      norm_num [leaf5075Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5075CertificateValid :
    WideCertificateValid leaf5075Box leaf5075Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi277ValidityFacts
    leaf5075LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5075CoverageChecked :
    coverageCheck (innerAD leaf5075Box) leaf5075InnerLog = true := by
  rfl'

private theorem leaf5075InnerLogValid :
    leaf5075InnerLog.Valid 8 (innerAD leaf5075Box) :=
  wideLogDataValid_of_cachedCheck endpoint267PositiveFacts
    endpoint283PositiveFacts.valid leaf5075CoverageChecked

private noncomputable def leaf5075InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629347/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5075InputLogOnePlusV_eq :
    leaf5075InputLogOnePlusV = outerEnclosure 24
      (leaf5075Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5075RoundedFacts : LeafRoundedFacts 8
    leaf5075Certificate.logOnePlusV leaf5075InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5075InputLogOnePlusV_eq }

private noncomputable def leaf5075Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi277InputQChi innerPair533Input
    leaf5075InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5075LowerChecked :
    lowerCheck 24 leaf5075Box leaf5075Inputs = true := by
  rfl'

private theorem leaf5075CoversExact : CoversExact 8
    leaf5075Box leaf5075Certificate leaf5075InnerLog leaf5075Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi277RoundedFacts
    innerPair533RoundedFacts leaf5075RoundedFacts (by rfl)

private theorem leaf5075FlatSound : Sound leaf5075Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5075CertificateValid
    leaf5075InnerLogValid leaf5075CoversExact leaf5075LowerChecked

private noncomputable def leaf5076Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (1/4), chiHi := (65/256) }

private noncomputable def leaf5076Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742465/1073741824) }, vSqrt := { lower := (65527/65536), upper := (68717412351/68715216896) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2143190657/1073741824) }, upper := { exponent := 1, mantissa := (129/128) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi277LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (137432629247/137430433792) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf5076InnerLog : WideLogData :=
  innerPair533Data

set_option maxRecDepth 1000000 in
private theorem leaf5076LocalValidity :
    LeafFacts leaf5076Box leaf5076Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5076Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (68717412351/68715216896) }) = true
      norm_num [leaf5076Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5076CertificateValid :
    WideCertificateValid leaf5076Box leaf5076Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi277ValidityFacts
    leaf5076LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5076CoverageChecked :
    coverageCheck (innerAD leaf5076Box) leaf5076InnerLog = true := by
  rfl'

private theorem leaf5076InnerLogValid :
    leaf5076InnerLog.Valid 8 (innerAD leaf5076Box) :=
  wideLogDataValid_of_cachedCheck endpoint267PositiveFacts
    endpoint283PositiveFacts.valid leaf5076CoverageChecked

private noncomputable def leaf5076InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629349/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5076InputLogOnePlusV_eq :
    leaf5076InputLogOnePlusV = outerEnclosure 24
      (leaf5076Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5076RoundedFacts : LeafRoundedFacts 8
    leaf5076Certificate.logOnePlusV leaf5076InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5076InputLogOnePlusV_eq }

private noncomputable def leaf5076Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi277InputQChi innerPair533Input
    leaf5076InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5076LowerChecked :
    lowerCheck 24 leaf5076Box leaf5076Inputs = true := by
  rfl'

private theorem leaf5076CoversExact : CoversExact 8
    leaf5076Box leaf5076Certificate leaf5076InnerLog leaf5076Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi277RoundedFacts
    innerPair533RoundedFacts leaf5076RoundedFacts (by rfl)

private theorem leaf5076FlatSound : Sound leaf5076Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5076CertificateValid
    leaf5076InnerLogValid leaf5076CoversExact leaf5076LowerChecked

private noncomputable def leaf5077Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (65/256), chiHi := (33/128) }

private noncomputable def leaf5077Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742465/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9816773193/9816452608) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2155641737/2147483648) }, upper := { exponent := 1, mantissa := (16607/16384) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi278LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (19633225801/19632905216) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf5077InnerLog : WideLogData :=
  innerPair119Data

set_option maxRecDepth 1000000 in
private theorem leaf5077LocalValidity :
    LeafFacts leaf5077Box leaf5077Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5077Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9816773193/9816452608) }) = true
      norm_num [leaf5077Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5077CertificateValid :
    WideCertificateValid leaf5077Box leaf5077Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi278ValidityFacts
    leaf5077LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5077CoverageChecked :
    coverageCheck (innerAD leaf5077Box) leaf5077InnerLog = true := by
  rfl'

private theorem leaf5077InnerLogValid :
    leaf5077InnerLog.Valid 8 (innerAD leaf5077Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint82PositiveFacts.valid leaf5077CoverageChecked

private noncomputable def leaf5077InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629355/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5077InputLogOnePlusV_eq :
    leaf5077InputLogOnePlusV = outerEnclosure 24
      (leaf5077Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5077RoundedFacts : LeafRoundedFacts 8
    leaf5077Certificate.logOnePlusV leaf5077InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5077InputLogOnePlusV_eq }

private noncomputable def leaf5077Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi278InputQChi innerPair119Input
    leaf5077InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5077LowerChecked :
    lowerCheck 24 leaf5077Box leaf5077Inputs = true := by
  rfl'

private theorem leaf5077CoversExact : CoversExact 8
    leaf5077Box leaf5077Certificate leaf5077InnerLog leaf5077Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi278RoundedFacts
    innerPair119RoundedFacts leaf5077RoundedFacts (by rfl)

private theorem leaf5077FlatSound : Sound leaf5077Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5077CertificateValid
    leaf5077InnerLogValid leaf5077CoversExact leaf5077LowerChecked

private noncomputable def leaf5078Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (65/256), chiHi := (33/128) }

private noncomputable def leaf5078Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742467/1073741824) }, vSqrt := { lower := (65527/65536), upper := (68717412351/68715151360) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2159901315/2147483648) }, upper := { exponent := 1, mantissa := (65/64) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi278LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (137432563711/137430302720) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf5078InnerLog : WideLogData :=
  innerPair119Data

set_option maxRecDepth 1000000 in
private theorem leaf5078LocalValidity :
    LeafFacts leaf5078Box leaf5078Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5078Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (68717412351/68715151360) }) = true
      norm_num [leaf5078Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5078CertificateValid :
    WideCertificateValid leaf5078Box leaf5078Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi278ValidityFacts
    leaf5078LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5078CoverageChecked :
    coverageCheck (innerAD leaf5078Box) leaf5078InnerLog = true := by
  rfl'

private theorem leaf5078InnerLogValid :
    leaf5078InnerLog.Valid 8 (innerAD leaf5078Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint82PositiveFacts.valid leaf5078CoverageChecked

private noncomputable def leaf5078InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629357/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5078InputLogOnePlusV_eq :
    leaf5078InputLogOnePlusV = outerEnclosure 24
      (leaf5078Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5078RoundedFacts : LeafRoundedFacts 8
    leaf5078Certificate.logOnePlusV leaf5078InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5078InputLogOnePlusV_eq }

private noncomputable def leaf5078Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi278InputQChi innerPair119Input
    leaf5078InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5078LowerChecked :
    lowerCheck 24 leaf5078Box leaf5078Inputs = true := by
  rfl'

private theorem leaf5078CoversExact : CoversExact 8
    leaf5078Box leaf5078Certificate leaf5078InnerLog leaf5078Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi278RoundedFacts
    innerPair119RoundedFacts leaf5078RoundedFacts (by rfl)

private theorem leaf5078FlatSound : Sound leaf5078Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5078CertificateValid
    leaf5078InnerLogValid leaf5078CoversExact leaf5078LowerChecked

private noncomputable def leaf5079Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (33/128), chiHi := (67/256) }

private noncomputable def leaf5079Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742463/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22905045760) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2163636643/2147483648) }, upper := { exponent := 1, mantissa := (33335/32768) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi275LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810849877/45810091520) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf5079InnerLog : WideLogData :=
  innerPair121Data

set_option maxRecDepth 1000000 in
private theorem leaf5079LocalValidity :
    LeafFacts leaf5079Box leaf5079Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5079Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22905045760) }) = true
      norm_num [leaf5079Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5079CertificateValid :
    WideCertificateValid leaf5079Box leaf5079Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi275ValidityFacts
    leaf5079LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5079CoverageChecked :
    coverageCheck (innerAD leaf5079Box) leaf5079InnerLog = true := by
  rfl'

private theorem leaf5079InnerLogValid :
    leaf5079InnerLog.Valid 8 (innerAD leaf5079Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint87PositiveFacts.valid leaf5079CoverageChecked

private noncomputable def leaf5079InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814679/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5079InputLogOnePlusV_eq :
    leaf5079InputLogOnePlusV = outerEnclosure 24
      (leaf5079Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5079RoundedFacts : LeafRoundedFacts 8
    leaf5079Certificate.logOnePlusV leaf5079InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5079InputLogOnePlusV_eq }

private noncomputable def leaf5079Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi275InputQChi innerPair121Input
    leaf5079InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5079LowerChecked :
    lowerCheck 24 leaf5079Box leaf5079Inputs = true := by
  rfl'

private theorem leaf5079CoversExact : CoversExact 8
    leaf5079Box leaf5079Certificate leaf5079InnerLog leaf5079Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi275RoundedFacts
    innerPair121RoundedFacts leaf5079RoundedFacts (by rfl)

private theorem leaf5079FlatSound : Sound leaf5079Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5079CertificateValid
    leaf5079InnerLogValid leaf5079CoversExact leaf5079LowerChecked

private noncomputable def leaf5080Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (33/128), chiHi := (67/256) }

private noncomputable def leaf5080Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742465/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715120128) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2167961753/2147483648) }, upper := { exponent := 1, mantissa := (16701/16384) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi275LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432532479/137430240256) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf5080InnerLog : WideLogData :=
  innerPair548Data

set_option maxRecDepth 1000000 in
private theorem leaf5080LocalValidity :
    LeafFacts leaf5080Box leaf5080Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5080Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715120128) }) = true
      norm_num [leaf5080Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5080CertificateValid :
    WideCertificateValid leaf5080Box leaf5080Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi275ValidityFacts
    leaf5080LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5080CoverageChecked :
    coverageCheck (innerAD leaf5080Box) leaf5080InnerLog = true := by
  rfl'

private theorem leaf5080InnerLogValid :
    leaf5080InnerLog.Valid 8 (innerAD leaf5080Box) :=
  wideLogDataValid_of_cachedCheck endpoint283PositiveFacts
    endpoint87PositiveFacts.valid leaf5080CoverageChecked

private noncomputable def leaf5080InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629361/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5080InputLogOnePlusV_eq :
    leaf5080InputLogOnePlusV = outerEnclosure 24
      (leaf5080Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5080RoundedFacts : LeafRoundedFacts 8
    leaf5080Certificate.logOnePlusV leaf5080InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5080InputLogOnePlusV_eq }

private noncomputable def leaf5080Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi275InputQChi innerPair548Input
    leaf5080InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5080LowerChecked :
    lowerCheck 24 leaf5080Box leaf5080Inputs = true := by
  rfl'

private theorem leaf5080CoversExact : CoversExact 8
    leaf5080Box leaf5080Certificate leaf5080InnerLog leaf5080Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi275RoundedFacts
    innerPair548RoundedFacts leaf5080RoundedFacts (by rfl)

private theorem leaf5080FlatSound : Sound leaf5080Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5080CertificateValid
    leaf5080InnerLogValid leaf5080CoversExact leaf5080LowerChecked

private noncomputable def leaf5081Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (67/256), chiHi := (17/64) }

private noncomputable def leaf5081Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742465/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715072512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2180150705/2147483648) }, upper := { exponent := 1, mantissa := (8397/8192) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi276LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432484863/137430145024) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf5081InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf5081LocalValidity :
    LeafFacts leaf5081Box leaf5081Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5081Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715072512) }) = true
      norm_num [leaf5081Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5081CertificateValid :
    WideCertificateValid leaf5081Box leaf5081Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi276ValidityFacts
    leaf5081LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5081CoverageChecked :
    coverageCheck (innerAD leaf5081Box) leaf5081InnerLog = true := by
  rfl'

private theorem leaf5081InnerLogValid :
    leaf5081InnerLog.Valid 8 (innerAD leaf5081Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf5081CoverageChecked

private noncomputable def leaf5081InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814683/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5081InputLogOnePlusV_eq :
    leaf5081InputLogOnePlusV = outerEnclosure 24
      (leaf5081Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5081RoundedFacts : LeafRoundedFacts 8
    leaf5081Certificate.logOnePlusV leaf5081InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5081InputLogOnePlusV_eq }

private noncomputable def leaf5081Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi276InputQChi innerPair116Input
    leaf5081InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5081LowerChecked :
    lowerCheck 24 leaf5081Box leaf5081Inputs = true := by
  rfl'

private theorem leaf5081CoversExact : CoversExact 8
    leaf5081Box leaf5081Certificate leaf5081InnerLog leaf5081Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi276RoundedFacts
    innerPair116RoundedFacts leaf5081RoundedFacts (by rfl)

private theorem leaf5081FlatSound : Sound leaf5081Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5081CertificateValid
    leaf5081InnerLogValid leaf5081CoversExact leaf5081LowerChecked

private noncomputable def leaf5082Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (67/256), chiHi := (17/64) }

private noncomputable def leaf5082Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742467/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22905018368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2184541347/2147483648) }, upper := { exponent := 1, mantissa := (4207/4096) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi276LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810822485/45810036736) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf5082InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf5082LocalValidity :
    LeafFacts leaf5082Box leaf5082Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5082Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22905018368) }) = true
      norm_num [leaf5082Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5082CertificateValid :
    WideCertificateValid leaf5082Box leaf5082Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi276ValidityFacts
    leaf5082LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5082CoverageChecked :
    coverageCheck (innerAD leaf5082Box) leaf5082InnerLog = true := by
  rfl'

private theorem leaf5082InnerLogValid :
    leaf5082InnerLog.Valid 8 (innerAD leaf5082Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf5082CoverageChecked

private noncomputable def leaf5082InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629369/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5082InputLogOnePlusV_eq :
    leaf5082InputLogOnePlusV = outerEnclosure 24
      (leaf5082Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5082RoundedFacts : LeafRoundedFacts 8
    leaf5082Certificate.logOnePlusV leaf5082InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5082InputLogOnePlusV_eq }

private noncomputable def leaf5082Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi276InputQChi innerPair116Input
    leaf5082InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5082LowerChecked :
    lowerCheck 24 leaf5082Box leaf5082Inputs = true := by
  rfl'

private theorem leaf5082CoversExact : CoversExact 8
    leaf5082Box leaf5082Certificate leaf5082InnerLog leaf5082Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi276RoundedFacts
    innerPair116RoundedFacts leaf5082RoundedFacts (by rfl)

private theorem leaf5082FlatSound : Sound leaf5082Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5082CertificateValid
    leaf5082InnerLogValid leaf5082CoversExact leaf5082LowerChecked

private noncomputable def leaf5083Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (33/128), chiHi := (67/256) }

private noncomputable def leaf5083Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742467/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715102976) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2172286863/2147483648) }, upper := { exponent := 1, mantissa := (33469/32768) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi275LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432515327/137430205952) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf5083InnerLog : WideLogData :=
  innerPair548Data

set_option maxRecDepth 1000000 in
private theorem leaf5083LocalValidity :
    LeafFacts leaf5083Box leaf5083Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5083Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715102976) }) = true
      norm_num [leaf5083Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5083CertificateValid :
    WideCertificateValid leaf5083Box leaf5083Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi275ValidityFacts
    leaf5083LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5083CoverageChecked :
    coverageCheck (innerAD leaf5083Box) leaf5083InnerLog = true := by
  rfl'

private theorem leaf5083InnerLogValid :
    leaf5083InnerLog.Valid 8 (innerAD leaf5083Box) :=
  wideLogDataValid_of_cachedCheck endpoint283PositiveFacts
    endpoint87PositiveFacts.valid leaf5083CoverageChecked

private noncomputable def leaf5083InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629363/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5083InputLogOnePlusV_eq :
    leaf5083InputLogOnePlusV = outerEnclosure 24
      (leaf5083Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5083RoundedFacts : LeafRoundedFacts 8
    leaf5083Certificate.logOnePlusV leaf5083InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5083InputLogOnePlusV_eq }

private noncomputable def leaf5083Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi275InputQChi innerPair548Input
    leaf5083InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5083LowerChecked :
    lowerCheck 24 leaf5083Box leaf5083Inputs = true := by
  rfl'

private theorem leaf5083CoversExact : CoversExact 8
    leaf5083Box leaf5083Certificate leaf5083InnerLog leaf5083Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi275RoundedFacts
    innerPair548RoundedFacts leaf5083RoundedFacts (by rfl)

private theorem leaf5083FlatSound : Sound leaf5083Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5083CertificateValid
    leaf5083InnerLogValid leaf5083CoversExact leaf5083LowerChecked

private noncomputable def leaf5084Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (33/128), chiHi := (67/256) }

private noncomputable def leaf5084Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742469/1073741824) }, vSqrt := { lower := (65527/65536), upper := (1090752577/1090715648) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2176611973/2147483648) }, upper := { exponent := 1, mantissa := (131/128) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi275LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (2181468225/2181431296) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf5084InnerLog : WideLogData :=
  innerPair548Data

set_option maxRecDepth 1000000 in
private theorem leaf5084LocalValidity :
    LeafFacts leaf5084Box leaf5084Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5084Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (1090752577/1090715648) }) = true
      norm_num [leaf5084Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5084CertificateValid :
    WideCertificateValid leaf5084Box leaf5084Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi275ValidityFacts
    leaf5084LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5084CoverageChecked :
    coverageCheck (innerAD leaf5084Box) leaf5084InnerLog = true := by
  rfl'

private theorem leaf5084InnerLogValid :
    leaf5084InnerLog.Valid 8 (innerAD leaf5084Box) :=
  wideLogDataValid_of_cachedCheck endpoint283PositiveFacts
    endpoint87PositiveFacts.valid leaf5084CoverageChecked

private noncomputable def leaf5084InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629365/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5084InputLogOnePlusV_eq :
    leaf5084InputLogOnePlusV = outerEnclosure 24
      (leaf5084Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5084RoundedFacts : LeafRoundedFacts 8
    leaf5084Certificate.logOnePlusV leaf5084InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5084InputLogOnePlusV_eq }

private noncomputable def leaf5084Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi275InputQChi innerPair548Input
    leaf5084InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5084LowerChecked :
    lowerCheck 24 leaf5084Box leaf5084Inputs = true := by
  rfl'

private theorem leaf5084CoversExact : CoversExact 8
    leaf5084Box leaf5084Certificate leaf5084InnerLog leaf5084Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi275RoundedFacts
    innerPair548RoundedFacts leaf5084RoundedFacts (by rfl)

private theorem leaf5084FlatSound : Sound leaf5084Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5084CertificateValid
    leaf5084InnerLogValid leaf5084CoversExact leaf5084LowerChecked

private noncomputable def leaf5085Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (67/256), chiHi := (17/64) }

private noncomputable def leaf5085Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742469/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715037696) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2188931989/2147483648) }, upper := { exponent := 1, mantissa := (8431/8192) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi276LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432450047/137430075392) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf5085InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf5085LocalValidity :
    LeafFacts leaf5085Box leaf5085Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5085Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715037696) }) = true
      norm_num [leaf5085Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5085CertificateValid :
    WideCertificateValid leaf5085Box leaf5085Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi276ValidityFacts
    leaf5085LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5085CoverageChecked :
    coverageCheck (innerAD leaf5085Box) leaf5085InnerLog = true := by
  rfl'

private theorem leaf5085InnerLogValid :
    leaf5085InnerLog.Valid 8 (innerAD leaf5085Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf5085CoverageChecked

private noncomputable def leaf5085InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629371/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5085InputLogOnePlusV_eq :
    leaf5085InputLogOnePlusV = outerEnclosure 24
      (leaf5085Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5085RoundedFacts : LeafRoundedFacts 8
    leaf5085Certificate.logOnePlusV leaf5085InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5085InputLogOnePlusV_eq }

private noncomputable def leaf5085Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi276InputQChi innerPair116Input
    leaf5085InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5085LowerChecked :
    lowerCheck 24 leaf5085Box leaf5085Inputs = true := by
  rfl'

private theorem leaf5085CoversExact : CoversExact 8
    leaf5085Box leaf5085Certificate leaf5085InnerLog leaf5085Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi276RoundedFacts
    innerPair116RoundedFacts leaf5085RoundedFacts (by rfl)

private theorem leaf5085FlatSound : Sound leaf5085Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5085CertificateValid
    leaf5085InnerLogValid leaf5085CoversExact leaf5085LowerChecked

private noncomputable def leaf5086Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (67/256), chiHi := (17/64) }

private noncomputable def leaf5086Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742471/1073741824) }, vSqrt := { lower := (65527/65536), upper := (68717412351/68715020288) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2193322631/2147483648) }, upper := { exponent := 1, mantissa := (33/32) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi276LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (137432432639/137430040576) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf5086InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf5086LocalValidity :
    LeafFacts leaf5086Box leaf5086Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5086Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (68717412351/68715020288) }) = true
      norm_num [leaf5086Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5086CertificateValid :
    WideCertificateValid leaf5086Box leaf5086Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi276ValidityFacts
    leaf5086LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5086CoverageChecked :
    coverageCheck (innerAD leaf5086Box) leaf5086InnerLog = true := by
  rfl'

private theorem leaf5086InnerLogValid :
    leaf5086InnerLog.Valid 8 (innerAD leaf5086Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf5086CoverageChecked

private noncomputable def leaf5086InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629373/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5086InputLogOnePlusV_eq :
    leaf5086InputLogOnePlusV = outerEnclosure 24
      (leaf5086Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5086RoundedFacts : LeafRoundedFacts 8
    leaf5086Certificate.logOnePlusV leaf5086InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5086InputLogOnePlusV_eq }

private noncomputable def leaf5086Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi276InputQChi innerPair116Input
    leaf5086InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5086LowerChecked :
    lowerCheck 24 leaf5086Box leaf5086Inputs = true := by
  rfl'

private theorem leaf5086CoversExact : CoversExact 8
    leaf5086Box leaf5086Certificate leaf5086InnerLog leaf5086Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi276RoundedFacts
    innerPair116RoundedFacts leaf5086RoundedFacts (by rfl)

private theorem leaf5086FlatSound : Sound leaf5086Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5086CertificateValid
    leaf5086InnerLogValid leaf5086CoversExact leaf5086LowerChecked

private noncomputable def leaf5087Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (249/64), chiLo := (17/64), chiHi := (69/256) }

private noncomputable def leaf5087Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742459/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715078400) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2178840071/2147483648) }, upper := { exponent := 1, mantissa := (33565/32768) } }, logOuter := sk233LogOuterCertificate, logK := sk233LogKCertificate, logChi := chi257LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432490751/137430156800) } }, logDArg := sk233LogDArgCertificate }

private noncomputable def leaf5087InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf5087LocalValidity :
    LeafFacts leaf5087Box leaf5087Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5087Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715078400) }) = true
      norm_num [leaf5087Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5087CertificateValid :
    WideCertificateValid leaf5087Box leaf5087Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk233ValidityFacts chi257ValidityFacts
    leaf5087LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5087CoverageChecked :
    coverageCheck (innerAD leaf5087Box) leaf5087InnerLog = true := by
  rfl'

private theorem leaf5087InnerLogValid :
    leaf5087InnerLog.Valid 8 (innerAD leaf5087Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf5087CoverageChecked

private noncomputable def leaf5087InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814683/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5087InputLogOnePlusV_eq :
    leaf5087InputLogOnePlusV = outerEnclosure 24
      (leaf5087Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5087RoundedFacts : LeafRoundedFacts 8
    leaf5087Certificate.logOnePlusV leaf5087InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5087InputLogOnePlusV_eq }

private noncomputable def leaf5087Inputs : Inputs :=
  inputsOfCaches globalInput sk233RoundedInputs
    chi257InputQChi innerPair116Input
    leaf5087InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5087LowerChecked :
    lowerCheck 24 leaf5087Box leaf5087Inputs = true := by
  rfl'

private theorem leaf5087CoversExact : CoversExact 8
    leaf5087Box leaf5087Certificate leaf5087InnerLog leaf5087Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk233RoundedFacts chi257RoundedFacts
    innerPair116RoundedFacts leaf5087RoundedFacts (by rfl)

private theorem leaf5087FlatSound : Sound leaf5087Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5087CertificateValid
    leaf5087InnerLogValid leaf5087CoversExact leaf5087LowerChecked

private noncomputable def leaf5088Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (249/64), kHi := (125/32), chiLo := (17/64), chiHi := (69/256) }

private noncomputable def leaf5088Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742461/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9816773193/9816437248) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2183296245/2147483648) }, upper := { exponent := 1, mantissa := (16817/16384) } }, logOuter := sk234LogOuterCertificate, logK := sk234LogKCertificate, logChi := chi257LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (19633210441/19632874496) } }, logDArg := sk234LogDArgCertificate }

private noncomputable def leaf5088InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf5088LocalValidity :
    LeafFacts leaf5088Box leaf5088Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5088Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9816773193/9816437248) }) = true
      norm_num [leaf5088Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5088CertificateValid :
    WideCertificateValid leaf5088Box leaf5088Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk234ValidityFacts chi257ValidityFacts
    leaf5088LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5088CoverageChecked :
    coverageCheck (innerAD leaf5088Box) leaf5088InnerLog = true := by
  rfl'

private theorem leaf5088InnerLogValid :
    leaf5088InnerLog.Valid 8 (innerAD leaf5088Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf5088CoverageChecked

private noncomputable def leaf5088InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453671/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5088InputLogOnePlusV_eq :
    leaf5088InputLogOnePlusV = outerEnclosure 24
      (leaf5088Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5088RoundedFacts : LeafRoundedFacts 8
    leaf5088Certificate.logOnePlusV leaf5088InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5088InputLogOnePlusV_eq }

private noncomputable def leaf5088Inputs : Inputs :=
  inputsOfCaches globalInput sk234RoundedInputs
    chi257InputQChi innerPair116Input
    leaf5088InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5088LowerChecked :
    lowerCheck 24 leaf5088Box leaf5088Inputs = true := by
  rfl'

private theorem leaf5088CoversExact : CoversExact 8
    leaf5088Box leaf5088Certificate leaf5088InnerLog leaf5088Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk234RoundedFacts chi257RoundedFacts
    innerPair116RoundedFacts leaf5088RoundedFacts (by rfl)

private theorem leaf5088FlatSound : Sound leaf5088Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5088CertificateValid
    leaf5088InnerLogValid leaf5088CoversExact leaf5088LowerChecked

private noncomputable def leaf5089Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (249/64), chiLo := (69/256), chiHi := (35/128) }

private noncomputable def leaf5089Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742461/1073741824) }, vSqrt := { lower := (8191/8192), upper := (2216690721/2216613376) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2195092005/2147483648) }, upper := { exponent := 1, mantissa := (16907/16384) } }, logOuter := sk233LogOuterCertificate, logK := sk233LogKCertificate, logChi := chi258LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (4433304097/4433226752) } }, logDArg := sk233LogDArgCertificate }

private noncomputable def leaf5089InnerLog : WideLogData :=
  innerPair311Data

set_option maxRecDepth 1000000 in
private theorem leaf5089LocalValidity :
    LeafFacts leaf5089Box leaf5089Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5089Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (2216690721/2216613376) }) = true
      norm_num [leaf5089Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5089CertificateValid :
    WideCertificateValid leaf5089Box leaf5089Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk233ValidityFacts chi258ValidityFacts
    leaf5089LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5089CoverageChecked :
    coverageCheck (innerAD leaf5089Box) leaf5089InnerLog = true := by
  rfl'

private theorem leaf5089InnerLogValid :
    leaf5089InnerLog.Valid 8 (innerAD leaf5089Box) :=
  wideLogDataValid_of_cachedCheck endpoint82PositiveFacts
    endpoint86PositiveFacts.valid leaf5089CoverageChecked

private noncomputable def leaf5089InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629373/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5089InputLogOnePlusV_eq :
    leaf5089InputLogOnePlusV = outerEnclosure 24
      (leaf5089Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5089RoundedFacts : LeafRoundedFacts 8
    leaf5089Certificate.logOnePlusV leaf5089InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5089InputLogOnePlusV_eq }

private noncomputable def leaf5089Inputs : Inputs :=
  inputsOfCaches globalInput sk233RoundedInputs
    chi258InputQChi innerPair311Input
    leaf5089InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5089LowerChecked :
    lowerCheck 24 leaf5089Box leaf5089Inputs = true := by
  rfl'

private theorem leaf5089CoversExact : CoversExact 8
    leaf5089Box leaf5089Certificate leaf5089InnerLog leaf5089Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk233RoundedFacts chi258RoundedFacts
    innerPair311RoundedFacts leaf5089RoundedFacts (by rfl)

private theorem leaf5089FlatSound : Sound leaf5089Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5089CertificateValid
    leaf5089InnerLogValid leaf5089CoversExact leaf5089LowerChecked

private noncomputable def leaf5090Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (249/64), kHi := (125/32), chiLo := (69/256), chiHi := (35/128) }

private noncomputable def leaf5090Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742463/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22904998912) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2199613711/2147483648) }, upper := { exponent := 1, mantissa := (8471/8192) } }, logOuter := sk234LogOuterCertificate, logK := sk234LogKCertificate, logChi := chi258LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810803029/45809997824) } }, logDArg := sk234LogDArgCertificate }

private noncomputable def leaf5090InnerLog : WideLogData :=
  innerPair327Data

set_option maxRecDepth 1000000 in
private theorem leaf5090LocalValidity :
    LeafFacts leaf5090Box leaf5090Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5090Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22904998912) }) = true
      norm_num [leaf5090Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5090CertificateValid :
    WideCertificateValid leaf5090Box leaf5090Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk234ValidityFacts chi258ValidityFacts
    leaf5090LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5090CoverageChecked :
    coverageCheck (innerAD leaf5090Box) leaf5090InnerLog = true := by
  rfl'

private theorem leaf5090InnerLogValid :
    leaf5090InnerLog.Valid 8 (innerAD leaf5090Box) :=
  wideLogDataValid_of_cachedCheck endpoint87PositiveFacts
    endpoint86PositiveFacts.valid leaf5090CoverageChecked

private noncomputable def leaf5090InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (181709/262144) }

set_option maxRecDepth 1000000 in
private theorem leaf5090InputLogOnePlusV_eq :
    leaf5090InputLogOnePlusV = outerEnclosure 24
      (leaf5090Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5090RoundedFacts : LeafRoundedFacts 8
    leaf5090Certificate.logOnePlusV leaf5090InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5090InputLogOnePlusV_eq }

private noncomputable def leaf5090Inputs : Inputs :=
  inputsOfCaches globalInput sk234RoundedInputs
    chi258InputQChi innerPair327Input
    leaf5090InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5090LowerChecked :
    lowerCheck 24 leaf5090Box leaf5090Inputs = true := by
  rfl'

private theorem leaf5090CoversExact : CoversExact 8
    leaf5090Box leaf5090Certificate leaf5090InnerLog leaf5090Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk234RoundedFacts chi258RoundedFacts
    innerPair327RoundedFacts leaf5090RoundedFacts (by rfl)

private theorem leaf5090FlatSound : Sound leaf5090Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5090CertificateValid
    leaf5090InnerLogValid leaf5090CoversExact leaf5090LowerChecked

private noncomputable def leaf5091Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (251/64), chiLo := (17/64), chiHi := (69/256) }

private noncomputable def leaf5091Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742463/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715043072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2187752419/2147483648) }, upper := { exponent := 1, mantissa := (33703/32768) } }, logOuter := sk235LogOuterCertificate, logK := sk235LogKCertificate, logChi := chi257LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432455423/137430086144) } }, logDArg := sk235LogDArgCertificate }

private noncomputable def leaf5091InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf5091LocalValidity :
    LeafFacts leaf5091Box leaf5091Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5091Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715043072) }) = true
      norm_num [leaf5091Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5091CertificateValid :
    WideCertificateValid leaf5091Box leaf5091Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk235ValidityFacts chi257ValidityFacts
    leaf5091LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5091CoverageChecked :
    coverageCheck (innerAD leaf5091Box) leaf5091InnerLog = true := by
  rfl'

private theorem leaf5091InnerLogValid :
    leaf5091InnerLog.Valid 8 (innerAD leaf5091Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf5091CoverageChecked

private noncomputable def leaf5091InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814685/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5091InputLogOnePlusV_eq :
    leaf5091InputLogOnePlusV = outerEnclosure 24
      (leaf5091Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5091RoundedFacts : LeafRoundedFacts 8
    leaf5091Certificate.logOnePlusV leaf5091InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5091InputLogOnePlusV_eq }

private noncomputable def leaf5091Inputs : Inputs :=
  inputsOfCaches globalInput sk235RoundedInputs
    chi257InputQChi innerPair116Input
    leaf5091InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5091LowerChecked :
    lowerCheck 24 leaf5091Box leaf5091Inputs = true := by
  rfl'

private theorem leaf5091CoversExact : CoversExact 8
    leaf5091Box leaf5091Certificate leaf5091InnerLog leaf5091Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk235RoundedFacts chi257RoundedFacts
    innerPair116RoundedFacts leaf5091RoundedFacts (by rfl)

private theorem leaf5091FlatSound : Sound leaf5091Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5091CertificateValid
    leaf5091InnerLogValid leaf5091CoversExact leaf5091LowerChecked

private noncomputable def leaf5092Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (17/64), chiHi := (69/256) }

private noncomputable def leaf5092Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742465/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715025408) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2192208593/2147483648) }, upper := { exponent := 1, mantissa := (8443/8192) } }, logOuter := sk236LogOuterCertificate, logK := sk236LogKCertificate, logChi := chi257LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432437759/137430050816) } }, logDArg := sk236LogDArgCertificate }

private noncomputable def leaf5092InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf5092LocalValidity :
    LeafFacts leaf5092Box leaf5092Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5092Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715025408) }) = true
      norm_num [leaf5092Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5092CertificateValid :
    WideCertificateValid leaf5092Box leaf5092Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk236ValidityFacts chi257ValidityFacts
    leaf5092LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5092CoverageChecked :
    coverageCheck (innerAD leaf5092Box) leaf5092InnerLog = true := by
  rfl'

private theorem leaf5092InnerLogValid :
    leaf5092InnerLog.Valid 8 (innerAD leaf5092Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf5092CoverageChecked

private noncomputable def leaf5092InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907343/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5092InputLogOnePlusV_eq :
    leaf5092InputLogOnePlusV = outerEnclosure 24
      (leaf5092Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5092RoundedFacts : LeafRoundedFacts 8
    leaf5092Certificate.logOnePlusV leaf5092InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5092InputLogOnePlusV_eq }

private noncomputable def leaf5092Inputs : Inputs :=
  inputsOfCaches globalInput sk236RoundedInputs
    chi257InputQChi innerPair116Input
    leaf5092InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5092LowerChecked :
    lowerCheck 24 leaf5092Box leaf5092Inputs = true := by
  rfl'

private theorem leaf5092CoversExact : CoversExact 8
    leaf5092Box leaf5092Certificate leaf5092InnerLog leaf5092Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk236RoundedFacts chi257RoundedFacts
    innerPair116RoundedFacts leaf5092RoundedFacts (by rfl)

private theorem leaf5092FlatSound : Sound leaf5092Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5092CertificateValid
    leaf5092InnerLogValid leaf5092CoversExact leaf5092LowerChecked

private noncomputable def leaf5093Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (251/64), chiLo := (69/256), chiHi := (35/128) }

private noncomputable def leaf5093Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742465/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714978816) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2204135417/2147483648) }, upper := { exponent := 1, mantissa := (16977/16384) } }, logOuter := sk235LogOuterCertificate, logK := sk235LogKCertificate, logChi := chi258LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432391167/137429957632) } }, logDArg := sk235LogDArgCertificate }

private noncomputable def leaf5093InnerLog : WideLogData :=
  innerPair327Data

set_option maxRecDepth 1000000 in
private theorem leaf5093LocalValidity :
    LeafFacts leaf5093Box leaf5093Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5093Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714978816) }) = true
      norm_num [leaf5093Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5093CertificateValid :
    WideCertificateValid leaf5093Box leaf5093Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk235ValidityFacts chi258ValidityFacts
    leaf5093LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5093CoverageChecked :
    coverageCheck (innerAD leaf5093Box) leaf5093InnerLog = true := by
  rfl'

private theorem leaf5093InnerLogValid :
    leaf5093InnerLog.Valid 8 (innerAD leaf5093Box) :=
  wideLogDataValid_of_cachedCheck endpoint87PositiveFacts
    endpoint86PositiveFacts.valid leaf5093CoverageChecked

private noncomputable def leaf5093InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814689/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5093InputLogOnePlusV_eq :
    leaf5093InputLogOnePlusV = outerEnclosure 24
      (leaf5093Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5093RoundedFacts : LeafRoundedFacts 8
    leaf5093Certificate.logOnePlusV leaf5093InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5093InputLogOnePlusV_eq }

private noncomputable def leaf5093Inputs : Inputs :=
  inputsOfCaches globalInput sk235RoundedInputs
    chi258InputQChi innerPair327Input
    leaf5093InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5093LowerChecked :
    lowerCheck 24 leaf5093Box leaf5093Inputs = true := by
  rfl'

private theorem leaf5093CoversExact : CoversExact 8
    leaf5093Box leaf5093Certificate leaf5093InnerLog leaf5093Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk235RoundedFacts chi258RoundedFacts
    innerPair327RoundedFacts leaf5093RoundedFacts (by rfl)

private theorem leaf5093FlatSound : Sound leaf5093Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5093CertificateValid
    leaf5093InnerLogValid leaf5093CoversExact leaf5093LowerChecked

private noncomputable def leaf5094Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (69/256), chiHi := (35/128) }

private noncomputable def leaf5094Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742467/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714960896) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2208657123/2147483648) }, upper := { exponent := 1, mantissa := (4253/4096) } }, logOuter := sk236LogOuterCertificate, logK := sk236LogKCertificate, logChi := chi258LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432373247/137429921792) } }, logDArg := sk236LogDArgCertificate }

private noncomputable def leaf5094InnerLog : WideLogData :=
  innerPair327Data

set_option maxRecDepth 1000000 in
private theorem leaf5094LocalValidity :
    LeafFacts leaf5094Box leaf5094Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5094Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714960896) }) = true
      norm_num [leaf5094Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5094CertificateValid :
    WideCertificateValid leaf5094Box leaf5094Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk236ValidityFacts chi258ValidityFacts
    leaf5094LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5094CoverageChecked :
    coverageCheck (innerAD leaf5094Box) leaf5094InnerLog = true := by
  rfl'

private theorem leaf5094InnerLogValid :
    leaf5094InnerLog.Valid 8 (innerAD leaf5094Box) :=
  wideLogDataValid_of_cachedCheck endpoint87PositiveFacts
    endpoint86PositiveFacts.valid leaf5094CoverageChecked

private noncomputable def leaf5094InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907345/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5094InputLogOnePlusV_eq :
    leaf5094InputLogOnePlusV = outerEnclosure 24
      (leaf5094Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5094RoundedFacts : LeafRoundedFacts 8
    leaf5094Certificate.logOnePlusV leaf5094InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5094InputLogOnePlusV_eq }

private noncomputable def leaf5094Inputs : Inputs :=
  inputsOfCaches globalInput sk236RoundedInputs
    chi258InputQChi innerPair327Input
    leaf5094InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5094LowerChecked :
    lowerCheck 24 leaf5094Box leaf5094Inputs = true := by
  rfl'

private theorem leaf5094CoversExact : CoversExact 8
    leaf5094Box leaf5094Certificate leaf5094InnerLog leaf5094Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk236RoundedFacts chi258RoundedFacts
    innerPair327RoundedFacts leaf5094RoundedFacts (by rfl)

private theorem leaf5094FlatSound : Sound leaf5094Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5094CertificateValid
    leaf5094InnerLogValid leaf5094CoversExact leaf5094LowerChecked

private noncomputable def leaf5095Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (249/64), chiLo := (35/128), chiHi := (71/256) }

private noncomputable def leaf5095Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742463/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714950912) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2211343939/2147483648) }, upper := { exponent := 1, mantissa := (34063/32768) } }, logOuter := sk233LogOuterCertificate, logK := sk233LogKCertificate, logChi := chi279LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432363263/137429901824) } }, logDArg := sk233LogDArgCertificate }

private noncomputable def leaf5095InnerLog : WideLogData :=
  innerPair329Data

set_option maxRecDepth 1000000 in
private theorem leaf5095LocalValidity :
    LeafFacts leaf5095Box leaf5095Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5095Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714950912) }) = true
      norm_num [leaf5095Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5095CertificateValid :
    WideCertificateValid leaf5095Box leaf5095Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk233ValidityFacts chi279ValidityFacts
    leaf5095LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5095CoverageChecked :
    coverageCheck (innerAD leaf5095Box) leaf5095InnerLog = true := by
  rfl'

private theorem leaf5095InnerLogValid :
    leaf5095InnerLog.Valid 8 (innerAD leaf5095Box) :=
  wideLogDataValid_of_cachedCheck endpoint87PositiveFacts
    endpoint284PositiveFacts.valid leaf5095CoverageChecked

private noncomputable def leaf5095InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629381/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5095InputLogOnePlusV_eq :
    leaf5095InputLogOnePlusV = outerEnclosure 24
      (leaf5095Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5095RoundedFacts : LeafRoundedFacts 8
    leaf5095Certificate.logOnePlusV leaf5095InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5095InputLogOnePlusV_eq }

private noncomputable def leaf5095Inputs : Inputs :=
  inputsOfCaches globalInput sk233RoundedInputs
    chi279InputQChi innerPair329Input
    leaf5095InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5095LowerChecked :
    lowerCheck 24 leaf5095Box leaf5095Inputs = true := by
  rfl'

private theorem leaf5095CoversExact : CoversExact 8
    leaf5095Box leaf5095Certificate leaf5095InnerLog leaf5095Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk233RoundedFacts chi279RoundedFacts
    innerPair329RoundedFacts leaf5095RoundedFacts (by rfl)

private theorem leaf5095FlatSound : Sound leaf5095Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5095CertificateValid
    leaf5095InnerLogValid leaf5095CoversExact leaf5095LowerChecked

private noncomputable def leaf5096Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (249/64), kHi := (125/32), chiLo := (35/128), chiHi := (71/256) }

private noncomputable def leaf5096Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742465/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714932736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2215931177/2147483648) }, upper := { exponent := 1, mantissa := (17067/16384) } }, logOuter := sk234LogOuterCertificate, logK := sk234LogKCertificate, logChi := chi279LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432345087/137429865472) } }, logDArg := sk234LogDArgCertificate }

private noncomputable def leaf5096InnerLog : WideLogData :=
  innerPair248Data

set_option maxRecDepth 1000000 in
private theorem leaf5096LocalValidity :
    LeafFacts leaf5096Box leaf5096Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5096Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714932736) }) = true
      norm_num [leaf5096Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5096CertificateValid :
    WideCertificateValid leaf5096Box leaf5096Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk234ValidityFacts chi279ValidityFacts
    leaf5096LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5096CoverageChecked :
    coverageCheck (innerAD leaf5096Box) leaf5096InnerLog = true := by
  rfl'

private theorem leaf5096InnerLogValid :
    leaf5096InnerLog.Valid 8 (innerAD leaf5096Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint284PositiveFacts.valid leaf5096CoverageChecked

private noncomputable def leaf5096InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629383/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5096InputLogOnePlusV_eq :
    leaf5096InputLogOnePlusV = outerEnclosure 24
      (leaf5096Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5096RoundedFacts : LeafRoundedFacts 8
    leaf5096Certificate.logOnePlusV leaf5096InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5096InputLogOnePlusV_eq }

private noncomputable def leaf5096Inputs : Inputs :=
  inputsOfCaches globalInput sk234RoundedInputs
    chi279InputQChi innerPair248Input
    leaf5096InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5096LowerChecked :
    lowerCheck 24 leaf5096Box leaf5096Inputs = true := by
  rfl'

private theorem leaf5096CoversExact : CoversExact 8
    leaf5096Box leaf5096Certificate leaf5096InnerLog leaf5096Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk234RoundedFacts chi279RoundedFacts
    innerPair248RoundedFacts leaf5096RoundedFacts (by rfl)

private theorem leaf5096FlatSound : Sound leaf5096Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5096CertificateValid
    leaf5096InnerLogValid leaf5096CoversExact leaf5096LowerChecked

private noncomputable def leaf5097Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (249/64), chiLo := (71/256), chiHi := (9/32) }

private noncomputable def leaf5097Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742465/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714887168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2227595873/2147483648) }, upper := { exponent := 1, mantissa := (4289/4096) } }, logOuter := sk233LogOuterCertificate, logK := sk233LogKCertificate, logChi := chi280LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432299519/137429774336) } }, logDArg := sk233LogDArgCertificate }

private noncomputable def leaf5097InnerLog : WideLogData :=
  innerPair247Data

set_option maxRecDepth 1000000 in
private theorem leaf5097LocalValidity :
    LeafFacts leaf5097Box leaf5097Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5097Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714887168) }) = true
      norm_num [leaf5097Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5097CertificateValid :
    WideCertificateValid leaf5097Box leaf5097Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk233ValidityFacts chi280ValidityFacts
    leaf5097LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5097CoverageChecked :
    coverageCheck (innerAD leaf5097Box) leaf5097InnerLog = true := by
  rfl'

private theorem leaf5097InnerLogValid :
    leaf5097InnerLog.Valid 8 (innerAD leaf5097Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint89PositiveFacts.valid leaf5097CoverageChecked

private noncomputable def leaf5097InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629389/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5097InputLogOnePlusV_eq :
    leaf5097InputLogOnePlusV = outerEnclosure 24
      (leaf5097Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5097RoundedFacts : LeafRoundedFacts 8
    leaf5097Certificate.logOnePlusV leaf5097InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5097InputLogOnePlusV_eq }

private noncomputable def leaf5097Inputs : Inputs :=
  inputsOfCaches globalInput sk233RoundedInputs
    chi280InputQChi innerPair247Input
    leaf5097InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5097LowerChecked :
    lowerCheck 24 leaf5097Box leaf5097Inputs = true := by
  rfl'

private theorem leaf5097CoversExact : CoversExact 8
    leaf5097Box leaf5097Certificate leaf5097InnerLog leaf5097Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk233RoundedFacts chi280RoundedFacts
    innerPair247RoundedFacts leaf5097RoundedFacts (by rfl)

private theorem leaf5097FlatSound : Sound leaf5097Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5097CertificateValid
    leaf5097InnerLogValid leaf5097CoversExact leaf5097LowerChecked

private noncomputable def leaf5098Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (249/64), kHi := (125/32), chiLo := (71/256), chiHi := (9/32) }

private noncomputable def leaf5098Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742467/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714868736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2232248643/2147483648) }, upper := { exponent := 1, mantissa := (2149/2048) } }, logOuter := sk234LogOuterCertificate, logK := sk234LogKCertificate, logChi := chi280LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432281087/137429737472) } }, logDArg := sk234LogDArgCertificate }

private noncomputable def leaf5098InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf5098LocalValidity :
    LeafFacts leaf5098Box leaf5098Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5098Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714868736) }) = true
      norm_num [leaf5098Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5098CertificateValid :
    WideCertificateValid leaf5098Box leaf5098Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk234ValidityFacts chi280ValidityFacts
    leaf5098LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5098CoverageChecked :
    coverageCheck (innerAD leaf5098Box) leaf5098InnerLog = true := by
  rfl'

private theorem leaf5098InnerLogValid :
    leaf5098InnerLog.Valid 8 (innerAD leaf5098Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf5098CoverageChecked

private noncomputable def leaf5098InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629391/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5098InputLogOnePlusV_eq :
    leaf5098InputLogOnePlusV = outerEnclosure 24
      (leaf5098Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5098RoundedFacts : LeafRoundedFacts 8
    leaf5098Certificate.logOnePlusV leaf5098InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5098InputLogOnePlusV_eq }

private noncomputable def leaf5098Inputs : Inputs :=
  inputsOfCaches globalInput sk234RoundedInputs
    chi280InputQChi innerPair242Input
    leaf5098InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5098LowerChecked :
    lowerCheck 24 leaf5098Box leaf5098Inputs = true := by
  rfl'

private theorem leaf5098CoversExact : CoversExact 8
    leaf5098Box leaf5098Certificate leaf5098InnerLog leaf5098Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk234RoundedFacts chi280RoundedFacts
    innerPair242RoundedFacts leaf5098RoundedFacts (by rfl)

private theorem leaf5098FlatSound : Sound leaf5098Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5098CertificateValid
    leaf5098InnerLogValid leaf5098CoversExact leaf5098LowerChecked

private noncomputable def leaf5099Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (251/64), chiLo := (35/128), chiHi := (71/256) }

private noncomputable def leaf5099Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742467/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22904971520) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2220518415/2147483648) }, upper := { exponent := 1, mantissa := (34205/32768) } }, logOuter := sk235LogOuterCertificate, logK := sk235LogKCertificate, logChi := chi279LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810775637/45809943040) } }, logDArg := sk235LogDArgCertificate }

private noncomputable def leaf5099InnerLog : WideLogData :=
  innerPair248Data

set_option maxRecDepth 1000000 in
private theorem leaf5099LocalValidity :
    LeafFacts leaf5099Box leaf5099Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5099Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22904971520) }) = true
      norm_num [leaf5099Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5099CertificateValid :
    WideCertificateValid leaf5099Box leaf5099Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk235ValidityFacts chi279ValidityFacts
    leaf5099LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5099CoverageChecked :
    coverageCheck (innerAD leaf5099Box) leaf5099InnerLog = true := by
  rfl'

private theorem leaf5099InnerLogValid :
    leaf5099InnerLog.Valid 8 (innerAD leaf5099Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint284PositiveFacts.valid leaf5099CoverageChecked

private noncomputable def leaf5099InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814693/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5099InputLogOnePlusV_eq :
    leaf5099InputLogOnePlusV = outerEnclosure 24
      (leaf5099Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5099RoundedFacts : LeafRoundedFacts 8
    leaf5099Certificate.logOnePlusV leaf5099InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5099InputLogOnePlusV_eq }

private noncomputable def leaf5099Inputs : Inputs :=
  inputsOfCaches globalInput sk235RoundedInputs
    chi279InputQChi innerPair248Input
    leaf5099InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5099LowerChecked :
    lowerCheck 24 leaf5099Box leaf5099Inputs = true := by
  rfl'

private theorem leaf5099CoversExact : CoversExact 8
    leaf5099Box leaf5099Certificate leaf5099InnerLog leaf5099Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk235RoundedFacts chi279RoundedFacts
    innerPair248RoundedFacts leaf5099RoundedFacts (by rfl)

private theorem leaf5099FlatSound : Sound leaf5099Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5099CertificateValid
    leaf5099InnerLogValid leaf5099CoversExact leaf5099LowerChecked

private noncomputable def leaf5100Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (35/128), chiHi := (71/256) }

private noncomputable def leaf5100Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742469/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714896384) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2225105653/2147483648) }, upper := { exponent := 1, mantissa := (8569/8192) } }, logOuter := sk236LogOuterCertificate, logK := sk236LogKCertificate, logChi := chi279LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432308735/137429792768) } }, logDArg := sk236LogDArgCertificate }

private noncomputable def leaf5100InnerLog : WideLogData :=
  innerPair248Data

set_option maxRecDepth 1000000 in
private theorem leaf5100LocalValidity :
    LeafFacts leaf5100Box leaf5100Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5100Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714896384) }) = true
      norm_num [leaf5100Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5100CertificateValid :
    WideCertificateValid leaf5100Box leaf5100Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk236ValidityFacts chi279ValidityFacts
    leaf5100LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5100CoverageChecked :
    coverageCheck (innerAD leaf5100Box) leaf5100InnerLog = true := by
  rfl'

private theorem leaf5100InnerLogValid :
    leaf5100InnerLog.Valid 8 (innerAD leaf5100Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint284PositiveFacts.valid leaf5100CoverageChecked

private noncomputable def leaf5100InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907347/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5100InputLogOnePlusV_eq :
    leaf5100InputLogOnePlusV = outerEnclosure 24
      (leaf5100Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5100RoundedFacts : LeafRoundedFacts 8
    leaf5100Certificate.logOnePlusV leaf5100InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5100InputLogOnePlusV_eq }

private noncomputable def leaf5100Inputs : Inputs :=
  inputsOfCaches globalInput sk236RoundedInputs
    chi279InputQChi innerPair248Input
    leaf5100InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5100LowerChecked :
    lowerCheck 24 leaf5100Box leaf5100Inputs = true := by
  rfl'

private theorem leaf5100CoversExact : CoversExact 8
    leaf5100Box leaf5100Certificate leaf5100InnerLog leaf5100Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk236RoundedFacts chi279RoundedFacts
    innerPair248RoundedFacts leaf5100RoundedFacts (by rfl)

private theorem leaf5100FlatSound : Sound leaf5100Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5100CertificateValid
    leaf5100InnerLogValid leaf5100CoversExact leaf5100LowerChecked

private noncomputable def leaf5101Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (251/64), chiLo := (71/256), chiHi := (9/32) }

private noncomputable def leaf5101Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742469/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714850304) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2236901413/2147483648) }, upper := { exponent := 1, mantissa := (4307/4096) } }, logOuter := sk235LogOuterCertificate, logK := sk235LogKCertificate, logChi := chi280LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432262655/137429700608) } }, logDArg := sk235LogDArgCertificate }

private noncomputable def leaf5101InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf5101LocalValidity :
    LeafFacts leaf5101Box leaf5101Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5101Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714850304) }) = true
      norm_num [leaf5101Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5101CertificateValid :
    WideCertificateValid leaf5101Box leaf5101Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk235ValidityFacts chi280ValidityFacts
    leaf5101LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5101CoverageChecked :
    coverageCheck (innerAD leaf5101Box) leaf5101InnerLog = true := by
  rfl'

private theorem leaf5101InnerLogValid :
    leaf5101InnerLog.Valid 8 (innerAD leaf5101Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf5101CoverageChecked

private noncomputable def leaf5101InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814697/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5101InputLogOnePlusV_eq :
    leaf5101InputLogOnePlusV = outerEnclosure 24
      (leaf5101Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5101RoundedFacts : LeafRoundedFacts 8
    leaf5101Certificate.logOnePlusV leaf5101InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5101InputLogOnePlusV_eq }

private noncomputable def leaf5101Inputs : Inputs :=
  inputsOfCaches globalInput sk235RoundedInputs
    chi280InputQChi innerPair242Input
    leaf5101InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5101LowerChecked :
    lowerCheck 24 leaf5101Box leaf5101Inputs = true := by
  rfl'

private theorem leaf5101CoversExact : CoversExact 8
    leaf5101Box leaf5101Certificate leaf5101InnerLog leaf5101Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk235RoundedFacts chi280RoundedFacts
    innerPair242RoundedFacts leaf5101RoundedFacts (by rfl)

private theorem leaf5101FlatSound : Sound leaf5101Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5101CertificateValid
    leaf5101InnerLogValid leaf5101CoversExact leaf5101LowerChecked

private noncomputable def leaf5102Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (71/256), chiHi := (9/32) }

private noncomputable def leaf5102Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742471/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714831872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2241554183/2147483648) }, upper := { exponent := 1, mantissa := (1079/1024) } }, logOuter := sk236LogOuterCertificate, logK := sk236LogKCertificate, logChi := chi280LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432244223/137429663744) } }, logDArg := sk236LogDArgCertificate }

private noncomputable def leaf5102InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf5102LocalValidity :
    LeafFacts leaf5102Box leaf5102Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5102Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714831872) }) = true
      norm_num [leaf5102Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5102CertificateValid :
    WideCertificateValid leaf5102Box leaf5102Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk236ValidityFacts chi280ValidityFacts
    leaf5102LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5102CoverageChecked :
    coverageCheck (innerAD leaf5102Box) leaf5102InnerLog = true := by
  rfl'

private theorem leaf5102InnerLogValid :
    leaf5102InnerLog.Valid 8 (innerAD leaf5102Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf5102CoverageChecked

private noncomputable def leaf5102InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907349/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5102InputLogOnePlusV_eq :
    leaf5102InputLogOnePlusV = outerEnclosure 24
      (leaf5102Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5102RoundedFacts : LeafRoundedFacts 8
    leaf5102Certificate.logOnePlusV leaf5102InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5102InputLogOnePlusV_eq }

private noncomputable def leaf5102Inputs : Inputs :=
  inputsOfCaches globalInput sk236RoundedInputs
    chi280InputQChi innerPair242Input
    leaf5102InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5102LowerChecked :
    lowerCheck 24 leaf5102Box leaf5102Inputs = true := by
  rfl'

private theorem leaf5102CoversExact : CoversExact 8
    leaf5102Box leaf5102Certificate leaf5102InnerLog leaf5102Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk236RoundedFacts chi280RoundedFacts
    innerPair242RoundedFacts leaf5102RoundedFacts (by rfl)

private theorem leaf5102FlatSound : Sound leaf5102Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5102CertificateValid
    leaf5102InnerLogValid leaf5102CoversExact leaf5102LowerChecked

private noncomputable def leaf5103Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (17/64), chiHi := (69/256) }

private noncomputable def leaf5103Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742467/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715007744) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2196664767/2147483648) }, upper := { exponent := 1, mantissa := (33841/32768) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi257LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432420095/137430015488) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf5103InnerLog : WideLogData :=
  innerPair311Data

set_option maxRecDepth 1000000 in
private theorem leaf5103LocalValidity :
    LeafFacts leaf5103Box leaf5103Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5103Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715007744) }) = true
      norm_num [leaf5103Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5103CertificateValid :
    WideCertificateValid leaf5103Box leaf5103Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi257ValidityFacts
    leaf5103LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5103CoverageChecked :
    coverageCheck (innerAD leaf5103Box) leaf5103InnerLog = true := by
  rfl'

private theorem leaf5103InnerLogValid :
    leaf5103InnerLog.Valid 8 (innerAD leaf5103Box) :=
  wideLogDataValid_of_cachedCheck endpoint82PositiveFacts
    endpoint86PositiveFacts.valid leaf5103CoverageChecked

private noncomputable def leaf5103InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814687/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5103InputLogOnePlusV_eq :
    leaf5103InputLogOnePlusV = outerEnclosure 24
      (leaf5103Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5103RoundedFacts : LeafRoundedFacts 8
    leaf5103Certificate.logOnePlusV leaf5103InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5103InputLogOnePlusV_eq }

private noncomputable def leaf5103Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi257InputQChi innerPair311Input
    leaf5103InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5103LowerChecked :
    lowerCheck 24 leaf5103Box leaf5103Inputs = true := by
  rfl'

private theorem leaf5103CoversExact : CoversExact 8
    leaf5103Box leaf5103Certificate leaf5103InnerLog leaf5103Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi257RoundedFacts
    innerPair311RoundedFacts leaf5103RoundedFacts (by rfl)

private theorem leaf5103FlatSound : Sound leaf5103Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5103CertificateValid
    leaf5103InnerLogValid leaf5103CoversExact leaf5103LowerChecked

private noncomputable def leaf5104Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (17/64), chiHi := (69/256) }

private noncomputable def leaf5104Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742469/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714990080) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2201120941/2147483648) }, upper := { exponent := 1, mantissa := (16955/16384) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi257LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432402431/137429980160) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf5104InnerLog : WideLogData :=
  innerPair327Data

set_option maxRecDepth 1000000 in
private theorem leaf5104LocalValidity :
    LeafFacts leaf5104Box leaf5104Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5104Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714990080) }) = true
      norm_num [leaf5104Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5104CertificateValid :
    WideCertificateValid leaf5104Box leaf5104Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi257ValidityFacts
    leaf5104LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5104CoverageChecked :
    coverageCheck (innerAD leaf5104Box) leaf5104InnerLog = true := by
  rfl'

private theorem leaf5104InnerLogValid :
    leaf5104InnerLog.Valid 8 (innerAD leaf5104Box) :=
  wideLogDataValid_of_cachedCheck endpoint87PositiveFacts
    endpoint86PositiveFacts.valid leaf5104CoverageChecked

private noncomputable def leaf5104InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (181709/262144) }

set_option maxRecDepth 1000000 in
private theorem leaf5104InputLogOnePlusV_eq :
    leaf5104InputLogOnePlusV = outerEnclosure 24
      (leaf5104Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5104RoundedFacts : LeafRoundedFacts 8
    leaf5104Certificate.logOnePlusV leaf5104InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5104InputLogOnePlusV_eq }

private noncomputable def leaf5104Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi257InputQChi innerPair327Input
    leaf5104InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5104LowerChecked :
    lowerCheck 24 leaf5104Box leaf5104Inputs = true := by
  rfl'

private theorem leaf5104CoversExact : CoversExact 8
    leaf5104Box leaf5104Certificate leaf5104InnerLog leaf5104Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi257RoundedFacts
    innerPair327RoundedFacts leaf5104RoundedFacts (by rfl)

private theorem leaf5104FlatSound : Sound leaf5104Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5104CertificateValid
    leaf5104InnerLogValid leaf5104CoversExact leaf5104LowerChecked

private noncomputable def leaf5105Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (69/256), chiHi := (35/128) }

private noncomputable def leaf5105Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742469/1073741824) }, vSqrt := { lower := (8191/8192), upper := (7635268039/7634993664) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2213178829/2147483648) }, upper := { exponent := 1, mantissa := (17047/16384) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi258LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (15270261703/15269987328) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf5105InnerLog : WideLogData :=
  innerPair329Data

set_option maxRecDepth 1000000 in
private theorem leaf5105LocalValidity :
    LeafFacts leaf5105Box leaf5105Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5105Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (7635268039/7634993664) }) = true
      norm_num [leaf5105Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5105CertificateValid :
    WideCertificateValid leaf5105Box leaf5105Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi258ValidityFacts
    leaf5105LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5105CoverageChecked :
    coverageCheck (innerAD leaf5105Box) leaf5105InnerLog = true := by
  rfl'

private theorem leaf5105InnerLogValid :
    leaf5105InnerLog.Valid 8 (innerAD leaf5105Box) :=
  wideLogDataValid_of_cachedCheck endpoint87PositiveFacts
    endpoint284PositiveFacts.valid leaf5105CoverageChecked

private noncomputable def leaf5105InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814691/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5105InputLogOnePlusV_eq :
    leaf5105InputLogOnePlusV = outerEnclosure 24
      (leaf5105Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5105RoundedFacts : LeafRoundedFacts 8
    leaf5105Certificate.logOnePlusV leaf5105InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5105InputLogOnePlusV_eq }

private noncomputable def leaf5105Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi258InputQChi innerPair329Input
    leaf5105InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5105LowerChecked :
    lowerCheck 24 leaf5105Box leaf5105Inputs = true := by
  rfl'

private theorem leaf5105CoversExact : CoversExact 8
    leaf5105Box leaf5105Certificate leaf5105InnerLog leaf5105Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi258RoundedFacts
    innerPair329RoundedFacts leaf5105RoundedFacts (by rfl)

private theorem leaf5105FlatSound : Sound leaf5105Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5105CertificateValid
    leaf5105InnerLogValid leaf5105CoversExact leaf5105LowerChecked

private noncomputable def leaf5106Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (69/256), chiHi := (35/128) }

private noncomputable def leaf5106Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742471/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714925056) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2217700535/2147483648) }, upper := { exponent := 1, mantissa := (8541/8192) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi258LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432337407/137429850112) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf5106InnerLog : WideLogData :=
  innerPair248Data

set_option maxRecDepth 1000000 in
private theorem leaf5106LocalValidity :
    LeafFacts leaf5106Box leaf5106Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5106Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714925056) }) = true
      norm_num [leaf5106Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5106CertificateValid :
    WideCertificateValid leaf5106Box leaf5106Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi258ValidityFacts
    leaf5106LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5106CoverageChecked :
    coverageCheck (innerAD leaf5106Box) leaf5106InnerLog = true := by
  rfl'

private theorem leaf5106InnerLogValid :
    leaf5106InnerLog.Valid 8 (innerAD leaf5106Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint284PositiveFacts.valid leaf5106CoverageChecked

private noncomputable def leaf5106InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453673/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5106InputLogOnePlusV_eq :
    leaf5106InputLogOnePlusV = outerEnclosure 24
      (leaf5106Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5106RoundedFacts : LeafRoundedFacts 8
    leaf5106Certificate.logOnePlusV leaf5106InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5106InputLogOnePlusV_eq }

private noncomputable def leaf5106Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi258InputQChi innerPair248Input
    leaf5106InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5106LowerChecked :
    lowerCheck 24 leaf5106Box leaf5106Inputs = true := by
  rfl'

private theorem leaf5106CoversExact : CoversExact 8
    leaf5106Box leaf5106Certificate leaf5106InnerLog leaf5106Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi258RoundedFacts
    innerPair248RoundedFacts leaf5106RoundedFacts (by rfl)

private theorem leaf5106FlatSound : Sound leaf5106Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5106CertificateValid
    leaf5106InnerLogValid leaf5106CoversExact leaf5106LowerChecked

private noncomputable def leaf5107Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (17/64), chiHi := (69/256) }

private noncomputable def leaf5107Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742471/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714972416) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2205577115/2147483648) }, upper := { exponent := 1, mantissa := (33979/32768) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi257LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432384767/137429944832) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf5107InnerLog : WideLogData :=
  innerPair327Data

set_option maxRecDepth 1000000 in
private theorem leaf5107LocalValidity :
    LeafFacts leaf5107Box leaf5107Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5107Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714972416) }) = true
      norm_num [leaf5107Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5107CertificateValid :
    WideCertificateValid leaf5107Box leaf5107Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi257ValidityFacts
    leaf5107LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5107CoverageChecked :
    coverageCheck (innerAD leaf5107Box) leaf5107InnerLog = true := by
  rfl'

private theorem leaf5107InnerLogValid :
    leaf5107InnerLog.Valid 8 (innerAD leaf5107Box) :=
  wideLogDataValid_of_cachedCheck endpoint87PositiveFacts
    endpoint86PositiveFacts.valid leaf5107CoverageChecked

private noncomputable def leaf5107InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629379/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5107InputLogOnePlusV_eq :
    leaf5107InputLogOnePlusV = outerEnclosure 24
      (leaf5107Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5107RoundedFacts : LeafRoundedFacts 8
    leaf5107Certificate.logOnePlusV leaf5107InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5107InputLogOnePlusV_eq }

private noncomputable def leaf5107Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi257InputQChi innerPair327Input
    leaf5107InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5107LowerChecked :
    lowerCheck 24 leaf5107Box leaf5107Inputs = true := by
  rfl'

private theorem leaf5107CoversExact : CoversExact 8
    leaf5107Box leaf5107Certificate leaf5107InnerLog leaf5107Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi257RoundedFacts
    innerPair327RoundedFacts leaf5107RoundedFacts (by rfl)

private theorem leaf5107FlatSound : Sound leaf5107Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5107CertificateValid
    leaf5107InnerLogValid leaf5107CoversExact leaf5107LowerChecked

private noncomputable def leaf5108Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (17/64), chiHi := (69/256) }

private noncomputable def leaf5108Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742473/1073741824) }, vSqrt := { lower := (65527/65536), upper := (68717412351/68714954752) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2210033289/2147483648) }, upper := { exponent := 1, mantissa := (133/128) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi257LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (137432367103/137429909504) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf5108InnerLog : WideLogData :=
  innerPair327Data

set_option maxRecDepth 1000000 in
private theorem leaf5108LocalValidity :
    LeafFacts leaf5108Box leaf5108Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5108Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (68717412351/68714954752) }) = true
      norm_num [leaf5108Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5108CertificateValid :
    WideCertificateValid leaf5108Box leaf5108Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi257ValidityFacts
    leaf5108LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5108CoverageChecked :
    coverageCheck (innerAD leaf5108Box) leaf5108InnerLog = true := by
  rfl'

private theorem leaf5108InnerLogValid :
    leaf5108InnerLog.Valid 8 (innerAD leaf5108Box) :=
  wideLogDataValid_of_cachedCheck endpoint87PositiveFacts
    endpoint86PositiveFacts.valid leaf5108CoverageChecked

private noncomputable def leaf5108InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629381/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5108InputLogOnePlusV_eq :
    leaf5108InputLogOnePlusV = outerEnclosure 24
      (leaf5108Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5108RoundedFacts : LeafRoundedFacts 8
    leaf5108Certificate.logOnePlusV leaf5108InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5108InputLogOnePlusV_eq }

private noncomputable def leaf5108Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi257InputQChi innerPair327Input
    leaf5108InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5108LowerChecked :
    lowerCheck 24 leaf5108Box leaf5108Inputs = true := by
  rfl'

private theorem leaf5108CoversExact : CoversExact 8
    leaf5108Box leaf5108Certificate leaf5108InnerLog leaf5108Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi257RoundedFacts
    innerPair327RoundedFacts leaf5108RoundedFacts (by rfl)

private theorem leaf5108FlatSound : Sound leaf5108Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5108CertificateValid
    leaf5108InnerLogValid leaf5108CoversExact leaf5108LowerChecked

private noncomputable def leaf5109Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (69/256), chiHi := (35/128) }

private noncomputable def leaf5109Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742473/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714907136) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2222222241/2147483648) }, upper := { exponent := 1, mantissa := (17117/16384) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi258LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432319487/137429814272) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf5109InnerLog : WideLogData :=
  innerPair248Data

set_option maxRecDepth 1000000 in
private theorem leaf5109LocalValidity :
    LeafFacts leaf5109Box leaf5109Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5109Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714907136) }) = true
      norm_num [leaf5109Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5109CertificateValid :
    WideCertificateValid leaf5109Box leaf5109Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi258ValidityFacts
    leaf5109LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5109CoverageChecked :
    coverageCheck (innerAD leaf5109Box) leaf5109InnerLog = true := by
  rfl'

private theorem leaf5109InnerLogValid :
    leaf5109InnerLog.Valid 8 (innerAD leaf5109Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint284PositiveFacts.valid leaf5109CoverageChecked

private noncomputable def leaf5109InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629387/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5109InputLogOnePlusV_eq :
    leaf5109InputLogOnePlusV = outerEnclosure 24
      (leaf5109Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5109RoundedFacts : LeafRoundedFacts 8
    leaf5109Certificate.logOnePlusV leaf5109InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5109InputLogOnePlusV_eq }

private noncomputable def leaf5109Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi258InputQChi innerPair248Input
    leaf5109InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5109LowerChecked :
    lowerCheck 24 leaf5109Box leaf5109Inputs = true := by
  rfl'

private theorem leaf5109CoversExact : CoversExact 8
    leaf5109Box leaf5109Certificate leaf5109InnerLog leaf5109Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi258RoundedFacts
    innerPair248RoundedFacts leaf5109RoundedFacts (by rfl)

private theorem leaf5109FlatSound : Sound leaf5109Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5109CertificateValid
    leaf5109InnerLogValid leaf5109CoversExact leaf5109LowerChecked

private noncomputable def leaf5110Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (69/256), chiHi := (35/128) }

private noncomputable def leaf5110Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742475/1073741824) }, vSqrt := { lower := (65527/65536), upper := (22905804117/22904963072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2226743947/2147483648) }, upper := { exponent := 1, mantissa := (67/64) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi258LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (45810767189/45809926144) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf5110InnerLog : WideLogData :=
  innerPair248Data

set_option maxRecDepth 1000000 in
private theorem leaf5110LocalValidity :
    LeafFacts leaf5110Box leaf5110Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5110Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (22905804117/22904963072) }) = true
      norm_num [leaf5110Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5110CertificateValid :
    WideCertificateValid leaf5110Box leaf5110Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi258ValidityFacts
    leaf5110LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5110CoverageChecked :
    coverageCheck (innerAD leaf5110Box) leaf5110InnerLog = true := by
  rfl'

private theorem leaf5110InnerLogValid :
    leaf5110InnerLog.Valid 8 (innerAD leaf5110Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint284PositiveFacts.valid leaf5110CoverageChecked

private noncomputable def leaf5110InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629389/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5110InputLogOnePlusV_eq :
    leaf5110InputLogOnePlusV = outerEnclosure 24
      (leaf5110Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5110RoundedFacts : LeafRoundedFacts 8
    leaf5110Certificate.logOnePlusV leaf5110InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5110InputLogOnePlusV_eq }

private noncomputable def leaf5110Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi258InputQChi innerPair248Input
    leaf5110InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5110LowerChecked :
    lowerCheck 24 leaf5110Box leaf5110Inputs = true := by
  rfl'

private theorem leaf5110CoversExact : CoversExact 8
    leaf5110Box leaf5110Certificate leaf5110InnerLog leaf5110Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi258RoundedFacts
    innerPair248RoundedFacts leaf5110RoundedFacts (by rfl)

private theorem leaf5110FlatSound : Sound leaf5110Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5110CertificateValid
    leaf5110InnerLogValid leaf5110CoversExact leaf5110LowerChecked

private noncomputable def leaf5111Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (35/128), chiHi := (71/256) }

private noncomputable def leaf5111Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742471/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714878208) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2229692891/2147483648) }, upper := { exponent := 1, mantissa := (34347/32768) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi279LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432290559/137429756416) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf5111InnerLog : WideLogData :=
  innerPair247Data

set_option maxRecDepth 1000000 in
private theorem leaf5111LocalValidity :
    LeafFacts leaf5111Box leaf5111Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5111Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714878208) }) = true
      norm_num [leaf5111Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5111CertificateValid :
    WideCertificateValid leaf5111Box leaf5111Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi279ValidityFacts
    leaf5111LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5111CoverageChecked :
    coverageCheck (innerAD leaf5111Box) leaf5111InnerLog = true := by
  rfl'

private theorem leaf5111InnerLogValid :
    leaf5111InnerLog.Valid 8 (innerAD leaf5111Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint89PositiveFacts.valid leaf5111CoverageChecked

private noncomputable def leaf5111InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814695/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5111InputLogOnePlusV_eq :
    leaf5111InputLogOnePlusV = outerEnclosure 24
      (leaf5111Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5111RoundedFacts : LeafRoundedFacts 8
    leaf5111Certificate.logOnePlusV leaf5111InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5111InputLogOnePlusV_eq }

private noncomputable def leaf5111Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi279InputQChi innerPair247Input
    leaf5111InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5111LowerChecked :
    lowerCheck 24 leaf5111Box leaf5111Inputs = true := by
  rfl'

private theorem leaf5111CoversExact : CoversExact 8
    leaf5111Box leaf5111Certificate leaf5111InnerLog leaf5111Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi279RoundedFacts
    innerPair247RoundedFacts leaf5111RoundedFacts (by rfl)

private theorem leaf5111FlatSound : Sound leaf5111Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5111CertificateValid
    leaf5111InnerLogValid leaf5111CoversExact leaf5111LowerChecked

private noncomputable def leaf5112Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (35/128), chiHi := (71/256) }

private noncomputable def leaf5112Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742473/1073741824) }, vSqrt := { lower := (8191/8192), upper := (1090752577/1090712064) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2234280129/2147483648) }, upper := { exponent := 1, mantissa := (17209/16384) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi279LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (2181464641/2181424128) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf5112InnerLog : WideLogData :=
  innerPair323Data

set_option maxRecDepth 1000000 in
private theorem leaf5112LocalValidity :
    LeafFacts leaf5112Box leaf5112Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5112Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (1090752577/1090712064) }) = true
      norm_num [leaf5112Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5112CertificateValid :
    WideCertificateValid leaf5112Box leaf5112Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi279ValidityFacts
    leaf5112LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5112CoverageChecked :
    coverageCheck (innerAD leaf5112Box) leaf5112InnerLog = true := by
  rfl'

private theorem leaf5112InnerLogValid :
    leaf5112InnerLog.Valid 8 (innerAD leaf5112Box) :=
  wideLogDataValid_of_cachedCheck endpoint86PositiveFacts
    endpoint89PositiveFacts.valid leaf5112CoverageChecked

private noncomputable def leaf5112InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726837/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf5112InputLogOnePlusV_eq :
    leaf5112InputLogOnePlusV = outerEnclosure 24
      (leaf5112Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5112RoundedFacts : LeafRoundedFacts 8
    leaf5112Certificate.logOnePlusV leaf5112InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5112InputLogOnePlusV_eq }

private noncomputable def leaf5112Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi279InputQChi innerPair323Input
    leaf5112InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5112LowerChecked :
    lowerCheck 24 leaf5112Box leaf5112Inputs = true := by
  rfl'

private theorem leaf5112CoversExact : CoversExact 8
    leaf5112Box leaf5112Certificate leaf5112InnerLog leaf5112Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi279RoundedFacts
    innerPair323RoundedFacts leaf5112RoundedFacts (by rfl)

private theorem leaf5112FlatSound : Sound leaf5112Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5112CertificateValid
    leaf5112InnerLogValid leaf5112CoversExact leaf5112LowerChecked

private noncomputable def leaf5113Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (71/256), chiHi := (9/32) }

private noncomputable def leaf5113Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742473/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9816773193/9816401920) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2246206953/2147483648) }, upper := { exponent := 1, mantissa := (4325/4096) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi280LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (19633175113/19632803840) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf5113InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf5113LocalValidity :
    LeafFacts leaf5113Box leaf5113Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5113Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9816773193/9816401920) }) = true
      norm_num [leaf5113Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5113CertificateValid :
    WideCertificateValid leaf5113Box leaf5113Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi280ValidityFacts
    leaf5113LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5113CoverageChecked :
    coverageCheck (innerAD leaf5113Box) leaf5113InnerLog = true := by
  rfl'

private theorem leaf5113InnerLogValid :
    leaf5113InnerLog.Valid 8 (innerAD leaf5113Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf5113CoverageChecked

private noncomputable def leaf5113InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814699/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5113InputLogOnePlusV_eq :
    leaf5113InputLogOnePlusV = outerEnclosure 24
      (leaf5113Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5113RoundedFacts : LeafRoundedFacts 8
    leaf5113Certificate.logOnePlusV leaf5113InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5113InputLogOnePlusV_eq }

private noncomputable def leaf5113Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi280InputQChi innerPair242Input
    leaf5113InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5113LowerChecked :
    lowerCheck 24 leaf5113Box leaf5113Inputs = true := by
  rfl'

private theorem leaf5113CoversExact : CoversExact 8
    leaf5113Box leaf5113Certificate leaf5113InnerLog leaf5113Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi280RoundedFacts
    innerPair242RoundedFacts leaf5113RoundedFacts (by rfl)

private theorem leaf5113FlatSound : Sound leaf5113Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5113CertificateValid
    leaf5113InnerLogValid leaf5113CoversExact leaf5113LowerChecked

private noncomputable def leaf5114Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (71/256), chiHi := (9/32) }

private noncomputable def leaf5114Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742475/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714795008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2250859723/2147483648) }, upper := { exponent := 1, mantissa := (2167/2048) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi280LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432207359/137429590016) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf5114InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf5114LocalValidity :
    LeafFacts leaf5114Box leaf5114Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5114Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714795008) }) = true
      norm_num [leaf5114Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5114CertificateValid :
    WideCertificateValid leaf5114Box leaf5114Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi280ValidityFacts
    leaf5114LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5114CoverageChecked :
    coverageCheck (innerAD leaf5114Box) leaf5114InnerLog = true := by
  rfl'

private theorem leaf5114InnerLogValid :
    leaf5114InnerLog.Valid 8 (innerAD leaf5114Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf5114CoverageChecked

private noncomputable def leaf5114InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453675/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5114InputLogOnePlusV_eq :
    leaf5114InputLogOnePlusV = outerEnclosure 24
      (leaf5114Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5114RoundedFacts : LeafRoundedFacts 8
    leaf5114Certificate.logOnePlusV leaf5114InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5114InputLogOnePlusV_eq }

private noncomputable def leaf5114Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi280InputQChi innerPair242Input
    leaf5114InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5114LowerChecked :
    lowerCheck 24 leaf5114Box leaf5114Inputs = true := by
  rfl'

private theorem leaf5114CoversExact : CoversExact 8
    leaf5114Box leaf5114Certificate leaf5114InnerLog leaf5114Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi280RoundedFacts
    innerPair242RoundedFacts leaf5114RoundedFacts (by rfl)

private theorem leaf5114FlatSound : Sound leaf5114Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5114CertificateValid
    leaf5114InnerLogValid leaf5114CoversExact leaf5114LowerChecked

private noncomputable def leaf5115Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (35/128), chiHi := (71/256) }

private noncomputable def leaf5115Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742475/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714841856) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2238867367/2147483648) }, upper := { exponent := 1, mantissa := (34489/32768) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi279LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432254207/137429683712) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf5115InnerLog : WideLogData :=
  innerPair323Data

set_option maxRecDepth 1000000 in
private theorem leaf5115LocalValidity :
    LeafFacts leaf5115Box leaf5115Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5115Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714841856) }) = true
      norm_num [leaf5115Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5115CertificateValid :
    WideCertificateValid leaf5115Box leaf5115Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi279ValidityFacts
    leaf5115LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5115CoverageChecked :
    coverageCheck (innerAD leaf5115Box) leaf5115InnerLog = true := by
  rfl'

private theorem leaf5115InnerLogValid :
    leaf5115InnerLog.Valid 8 (innerAD leaf5115Box) :=
  wideLogDataValid_of_cachedCheck endpoint86PositiveFacts
    endpoint89PositiveFacts.valid leaf5115CoverageChecked

private noncomputable def leaf5115InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629395/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5115InputLogOnePlusV_eq :
    leaf5115InputLogOnePlusV = outerEnclosure 24
      (leaf5115Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5115RoundedFacts : LeafRoundedFacts 8
    leaf5115Certificate.logOnePlusV leaf5115InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5115InputLogOnePlusV_eq }

private noncomputable def leaf5115Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi279InputQChi innerPair323Input
    leaf5115InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5115LowerChecked :
    lowerCheck 24 leaf5115Box leaf5115Inputs = true := by
  rfl'

private theorem leaf5115CoversExact : CoversExact 8
    leaf5115Box leaf5115Certificate leaf5115InnerLog leaf5115Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi279RoundedFacts
    innerPair323RoundedFacts leaf5115RoundedFacts (by rfl)

private theorem leaf5115FlatSound : Sound leaf5115Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5115CertificateValid
    leaf5115InnerLogValid leaf5115CoversExact leaf5115LowerChecked

private noncomputable def leaf5116Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (35/128), chiHi := (71/256) }

private noncomputable def leaf5116Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742477/1073741824) }, vSqrt := { lower := (65527/65536), upper := (68717412351/68714823680) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2243454605/2147483648) }, upper := { exponent := 1, mantissa := (135/128) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi279LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (137432236031/137429647360) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf5116InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf5116LocalValidity :
    LeafFacts leaf5116Box leaf5116Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5116Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (68717412351/68714823680) }) = true
      norm_num [leaf5116Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5116CertificateValid :
    WideCertificateValid leaf5116Box leaf5116Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi279ValidityFacts
    leaf5116LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5116CoverageChecked :
    coverageCheck (innerAD leaf5116Box) leaf5116InnerLog = true := by
  rfl'

private theorem leaf5116InnerLogValid :
    leaf5116InnerLog.Valid 8 (innerAD leaf5116Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf5116CoverageChecked

private noncomputable def leaf5116InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629397/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5116InputLogOnePlusV_eq :
    leaf5116InputLogOnePlusV = outerEnclosure 24
      (leaf5116Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5116RoundedFacts : LeafRoundedFacts 8
    leaf5116Certificate.logOnePlusV leaf5116InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5116InputLogOnePlusV_eq }

private noncomputable def leaf5116Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi279InputQChi innerPair242Input
    leaf5116InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5116LowerChecked :
    lowerCheck 24 leaf5116Box leaf5116Inputs = true := by
  rfl'

private theorem leaf5116CoversExact : CoversExact 8
    leaf5116Box leaf5116Certificate leaf5116InnerLog leaf5116Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi279RoundedFacts
    innerPair242RoundedFacts leaf5116RoundedFacts (by rfl)

private theorem leaf5116FlatSound : Sound leaf5116Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5116CertificateValid
    leaf5116InnerLogValid leaf5116CoversExact leaf5116LowerChecked

private noncomputable def leaf5117Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (71/256), chiHi := (9/32) }

private noncomputable def leaf5117Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742477/1073741824) }, vSqrt := { lower := (8191/8192), upper := (2216690721/2216605696) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2255512493/2147483648) }, upper := { exponent := 1, mantissa := (4343/4096) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi280LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (4433296417/4433211392) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf5117InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf5117LocalValidity :
    LeafFacts leaf5117Box leaf5117Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5117Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (2216690721/2216605696) }) = true
      norm_num [leaf5117Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5117CertificateValid :
    WideCertificateValid leaf5117Box leaf5117Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi280ValidityFacts
    leaf5117LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5117CoverageChecked :
    coverageCheck (innerAD leaf5117Box) leaf5117InnerLog = true := by
  rfl'

private theorem leaf5117InnerLogValid :
    leaf5117InnerLog.Valid 8 (innerAD leaf5117Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf5117CoverageChecked

private noncomputable def leaf5117InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629403/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5117InputLogOnePlusV_eq :
    leaf5117InputLogOnePlusV = outerEnclosure 24
      (leaf5117Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5117RoundedFacts : LeafRoundedFacts 8
    leaf5117Certificate.logOnePlusV leaf5117InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5117InputLogOnePlusV_eq }

private noncomputable def leaf5117Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi280InputQChi innerPair242Input
    leaf5117InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5117LowerChecked :
    lowerCheck 24 leaf5117Box leaf5117Inputs = true := by
  rfl'

private theorem leaf5117CoversExact : CoversExact 8
    leaf5117Box leaf5117Certificate leaf5117InnerLog leaf5117Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi280RoundedFacts
    innerPair242RoundedFacts leaf5117RoundedFacts (by rfl)

private theorem leaf5117FlatSound : Sound leaf5117Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5117CertificateValid
    leaf5117InnerLogValid leaf5117CoversExact leaf5117LowerChecked

private noncomputable def leaf5118Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (71/256), chiHi := (9/32) }

private noncomputable def leaf5118Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742479/1073741824) }, vSqrt := { lower := (65527/65536), upper := (68717412351/68714758144) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2260165263/2147483648) }, upper := { exponent := 1, mantissa := (17/16) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi280LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (137432170495/137429516288) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf5118InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf5118LocalValidity :
    LeafFacts leaf5118Box leaf5118Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5118Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (68717412351/68714758144) }) = true
      norm_num [leaf5118Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5118CertificateValid :
    WideCertificateValid leaf5118Box leaf5118Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi280ValidityFacts
    leaf5118LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5118CoverageChecked :
    coverageCheck (innerAD leaf5118Box) leaf5118InnerLog = true := by
  rfl'

private theorem leaf5118InnerLogValid :
    leaf5118InnerLog.Valid 8 (innerAD leaf5118Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf5118CoverageChecked

private noncomputable def leaf5118InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629405/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5118InputLogOnePlusV_eq :
    leaf5118InputLogOnePlusV = outerEnclosure 24
      (leaf5118Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5118RoundedFacts : LeafRoundedFacts 8
    leaf5118Certificate.logOnePlusV leaf5118InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5118InputLogOnePlusV_eq }

private noncomputable def leaf5118Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi280InputQChi innerPair242Input
    leaf5118InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5118LowerChecked :
    lowerCheck 24 leaf5118Box leaf5118Inputs = true := by
  rfl'

private theorem leaf5118CoversExact : CoversExact 8
    leaf5118Box leaf5118Certificate leaf5118InnerLog leaf5118Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi280RoundedFacts
    innerPair242RoundedFacts leaf5118RoundedFacts (by rfl)

private theorem leaf5118FlatSound : Sound leaf5118Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5118CertificateValid
    leaf5118InnerLogValid leaf5118CoversExact leaf5118LowerChecked

private noncomputable def component103Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (1/4), chiHi := (65/256) }

set_option maxRecDepth 1000000 in
private theorem component103Node0_sound : Sound component103Node0Box :=
  sound_of_literal_split component103Node0Box leaf5055Box leaf5056Box
    .k (249/64) (by rfl) (by rfl)
    leaf5055FlatSound leaf5056FlatSound

private noncomputable def component103Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (65/256), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component103Node1_sound : Sound component103Node1Box :=
  sound_of_literal_split component103Node1Box leaf5057Box leaf5058Box
    .k (249/64) (by rfl) (by rfl)
    leaf5057FlatSound leaf5058FlatSound

private noncomputable def component103Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (1/4), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component103Node2_sound : Sound component103Node2Box :=
  sound_of_literal_split component103Node2Box component103Node0Box component103Node1Box
    .chi (65/256) (by rfl) (by rfl)
    component103Node0_sound component103Node1_sound

private noncomputable def component103Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (1/4), chiHi := (65/256) }

set_option maxRecDepth 1000000 in
private theorem component103Node3_sound : Sound component103Node3Box :=
  sound_of_literal_split component103Node3Box leaf5059Box leaf5060Box
    .k (251/64) (by rfl) (by rfl)
    leaf5059FlatSound leaf5060FlatSound

private noncomputable def component103Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (65/256), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component103Node4_sound : Sound component103Node4Box :=
  sound_of_literal_split component103Node4Box leaf5061Box leaf5062Box
    .k (251/64) (by rfl) (by rfl)
    leaf5061FlatSound leaf5062FlatSound

private noncomputable def component103Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (1/4), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component103Node5_sound : Sound component103Node5Box :=
  sound_of_literal_split component103Node5Box component103Node3Box component103Node4Box
    .chi (65/256) (by rfl) (by rfl)
    component103Node3_sound component103Node4_sound

private noncomputable def component103Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (1/4), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component103Node6_sound : Sound component103Node6Box :=
  sound_of_literal_split component103Node6Box component103Node2Box component103Node5Box
    .k (125/32) (by rfl) (by rfl)
    component103Node2_sound component103Node5_sound

private noncomputable def component103Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (33/128), chiHi := (67/256) }

set_option maxRecDepth 1000000 in
private theorem component103Node7_sound : Sound component103Node7Box :=
  sound_of_literal_split component103Node7Box leaf5063Box leaf5064Box
    .k (249/64) (by rfl) (by rfl)
    leaf5063FlatSound leaf5064FlatSound

private noncomputable def component103Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (67/256), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component103Node8_sound : Sound component103Node8Box :=
  sound_of_literal_split component103Node8Box leaf5065Box leaf5066Box
    .k (249/64) (by rfl) (by rfl)
    leaf5065FlatSound leaf5066FlatSound

private noncomputable def component103Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (33/128), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component103Node9_sound : Sound component103Node9Box :=
  sound_of_literal_split component103Node9Box component103Node7Box component103Node8Box
    .chi (67/256) (by rfl) (by rfl)
    component103Node7_sound component103Node8_sound

private noncomputable def component103Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (33/128), chiHi := (67/256) }

set_option maxRecDepth 1000000 in
private theorem component103Node10_sound : Sound component103Node10Box :=
  sound_of_literal_split component103Node10Box leaf5067Box leaf5068Box
    .k (251/64) (by rfl) (by rfl)
    leaf5067FlatSound leaf5068FlatSound

private noncomputable def component103Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (67/256), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component103Node11_sound : Sound component103Node11Box :=
  sound_of_literal_split component103Node11Box leaf5069Box leaf5070Box
    .k (251/64) (by rfl) (by rfl)
    leaf5069FlatSound leaf5070FlatSound

private noncomputable def component103Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (33/128), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component103Node12_sound : Sound component103Node12Box :=
  sound_of_literal_split component103Node12Box component103Node10Box component103Node11Box
    .chi (67/256) (by rfl) (by rfl)
    component103Node10_sound component103Node11_sound

private noncomputable def component103Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (33/128), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component103Node13_sound : Sound component103Node13Box :=
  sound_of_literal_split component103Node13Box component103Node9Box component103Node12Box
    .k (125/32) (by rfl) (by rfl)
    component103Node9_sound component103Node12_sound

private noncomputable def component103Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component103Node14_sound : Sound component103Node14Box :=
  sound_of_literal_split component103Node14Box component103Node6Box component103Node13Box
    .chi (33/128) (by rfl) (by rfl)
    component103Node6_sound component103Node13_sound

private noncomputable def component103Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (1/4), chiHi := (65/256) }

set_option maxRecDepth 1000000 in
private theorem component103Node15_sound : Sound component103Node15Box :=
  sound_of_literal_split component103Node15Box leaf5071Box leaf5072Box
    .k (253/64) (by rfl) (by rfl)
    leaf5071FlatSound leaf5072FlatSound

private noncomputable def component103Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (65/256), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component103Node16_sound : Sound component103Node16Box :=
  sound_of_literal_split component103Node16Box leaf5073Box leaf5074Box
    .k (253/64) (by rfl) (by rfl)
    leaf5073FlatSound leaf5074FlatSound

private noncomputable def component103Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (1/4), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component103Node17_sound : Sound component103Node17Box :=
  sound_of_literal_split component103Node17Box component103Node15Box component103Node16Box
    .chi (65/256) (by rfl) (by rfl)
    component103Node15_sound component103Node16_sound

private noncomputable def component103Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (1/4), chiHi := (65/256) }

set_option maxRecDepth 1000000 in
private theorem component103Node18_sound : Sound component103Node18Box :=
  sound_of_literal_split component103Node18Box leaf5075Box leaf5076Box
    .k (255/64) (by rfl) (by rfl)
    leaf5075FlatSound leaf5076FlatSound

private noncomputable def component103Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (65/256), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component103Node19_sound : Sound component103Node19Box :=
  sound_of_literal_split component103Node19Box leaf5077Box leaf5078Box
    .k (255/64) (by rfl) (by rfl)
    leaf5077FlatSound leaf5078FlatSound

private noncomputable def component103Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (1/4), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component103Node20_sound : Sound component103Node20Box :=
  sound_of_literal_split component103Node20Box component103Node18Box component103Node19Box
    .chi (65/256) (by rfl) (by rfl)
    component103Node18_sound component103Node19_sound

private noncomputable def component103Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (1/4), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component103Node21_sound : Sound component103Node21Box :=
  sound_of_literal_split component103Node21Box component103Node17Box component103Node20Box
    .k (127/32) (by rfl) (by rfl)
    component103Node17_sound component103Node20_sound

private noncomputable def component103Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (33/128), chiHi := (67/256) }

set_option maxRecDepth 1000000 in
private theorem component103Node22_sound : Sound component103Node22Box :=
  sound_of_literal_split component103Node22Box leaf5079Box leaf5080Box
    .k (253/64) (by rfl) (by rfl)
    leaf5079FlatSound leaf5080FlatSound

private noncomputable def component103Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (67/256), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component103Node23_sound : Sound component103Node23Box :=
  sound_of_literal_split component103Node23Box leaf5081Box leaf5082Box
    .k (253/64) (by rfl) (by rfl)
    leaf5081FlatSound leaf5082FlatSound

private noncomputable def component103Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (33/128), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component103Node24_sound : Sound component103Node24Box :=
  sound_of_literal_split component103Node24Box component103Node22Box component103Node23Box
    .chi (67/256) (by rfl) (by rfl)
    component103Node22_sound component103Node23_sound

private noncomputable def component103Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (33/128), chiHi := (67/256) }

set_option maxRecDepth 1000000 in
private theorem component103Node25_sound : Sound component103Node25Box :=
  sound_of_literal_split component103Node25Box leaf5083Box leaf5084Box
    .k (255/64) (by rfl) (by rfl)
    leaf5083FlatSound leaf5084FlatSound

private noncomputable def component103Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (67/256), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component103Node26_sound : Sound component103Node26Box :=
  sound_of_literal_split component103Node26Box leaf5085Box leaf5086Box
    .k (255/64) (by rfl) (by rfl)
    leaf5085FlatSound leaf5086FlatSound

private noncomputable def component103Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (33/128), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component103Node27_sound : Sound component103Node27Box :=
  sound_of_literal_split component103Node27Box component103Node25Box component103Node26Box
    .chi (67/256) (by rfl) (by rfl)
    component103Node25_sound component103Node26_sound

private noncomputable def component103Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (33/128), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component103Node28_sound : Sound component103Node28Box :=
  sound_of_literal_split component103Node28Box component103Node24Box component103Node27Box
    .k (127/32) (by rfl) (by rfl)
    component103Node24_sound component103Node27_sound

private noncomputable def component103Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component103Node29_sound : Sound component103Node29Box :=
  sound_of_literal_split component103Node29Box component103Node21Box component103Node28Box
    .chi (33/128) (by rfl) (by rfl)
    component103Node21_sound component103Node28_sound

private noncomputable def component103Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component103Node30_sound : Sound component103Node30Box :=
  sound_of_literal_split component103Node30Box component103Node14Box component103Node29Box
    .k (63/16) (by rfl) (by rfl)
    component103Node14_sound component103Node29_sound

private noncomputable def component103Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (17/64), chiHi := (69/256) }

set_option maxRecDepth 1000000 in
private theorem component103Node31_sound : Sound component103Node31Box :=
  sound_of_literal_split component103Node31Box leaf5087Box leaf5088Box
    .k (249/64) (by rfl) (by rfl)
    leaf5087FlatSound leaf5088FlatSound

private noncomputable def component103Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (69/256), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component103Node32_sound : Sound component103Node32Box :=
  sound_of_literal_split component103Node32Box leaf5089Box leaf5090Box
    .k (249/64) (by rfl) (by rfl)
    leaf5089FlatSound leaf5090FlatSound

private noncomputable def component103Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (17/64), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component103Node33_sound : Sound component103Node33Box :=
  sound_of_literal_split component103Node33Box component103Node31Box component103Node32Box
    .chi (69/256) (by rfl) (by rfl)
    component103Node31_sound component103Node32_sound

private noncomputable def component103Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (17/64), chiHi := (69/256) }

set_option maxRecDepth 1000000 in
private theorem component103Node34_sound : Sound component103Node34Box :=
  sound_of_literal_split component103Node34Box leaf5091Box leaf5092Box
    .k (251/64) (by rfl) (by rfl)
    leaf5091FlatSound leaf5092FlatSound

private noncomputable def component103Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (69/256), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component103Node35_sound : Sound component103Node35Box :=
  sound_of_literal_split component103Node35Box leaf5093Box leaf5094Box
    .k (251/64) (by rfl) (by rfl)
    leaf5093FlatSound leaf5094FlatSound

private noncomputable def component103Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (17/64), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component103Node36_sound : Sound component103Node36Box :=
  sound_of_literal_split component103Node36Box component103Node34Box component103Node35Box
    .chi (69/256) (by rfl) (by rfl)
    component103Node34_sound component103Node35_sound

private noncomputable def component103Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (17/64), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component103Node37_sound : Sound component103Node37Box :=
  sound_of_literal_split component103Node37Box component103Node33Box component103Node36Box
    .k (125/32) (by rfl) (by rfl)
    component103Node33_sound component103Node36_sound

private noncomputable def component103Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (35/128), chiHi := (71/256) }

set_option maxRecDepth 1000000 in
private theorem component103Node38_sound : Sound component103Node38Box :=
  sound_of_literal_split component103Node38Box leaf5095Box leaf5096Box
    .k (249/64) (by rfl) (by rfl)
    leaf5095FlatSound leaf5096FlatSound

private noncomputable def component103Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (71/256), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component103Node39_sound : Sound component103Node39Box :=
  sound_of_literal_split component103Node39Box leaf5097Box leaf5098Box
    .k (249/64) (by rfl) (by rfl)
    leaf5097FlatSound leaf5098FlatSound

private noncomputable def component103Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (35/128), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component103Node40_sound : Sound component103Node40Box :=
  sound_of_literal_split component103Node40Box component103Node38Box component103Node39Box
    .chi (71/256) (by rfl) (by rfl)
    component103Node38_sound component103Node39_sound

private noncomputable def component103Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (35/128), chiHi := (71/256) }

set_option maxRecDepth 1000000 in
private theorem component103Node41_sound : Sound component103Node41Box :=
  sound_of_literal_split component103Node41Box leaf5099Box leaf5100Box
    .k (251/64) (by rfl) (by rfl)
    leaf5099FlatSound leaf5100FlatSound

private noncomputable def component103Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (71/256), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component103Node42_sound : Sound component103Node42Box :=
  sound_of_literal_split component103Node42Box leaf5101Box leaf5102Box
    .k (251/64) (by rfl) (by rfl)
    leaf5101FlatSound leaf5102FlatSound

private noncomputable def component103Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (35/128), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component103Node43_sound : Sound component103Node43Box :=
  sound_of_literal_split component103Node43Box component103Node41Box component103Node42Box
    .chi (71/256) (by rfl) (by rfl)
    component103Node41_sound component103Node42_sound

private noncomputable def component103Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (35/128), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component103Node44_sound : Sound component103Node44Box :=
  sound_of_literal_split component103Node44Box component103Node40Box component103Node43Box
    .k (125/32) (by rfl) (by rfl)
    component103Node40_sound component103Node43_sound

private noncomputable def component103Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component103Node45_sound : Sound component103Node45Box :=
  sound_of_literal_split component103Node45Box component103Node37Box component103Node44Box
    .chi (35/128) (by rfl) (by rfl)
    component103Node37_sound component103Node44_sound

private noncomputable def component103Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (17/64), chiHi := (69/256) }

set_option maxRecDepth 1000000 in
private theorem component103Node46_sound : Sound component103Node46Box :=
  sound_of_literal_split component103Node46Box leaf5103Box leaf5104Box
    .k (253/64) (by rfl) (by rfl)
    leaf5103FlatSound leaf5104FlatSound

private noncomputable def component103Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (69/256), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component103Node47_sound : Sound component103Node47Box :=
  sound_of_literal_split component103Node47Box leaf5105Box leaf5106Box
    .k (253/64) (by rfl) (by rfl)
    leaf5105FlatSound leaf5106FlatSound

private noncomputable def component103Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (17/64), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component103Node48_sound : Sound component103Node48Box :=
  sound_of_literal_split component103Node48Box component103Node46Box component103Node47Box
    .chi (69/256) (by rfl) (by rfl)
    component103Node46_sound component103Node47_sound

private noncomputable def component103Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (17/64), chiHi := (69/256) }

set_option maxRecDepth 1000000 in
private theorem component103Node49_sound : Sound component103Node49Box :=
  sound_of_literal_split component103Node49Box leaf5107Box leaf5108Box
    .k (255/64) (by rfl) (by rfl)
    leaf5107FlatSound leaf5108FlatSound

private noncomputable def component103Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (69/256), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component103Node50_sound : Sound component103Node50Box :=
  sound_of_literal_split component103Node50Box leaf5109Box leaf5110Box
    .k (255/64) (by rfl) (by rfl)
    leaf5109FlatSound leaf5110FlatSound

private noncomputable def component103Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (17/64), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component103Node51_sound : Sound component103Node51Box :=
  sound_of_literal_split component103Node51Box component103Node49Box component103Node50Box
    .chi (69/256) (by rfl) (by rfl)
    component103Node49_sound component103Node50_sound

private noncomputable def component103Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (17/64), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component103Node52_sound : Sound component103Node52Box :=
  sound_of_literal_split component103Node52Box component103Node48Box component103Node51Box
    .k (127/32) (by rfl) (by rfl)
    component103Node48_sound component103Node51_sound

private noncomputable def component103Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (35/128), chiHi := (71/256) }

set_option maxRecDepth 1000000 in
private theorem component103Node53_sound : Sound component103Node53Box :=
  sound_of_literal_split component103Node53Box leaf5111Box leaf5112Box
    .k (253/64) (by rfl) (by rfl)
    leaf5111FlatSound leaf5112FlatSound

private noncomputable def component103Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (71/256), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component103Node54_sound : Sound component103Node54Box :=
  sound_of_literal_split component103Node54Box leaf5113Box leaf5114Box
    .k (253/64) (by rfl) (by rfl)
    leaf5113FlatSound leaf5114FlatSound

private noncomputable def component103Node55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (35/128), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component103Node55_sound : Sound component103Node55Box :=
  sound_of_literal_split component103Node55Box component103Node53Box component103Node54Box
    .chi (71/256) (by rfl) (by rfl)
    component103Node53_sound component103Node54_sound

private noncomputable def component103Node56Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (35/128), chiHi := (71/256) }

set_option maxRecDepth 1000000 in
private theorem component103Node56_sound : Sound component103Node56Box :=
  sound_of_literal_split component103Node56Box leaf5115Box leaf5116Box
    .k (255/64) (by rfl) (by rfl)
    leaf5115FlatSound leaf5116FlatSound

private noncomputable def component103Node57Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (71/256), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component103Node57_sound : Sound component103Node57Box :=
  sound_of_literal_split component103Node57Box leaf5117Box leaf5118Box
    .k (255/64) (by rfl) (by rfl)
    leaf5117FlatSound leaf5118FlatSound

private noncomputable def component103Node58Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (35/128), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component103Node58_sound : Sound component103Node58Box :=
  sound_of_literal_split component103Node58Box component103Node56Box component103Node57Box
    .chi (71/256) (by rfl) (by rfl)
    component103Node56_sound component103Node57_sound

private noncomputable def component103Node59Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (35/128), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component103Node59_sound : Sound component103Node59Box :=
  sound_of_literal_split component103Node59Box component103Node55Box component103Node58Box
    .k (127/32) (by rfl) (by rfl)
    component103Node55_sound component103Node58_sound

private noncomputable def component103Node60Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component103Node60_sound : Sound component103Node60Box :=
  sound_of_literal_split component103Node60Box component103Node52Box component103Node59Box
    .chi (35/128) (by rfl) (by rfl)
    component103Node52_sound component103Node59_sound

private noncomputable def component103Node61Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component103Node61_sound : Sound component103Node61Box :=
  sound_of_literal_split component103Node61Box component103Node45Box component103Node60Box
    .k (63/16) (by rfl) (by rfl)
    component103Node45_sound component103Node60_sound

noncomputable def component103Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (1/4), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
theorem component103_sound : Sound component103Box :=
  sound_of_literal_split component103Box component103Node30Box component103Node61Box
    .chi (17/64) (by rfl) (by rfl)
    component103Node30_sound component103Node61_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
