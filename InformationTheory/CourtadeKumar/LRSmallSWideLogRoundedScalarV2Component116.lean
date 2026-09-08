import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch4
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

private noncomputable def leaf5761Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (7/16), chiHi := (57/128) }

private noncomputable def leaf5761Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435779/268435456) }, vSqrt := { lower := (65529/65536), upper := (1108345889/1108279808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (650060735/536870912) }, upper := { exponent := 1, mantissa := (10081/8192) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi267LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (2216625697/2216559616) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf5761InnerLog : WideLogData :=
  innerPair279Data

set_option maxRecDepth 1000000 in
private theorem leaf5761LocalValidity :
    LeafFacts leaf5761Box leaf5761Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5761Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (1108345889/1108279808) }) = true
      norm_num [leaf5761Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5761CertificateValid :
    WideCertificateValid leaf5761Box leaf5761Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi267ValidityFacts
    leaf5761LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5761CoverageChecked :
    coverageCheck (innerAD leaf5761Box) leaf5761InnerLog = true := by
  rfl'

private theorem leaf5761InnerLogValid :
    leaf5761InnerLog.Valid 8 (innerAD leaf5761Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint79PositiveFacts.valid leaf5761CoverageChecked

private noncomputable def leaf5761InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629581/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5761InputLogOnePlusV_eq :
    leaf5761InputLogOnePlusV = outerEnclosure 24
      (leaf5761Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5761RoundedFacts : LeafRoundedFacts 8
    leaf5761Certificate.logOnePlusV leaf5761InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5761InputLogOnePlusV_eq }

private noncomputable def leaf5761Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi267InputQChi innerPair279Input
    leaf5761InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5761LowerChecked :
    lowerCheck 24 leaf5761Box leaf5761Inputs = true := by
  rfl'

private theorem leaf5761CoversExact : CoversExact 8
    leaf5761Box leaf5761Certificate leaf5761InnerLog leaf5761Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi267RoundedFacts
    innerPair279RoundedFacts leaf5761RoundedFacts (by rfl)

private theorem leaf5761FlatSound : Sound leaf5761Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5761CertificateValid
    leaf5761InnerLogValid leaf5761CoversExact leaf5761LowerChecked

private noncomputable def leaf5762Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (7/16), chiHi := (57/128) }

private noncomputable def leaf5762Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435781/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356644864) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (653730525/536870912) }, upper := { exponent := 1, mantissa := (5069/4096) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi267LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715367423/68713289728) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf5762InnerLog : WideLogData :=
  innerPair279Data

set_option maxRecDepth 1000000 in
private theorem leaf5762LocalValidity :
    LeafFacts leaf5762Box leaf5762Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5762Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356644864) }) = true
      norm_num [leaf5762Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5762CertificateValid :
    WideCertificateValid leaf5762Box leaf5762Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi267ValidityFacts
    leaf5762LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5762CoverageChecked :
    coverageCheck (innerAD leaf5762Box) leaf5762InnerLog = true := by
  rfl'

private theorem leaf5762InnerLogValid :
    leaf5762InnerLog.Valid 8 (innerAD leaf5762Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint79PositiveFacts.valid leaf5762CoverageChecked

private noncomputable def leaf5762InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907397/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5762InputLogOnePlusV_eq :
    leaf5762InputLogOnePlusV = outerEnclosure 24
      (leaf5762Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5762RoundedFacts : LeafRoundedFacts 8
    leaf5762Certificate.logOnePlusV leaf5762InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5762InputLogOnePlusV_eq }

private noncomputable def leaf5762Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi267InputQChi innerPair279Input
    leaf5762InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5762LowerChecked :
    lowerCheck 24 leaf5762Box leaf5762Inputs = true := by
  rfl'

private theorem leaf5762CoversExact : CoversExact 8
    leaf5762Box leaf5762Certificate leaf5762InnerLog leaf5762Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi267RoundedFacts
    innerPair279RoundedFacts leaf5762RoundedFacts (by rfl)

private theorem leaf5762FlatSound : Sound leaf5762Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5762CertificateValid
    leaf5762InnerLogValid leaf5762CoversExact leaf5762LowerChecked

private noncomputable def leaf5763Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (57/128), chiHi := (29/64) }

private noncomputable def leaf5763Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435781/268435456) }, vSqrt := { lower := (65529/65536), upper := (4042140973/4041955328) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (656876061/536870912) }, upper := { exponent := 1, mantissa := (5093/4096) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi268LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (8084096301/8083910656) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf5763InnerLog : WideLogData :=
  innerPair285Data

set_option maxRecDepth 1000000 in
private theorem leaf5763LocalValidity :
    LeafFacts leaf5763Box leaf5763Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5763Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4042140973/4041955328) }) = true
      norm_num [leaf5763Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5763CertificateValid :
    WideCertificateValid leaf5763Box leaf5763Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi268ValidityFacts
    leaf5763LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5763CoverageChecked :
    coverageCheck (innerAD leaf5763Box) leaf5763InnerLog = true := by
  rfl'

private theorem leaf5763InnerLogValid :
    leaf5763InnerLog.Valid 8 (innerAD leaf5763Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint79PositiveFacts.valid leaf5763CoverageChecked

private noncomputable def leaf5763InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814733/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5763InputLogOnePlusV_eq :
    leaf5763InputLogOnePlusV = outerEnclosure 24
      (leaf5763Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5763RoundedFacts : LeafRoundedFacts 8
    leaf5763Certificate.logOnePlusV leaf5763InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5763InputLogOnePlusV_eq }

private noncomputable def leaf5763Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi268InputQChi innerPair285Input
    leaf5763InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5763LowerChecked :
    lowerCheck 24 leaf5763Box leaf5763Inputs = true := by
  rfl'

private theorem leaf5763CoversExact : CoversExact 8
    leaf5763Box leaf5763Certificate leaf5763InnerLog leaf5763Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi268RoundedFacts
    innerPair285RoundedFacts leaf5763RoundedFacts (by rfl)

private theorem leaf5763FlatSound : Sound leaf5763Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5763CertificateValid
    leaf5763InnerLogValid leaf5763CoversExact leaf5763LowerChecked

private noncomputable def leaf5764Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (57/128), chiHi := (29/64) }

private noncomputable def leaf5764Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435783/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68713181184) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (660611383/536870912) }, upper := { exponent := 1, mantissa := (2561/2048) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi268LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429577725/137426362368) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf5764InnerLog : WideLogData :=
  innerPair286Data

set_option maxRecDepth 1000000 in
private theorem leaf5764LocalValidity :
    LeafFacts leaf5764Box leaf5764Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5764Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68713181184) }) = true
      norm_num [leaf5764Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5764CertificateValid :
    WideCertificateValid leaf5764Box leaf5764Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi268ValidityFacts
    leaf5764LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5764CoverageChecked :
    coverageCheck (innerAD leaf5764Box) leaf5764InnerLog = true := by
  rfl'

private theorem leaf5764InnerLogValid :
    leaf5764InnerLog.Valid 8 (innerAD leaf5764Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint90PositiveFacts.valid leaf5764CoverageChecked

private noncomputable def leaf5764InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629473/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5764InputLogOnePlusV_eq :
    leaf5764InputLogOnePlusV = outerEnclosure 24
      (leaf5764Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5764RoundedFacts : LeafRoundedFacts 8
    leaf5764Certificate.logOnePlusV leaf5764InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5764InputLogOnePlusV_eq }

private noncomputable def leaf5764Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi268InputQChi innerPair286Input
    leaf5764InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5764LowerChecked :
    lowerCheck 24 leaf5764Box leaf5764Inputs = true := by
  rfl'

private theorem leaf5764CoversExact : CoversExact 8
    leaf5764Box leaf5764Certificate leaf5764InnerLog leaf5764Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi268RoundedFacts
    innerPair286RoundedFacts leaf5764RoundedFacts (by rfl)

private theorem leaf5764FlatSound : Sound leaf5764Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5764CertificateValid
    leaf5764InnerLogValid leaf5764CoversExact leaf5764LowerChecked

private noncomputable def leaf5765Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (7/16), chiHi := (57/128) }

private noncomputable def leaf5765Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435783/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68713231360) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (657400315/536870912) }, upper := { exponent := 1, mantissa := (10195/8192) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi267LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429627901/137426462720) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf5765InnerLog : WideLogData :=
  innerPair285Data

set_option maxRecDepth 1000000 in
private theorem leaf5765LocalValidity :
    LeafFacts leaf5765Box leaf5765Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5765Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68713231360) }) = true
      norm_num [leaf5765Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5765CertificateValid :
    WideCertificateValid leaf5765Box leaf5765Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi267ValidityFacts
    leaf5765LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5765CoverageChecked :
    coverageCheck (innerAD leaf5765Box) leaf5765InnerLog = true := by
  rfl'

private theorem leaf5765InnerLogValid :
    leaf5765InnerLog.Valid 8 (innerAD leaf5765Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint79PositiveFacts.valid leaf5765CoverageChecked

private noncomputable def leaf5765InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629467/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5765InputLogOnePlusV_eq :
    leaf5765InputLogOnePlusV = outerEnclosure 24
      (leaf5765Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5765RoundedFacts : LeafRoundedFacts 8
    leaf5765Certificate.logOnePlusV leaf5765InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5765InputLogOnePlusV_eq }

private noncomputable def leaf5765Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi267InputQChi innerPair285Input
    leaf5765InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5765LowerChecked :
    lowerCheck 24 leaf5765Box leaf5765Inputs = true := by
  rfl'

private theorem leaf5765CoversExact : CoversExact 8
    leaf5765Box leaf5765Certificate leaf5765InnerLog leaf5765Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi267RoundedFacts
    innerPair285RoundedFacts leaf5765RoundedFacts (by rfl)

private theorem leaf5765FlatSound : Sound leaf5765Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5765CertificateValid
    leaf5765InnerLogValid leaf5765CoversExact leaf5765LowerChecked

private noncomputable def leaf5766Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (7/16), chiHi := (57/128) }

private noncomputable def leaf5766Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435785/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68713172992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (661070105/536870912) }, upper := { exponent := 1, mantissa := (2563/2048) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi267LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429569533/137426345984) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf5766InnerLog : WideLogData :=
  innerPair286Data

set_option maxRecDepth 1000000 in
private theorem leaf5766LocalValidity :
    LeafFacts leaf5766Box leaf5766Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5766Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68713172992) }) = true
      norm_num [leaf5766Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5766CertificateValid :
    WideCertificateValid leaf5766Box leaf5766Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi267ValidityFacts
    leaf5766LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5766CoverageChecked :
    coverageCheck (innerAD leaf5766Box) leaf5766InnerLog = true := by
  rfl'

private theorem leaf5766InnerLogValid :
    leaf5766InnerLog.Valid 8 (innerAD leaf5766Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint90PositiveFacts.valid leaf5766CoverageChecked

private noncomputable def leaf5766InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814737/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5766InputLogOnePlusV_eq :
    leaf5766InputLogOnePlusV = outerEnclosure 24
      (leaf5766Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5766RoundedFacts : LeafRoundedFacts 8
    leaf5766Certificate.logOnePlusV leaf5766InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5766InputLogOnePlusV_eq }

private noncomputable def leaf5766Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi267InputQChi innerPair286Input
    leaf5766InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5766LowerChecked :
    lowerCheck 24 leaf5766Box leaf5766Inputs = true := by
  rfl'

private theorem leaf5766CoversExact : CoversExact 8
    leaf5766Box leaf5766Certificate leaf5766InnerLog leaf5766Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi267RoundedFacts
    innerPair286RoundedFacts leaf5766RoundedFacts (by rfl)

private theorem leaf5766FlatSound : Sound leaf5766Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5766CertificateValid
    leaf5766InnerLogValid leaf5766CoversExact leaf5766LowerChecked

private noncomputable def leaf5767Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (57/128), chiHi := (29/64) }

private noncomputable def leaf5767Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435785/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68713121792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (664346705/536870912) }, upper := { exponent := 1, mantissa := (5151/4096) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi268LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429518333/137426243584) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf5767InnerLog : WideLogData :=
  innerPair286Data

set_option maxRecDepth 1000000 in
private theorem leaf5767LocalValidity :
    LeafFacts leaf5767Box leaf5767Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5767Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68713121792) }) = true
      norm_num [leaf5767Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5767CertificateValid :
    WideCertificateValid leaf5767Box leaf5767Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi268ValidityFacts
    leaf5767LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5767CoverageChecked :
    coverageCheck (innerAD leaf5767Box) leaf5767InnerLog = true := by
  rfl'

private theorem leaf5767InnerLogValid :
    leaf5767InnerLog.Valid 8 (innerAD leaf5767Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint90PositiveFacts.valid leaf5767CoverageChecked

private noncomputable def leaf5767InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629481/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5767InputLogOnePlusV_eq :
    leaf5767InputLogOnePlusV = outerEnclosure 24
      (leaf5767Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5767RoundedFacts : LeafRoundedFacts 8
    leaf5767Certificate.logOnePlusV leaf5767InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5767InputLogOnePlusV_eq }

private noncomputable def leaf5767Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi268InputQChi innerPair286Input
    leaf5767InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5767LowerChecked :
    lowerCheck 24 leaf5767Box leaf5767Inputs = true := by
  rfl'

private theorem leaf5767CoversExact : CoversExact 8
    leaf5767Box leaf5767Certificate leaf5767InnerLog leaf5767Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi268RoundedFacts
    innerPair286RoundedFacts leaf5767RoundedFacts (by rfl)

private theorem leaf5767FlatSound : Sound leaf5767Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5767CertificateValid
    leaf5767InnerLogValid leaf5767CoversExact leaf5767LowerChecked

private noncomputable def leaf5768Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (57/128), chiHi := (29/64) }

private noncomputable def leaf5768Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435787/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68713062400) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (668082027/536870912) }, upper := { exponent := 1, mantissa := (1295/1024) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi268LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429458941/137426124800) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf5768InnerLog : WideLogData :=
  innerPair286Data

set_option maxRecDepth 1000000 in
private theorem leaf5768LocalValidity :
    LeafFacts leaf5768Box leaf5768Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5768Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68713062400) }) = true
      norm_num [leaf5768Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5768CertificateValid :
    WideCertificateValid leaf5768Box leaf5768Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi268ValidityFacts
    leaf5768LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5768CoverageChecked :
    coverageCheck (innerAD leaf5768Box) leaf5768InnerLog = true := by
  rfl'

private theorem leaf5768InnerLogValid :
    leaf5768InnerLog.Valid 8 (innerAD leaf5768Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint90PositiveFacts.valid leaf5768CoverageChecked

private noncomputable def leaf5768InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (726843/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf5768InputLogOnePlusV_eq :
    leaf5768InputLogOnePlusV = outerEnclosure 24
      (leaf5768Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5768RoundedFacts : LeafRoundedFacts 8
    leaf5768Certificate.logOnePlusV leaf5768InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5768InputLogOnePlusV_eq }

private noncomputable def leaf5768Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi268InputQChi innerPair286Input
    leaf5768InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5768LowerChecked :
    lowerCheck 24 leaf5768Box leaf5768Inputs = true := by
  rfl'

private theorem leaf5768CoversExact : CoversExact 8
    leaf5768Box leaf5768Certificate leaf5768InnerLog leaf5768Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi268RoundedFacts
    innerPair286RoundedFacts leaf5768RoundedFacts (by rfl)

private theorem leaf5768FlatSound : Sound leaf5768Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5768CertificateValid
    leaf5768InnerLogValid leaf5768CoversExact leaf5768LowerChecked

private noncomputable def leaf5769Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (29/64), chiHi := (59/128) }

private noncomputable def leaf5769Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435783/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68713133056) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (663691387/536870912) }, upper := { exponent := 1, mantissa := (10291/8192) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi269LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429529597/137426266112) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf5769InnerLog : WideLogData :=
  innerPair286Data

set_option maxRecDepth 1000000 in
private theorem leaf5769LocalValidity :
    LeafFacts leaf5769Box leaf5769Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5769Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68713133056) }) = true
      norm_num [leaf5769Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5769CertificateValid :
    WideCertificateValid leaf5769Box leaf5769Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi269ValidityFacts
    leaf5769LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5769CoverageChecked :
    coverageCheck (innerAD leaf5769Box) leaf5769InnerLog = true := by
  rfl'

private theorem leaf5769InnerLogValid :
    leaf5769InnerLog.Valid 8 (innerAD leaf5769Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint90PositiveFacts.valid leaf5769CoverageChecked

private noncomputable def leaf5769InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629479/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5769InputLogOnePlusV_eq :
    leaf5769InputLogOnePlusV = outerEnclosure 24
      (leaf5769Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5769RoundedFacts : LeafRoundedFacts 8
    leaf5769Certificate.logOnePlusV leaf5769InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5769InputLogOnePlusV_eq }

private noncomputable def leaf5769Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi269InputQChi innerPair286Input
    leaf5769InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5769LowerChecked :
    lowerCheck 24 leaf5769Box leaf5769Inputs = true := by
  rfl'

private theorem leaf5769CoversExact : CoversExact 8
    leaf5769Box leaf5769Certificate leaf5769InnerLog leaf5769Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi269RoundedFacts
    innerPair286RoundedFacts leaf5769RoundedFacts (by rfl)

private theorem leaf5769FlatSound : Sound leaf5769Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5769CertificateValid
    leaf5769InnerLogValid leaf5769CoversExact leaf5769LowerChecked

private noncomputable def leaf5770Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (29/64), chiHi := (59/128) }

private noncomputable def leaf5770Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435785/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68713072640) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (667492241/536870912) }, upper := { exponent := 1, mantissa := (5175/4096) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi269LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429469181/137426145280) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf5770InnerLog : WideLogData :=
  innerPair286Data

set_option maxRecDepth 1000000 in
private theorem leaf5770LocalValidity :
    LeafFacts leaf5770Box leaf5770Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5770Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68713072640) }) = true
      norm_num [leaf5770Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5770CertificateValid :
    WideCertificateValid leaf5770Box leaf5770Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi269ValidityFacts
    leaf5770LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5770CoverageChecked :
    coverageCheck (innerAD leaf5770Box) leaf5770InnerLog = true := by
  rfl'

private theorem leaf5770InnerLogValid :
    leaf5770InnerLog.Valid 8 (innerAD leaf5770Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint90PositiveFacts.valid leaf5770CoverageChecked

private noncomputable def leaf5770InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629487/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5770InputLogOnePlusV_eq :
    leaf5770InputLogOnePlusV = outerEnclosure 24
      (leaf5770Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5770RoundedFacts : LeafRoundedFacts 8
    leaf5770Certificate.logOnePlusV leaf5770InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5770InputLogOnePlusV_eq }

private noncomputable def leaf5770Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi269InputQChi innerPair286Input
    leaf5770InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5770LowerChecked :
    lowerCheck 24 leaf5770Box leaf5770Inputs = true := by
  rfl'

private theorem leaf5770CoversExact : CoversExact 8
    leaf5770Box leaf5770Certificate leaf5770InnerLog leaf5770Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi269RoundedFacts
    innerPair286RoundedFacts leaf5770RoundedFacts (by rfl)

private theorem leaf5770FlatSound : Sound leaf5770Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5770CertificateValid
    leaf5770InnerLogValid leaf5770CoversExact leaf5770LowerChecked

private noncomputable def leaf5771Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (59/128), chiHi := (15/32) }

private noncomputable def leaf5771Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435785/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68713025536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (670506713/536870912) }, upper := { exponent := 1, mantissa := (2599/2048) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi270LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429422077/137426051072) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf5771InnerLog : WideLogData :=
  innerPair286Data

set_option maxRecDepth 1000000 in
private theorem leaf5771LocalValidity :
    LeafFacts leaf5771Box leaf5771Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5771Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68713025536) }) = true
      norm_num [leaf5771Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5771CertificateValid :
    WideCertificateValid leaf5771Box leaf5771Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi270ValidityFacts
    leaf5771LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5771CoverageChecked :
    coverageCheck (innerAD leaf5771Box) leaf5771InnerLog = true := by
  rfl'

private theorem leaf5771InnerLogValid :
    leaf5771InnerLog.Valid 8 (innerAD leaf5771Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint90PositiveFacts.valid leaf5771CoverageChecked

private noncomputable def leaf5771InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907373/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5771InputLogOnePlusV_eq :
    leaf5771InputLogOnePlusV = outerEnclosure 24
      (leaf5771Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5771RoundedFacts : LeafRoundedFacts 8
    leaf5771Certificate.logOnePlusV leaf5771InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5771InputLogOnePlusV_eq }

private noncomputable def leaf5771Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi270InputQChi innerPair286Input
    leaf5771InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5771LowerChecked :
    lowerCheck 24 leaf5771Box leaf5771Inputs = true := by
  rfl'

private theorem leaf5771CoversExact : CoversExact 8
    leaf5771Box leaf5771Certificate leaf5771InnerLog leaf5771Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi270RoundedFacts
    innerPair286RoundedFacts leaf5771RoundedFacts (by rfl)

private theorem leaf5771FlatSound : Sound leaf5771Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5771CertificateValid
    leaf5771InnerLogValid leaf5771CoversExact leaf5771LowerChecked

private noncomputable def leaf5772Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (59/128), chiHi := (15/32) }

private noncomputable def leaf5772Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435787/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712964096) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (674373099/536870912) }, upper := { exponent := 1, mantissa := (1307/1024) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi270LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429360637/137425928192) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf5772InnerLog : WideLogData :=
  innerPair293Data

set_option maxRecDepth 1000000 in
private theorem leaf5772LocalValidity :
    LeafFacts leaf5772Box leaf5772Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5772Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712964096) }) = true
      norm_num [leaf5772Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5772CertificateValid :
    WideCertificateValid leaf5772Box leaf5772Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi270ValidityFacts
    leaf5772LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5772CoverageChecked :
    coverageCheck (innerAD leaf5772Box) leaf5772InnerLog = true := by
  rfl'

private theorem leaf5772InnerLogValid :
    leaf5772InnerLog.Valid 8 (innerAD leaf5772Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint90PositiveFacts.valid leaf5772CoverageChecked

private noncomputable def leaf5772InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907375/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5772InputLogOnePlusV_eq :
    leaf5772InputLogOnePlusV = outerEnclosure 24
      (leaf5772Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5772RoundedFacts : LeafRoundedFacts 8
    leaf5772Certificate.logOnePlusV leaf5772InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5772InputLogOnePlusV_eq }

private noncomputable def leaf5772Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi270InputQChi innerPair293Input
    leaf5772InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5772LowerChecked :
    lowerCheck 24 leaf5772Box leaf5772Inputs = true := by
  rfl'

private theorem leaf5772CoversExact : CoversExact 8
    leaf5772Box leaf5772Certificate leaf5772InnerLog leaf5772Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi270RoundedFacts
    innerPair293RoundedFacts leaf5772RoundedFacts (by rfl)

private theorem leaf5772FlatSound : Sound leaf5772Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5772CertificateValid
    leaf5772InnerLogValid leaf5772CoversExact leaf5772LowerChecked

private noncomputable def leaf5773Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (29/64), chiHi := (59/128) }

private noncomputable def leaf5773Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435787/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68713012224) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (671293095/536870912) }, upper := { exponent := 1, mantissa := (10409/8192) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi269LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429408765/137426024448) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf5773InnerLog : WideLogData :=
  innerPair293Data

set_option maxRecDepth 1000000 in
private theorem leaf5773LocalValidity :
    LeafFacts leaf5773Box leaf5773Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5773Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68713012224) }) = true
      norm_num [leaf5773Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5773CertificateValid :
    WideCertificateValid leaf5773Box leaf5773Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi269ValidityFacts
    leaf5773LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5773CoverageChecked :
    coverageCheck (innerAD leaf5773Box) leaf5773InnerLog = true := by
  rfl'

private theorem leaf5773InnerLogValid :
    leaf5773InnerLog.Valid 8 (innerAD leaf5773Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint90PositiveFacts.valid leaf5773CoverageChecked

private noncomputable def leaf5773InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814747/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5773InputLogOnePlusV_eq :
    leaf5773InputLogOnePlusV = outerEnclosure 24
      (leaf5773Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5773RoundedFacts : LeafRoundedFacts 8
    leaf5773Certificate.logOnePlusV leaf5773InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5773InputLogOnePlusV_eq }

private noncomputable def leaf5773Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi269InputQChi innerPair293Input
    leaf5773InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5773LowerChecked :
    lowerCheck 24 leaf5773Box leaf5773Inputs = true := by
  rfl'

private theorem leaf5773CoversExact : CoversExact 8
    leaf5773Box leaf5773Certificate leaf5773InnerLog leaf5773Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi269RoundedFacts
    innerPair293RoundedFacts leaf5773RoundedFacts (by rfl)

private theorem leaf5773FlatSound : Sound leaf5773Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5773CertificateValid
    leaf5773InnerLogValid leaf5773CoversExact leaf5773LowerChecked

private noncomputable def leaf5774Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (29/64), chiHi := (59/128) }

private noncomputable def leaf5774Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435789/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712951808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (675093949/536870912) }, upper := { exponent := 1, mantissa := (2617/2048) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi269LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429348349/137425903616) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf5774InnerLog : WideLogData :=
  innerPair293Data

set_option maxRecDepth 1000000 in
private theorem leaf5774LocalValidity :
    LeafFacts leaf5774Box leaf5774Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5774Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712951808) }) = true
      norm_num [leaf5774Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5774CertificateValid :
    WideCertificateValid leaf5774Box leaf5774Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi269ValidityFacts
    leaf5774LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5774CoverageChecked :
    coverageCheck (innerAD leaf5774Box) leaf5774InnerLog = true := by
  rfl'

private theorem leaf5774InnerLogValid :
    leaf5774InnerLog.Valid 8 (innerAD leaf5774Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint90PositiveFacts.valid leaf5774CoverageChecked

private noncomputable def leaf5774InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629501/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5774InputLogOnePlusV_eq :
    leaf5774InputLogOnePlusV = outerEnclosure 24
      (leaf5774Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5774RoundedFacts : LeafRoundedFacts 8
    leaf5774Certificate.logOnePlusV leaf5774InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5774InputLogOnePlusV_eq }

private noncomputable def leaf5774Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi269InputQChi innerPair293Input
    leaf5774InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5774LowerChecked :
    lowerCheck 24 leaf5774Box leaf5774Inputs = true := by
  rfl'

private theorem leaf5774CoversExact : CoversExact 8
    leaf5774Box leaf5774Certificate leaf5774InnerLog leaf5774Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi269RoundedFacts
    innerPair293RoundedFacts leaf5774RoundedFacts (by rfl)

private theorem leaf5774FlatSound : Sound leaf5774Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5774CertificateValid
    leaf5774InnerLogValid leaf5774CoversExact leaf5774LowerChecked

private noncomputable def leaf5775Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (59/128), chiHi := (15/32) }

private noncomputable def leaf5775Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435789/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712902656) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (678239485/536870912) }, upper := { exponent := 1, mantissa := (2629/2048) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi270LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429299197/137425805312) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf5775InnerLog : WideLogData :=
  innerPair294Data

set_option maxRecDepth 1000000 in
private theorem leaf5775LocalValidity :
    LeafFacts leaf5775Box leaf5775Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5775Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712902656) }) = true
      norm_num [leaf5775Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5775CertificateValid :
    WideCertificateValid leaf5775Box leaf5775Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi270ValidityFacts
    leaf5775LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5775CoverageChecked :
    coverageCheck (innerAD leaf5775Box) leaf5775InnerLog = true := by
  rfl'

private theorem leaf5775InnerLogValid :
    leaf5775InnerLog.Valid 8 (innerAD leaf5775Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint91PositiveFacts.valid leaf5775CoverageChecked

private noncomputable def leaf5775InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629507/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5775InputLogOnePlusV_eq :
    leaf5775InputLogOnePlusV = outerEnclosure 24
      (leaf5775Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5775RoundedFacts : LeafRoundedFacts 8
    leaf5775Certificate.logOnePlusV leaf5775InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5775InputLogOnePlusV_eq }

private noncomputable def leaf5775Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi270InputQChi innerPair294Input
    leaf5775InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5775LowerChecked :
    lowerCheck 24 leaf5775Box leaf5775Inputs = true := by
  rfl'

private theorem leaf5775CoversExact : CoversExact 8
    leaf5775Box leaf5775Certificate leaf5775InnerLog leaf5775Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi270RoundedFacts
    innerPair294RoundedFacts leaf5775RoundedFacts (by rfl)

private theorem leaf5775FlatSound : Sound leaf5775Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5775CertificateValid
    leaf5775InnerLogValid leaf5775CoversExact leaf5775LowerChecked

private noncomputable def leaf5776Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (59/128), chiHi := (15/32) }

private noncomputable def leaf5776Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435791/268435456) }, vSqrt := { lower := (65529/65536), upper := (967836571/967786496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (682105871/536870912) }, upper := { exponent := 1, mantissa := (661/512) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi270LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (1935623067/1935572992) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf5776InnerLog : WideLogData :=
  innerPair294Data

set_option maxRecDepth 1000000 in
private theorem leaf5776LocalValidity :
    LeafFacts leaf5776Box leaf5776Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5776Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (967836571/967786496) }) = true
      norm_num [leaf5776Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5776CertificateValid :
    WideCertificateValid leaf5776Box leaf5776Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi270ValidityFacts
    leaf5776LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5776CoverageChecked :
    coverageCheck (innerAD leaf5776Box) leaf5776InnerLog = true := by
  rfl'

private theorem leaf5776InnerLogValid :
    leaf5776InnerLog.Valid 8 (innerAD leaf5776Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint91PositiveFacts.valid leaf5776CoverageChecked

private noncomputable def leaf5776InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629515/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5776InputLogOnePlusV_eq :
    leaf5776InputLogOnePlusV = outerEnclosure 24
      (leaf5776Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5776RoundedFacts : LeafRoundedFacts 8
    leaf5776Certificate.logOnePlusV leaf5776InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5776InputLogOnePlusV_eq }

private noncomputable def leaf5776Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi270InputQChi innerPair294Input
    leaf5776InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5776LowerChecked :
    lowerCheck 24 leaf5776Box leaf5776Inputs = true := by
  rfl'

private theorem leaf5776CoversExact : CoversExact 8
    leaf5776Box leaf5776Certificate leaf5776InnerLog leaf5776Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi270RoundedFacts
    innerPair294RoundedFacts leaf5776RoundedFacts (by rfl)

private theorem leaf5776FlatSound : Sound leaf5776Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5776CertificateValid
    leaf5776InnerLogValid leaf5776CoversExact leaf5776LowerChecked

private noncomputable def leaf5777Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (7/16), chiHi := (57/128) }

private noncomputable def leaf5777Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435787/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68713114624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (664739895/536870912) }, upper := { exponent := 1, mantissa := (10309/8192) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi267LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429511165/137426229248) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf5777InnerLog : WideLogData :=
  innerPair286Data

set_option maxRecDepth 1000000 in
private theorem leaf5777LocalValidity :
    LeafFacts leaf5777Box leaf5777Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5777Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68713114624) }) = true
      norm_num [leaf5777Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5777CertificateValid :
    WideCertificateValid leaf5777Box leaf5777Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi267ValidityFacts
    leaf5777LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5777CoverageChecked :
    coverageCheck (innerAD leaf5777Box) leaf5777InnerLog = true := by
  rfl'

private theorem leaf5777InnerLogValid :
    leaf5777InnerLog.Valid 8 (innerAD leaf5777Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint90PositiveFacts.valid leaf5777CoverageChecked

private noncomputable def leaf5777InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629481/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5777InputLogOnePlusV_eq :
    leaf5777InputLogOnePlusV = outerEnclosure 24
      (leaf5777Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5777RoundedFacts : LeafRoundedFacts 8
    leaf5777Certificate.logOnePlusV leaf5777InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5777InputLogOnePlusV_eq }

private noncomputable def leaf5777Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi267InputQChi innerPair286Input
    leaf5777InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5777LowerChecked :
    lowerCheck 24 leaf5777Box leaf5777Inputs = true := by
  rfl'

private theorem leaf5777CoversExact : CoversExact 8
    leaf5777Box leaf5777Certificate leaf5777InnerLog leaf5777Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi267RoundedFacts
    innerPair286RoundedFacts leaf5777RoundedFacts (by rfl)

private theorem leaf5777FlatSound : Sound leaf5777Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5777CertificateValid
    leaf5777InnerLogValid leaf5777CoversExact leaf5777LowerChecked

private noncomputable def leaf5778Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (7/16), chiHi := (57/128) }

private noncomputable def leaf5778Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435789/268435456) }, vSqrt := { lower := (65529/65536), upper := (5285876657/5285619712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (668409685/536870912) }, upper := { exponent := 1, mantissa := (5183/4096) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi267LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (10571496369/10571239424) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf5778InnerLog : WideLogData :=
  innerPair286Data

set_option maxRecDepth 1000000 in
private theorem leaf5778LocalValidity :
    LeafFacts leaf5778Box leaf5778Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5778Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (5285876657/5285619712) }) = true
      norm_num [leaf5778Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5778CertificateValid :
    WideCertificateValid leaf5778Box leaf5778Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi267ValidityFacts
    leaf5778LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5778CoverageChecked :
    coverageCheck (innerAD leaf5778Box) leaf5778InnerLog = true := by
  rfl'

private theorem leaf5778InnerLogValid :
    leaf5778InnerLog.Valid 8 (innerAD leaf5778Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint90PositiveFacts.valid leaf5778CoverageChecked

private noncomputable def leaf5778InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629489/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5778InputLogOnePlusV_eq :
    leaf5778InputLogOnePlusV = outerEnclosure 24
      (leaf5778Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5778RoundedFacts : LeafRoundedFacts 8
    leaf5778Certificate.logOnePlusV leaf5778InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5778InputLogOnePlusV_eq }

private noncomputable def leaf5778Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi267InputQChi innerPair286Input
    leaf5778InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5778LowerChecked :
    lowerCheck 24 leaf5778Box leaf5778Inputs = true := by
  rfl'

private theorem leaf5778CoversExact : CoversExact 8
    leaf5778Box leaf5778Certificate leaf5778InnerLog leaf5778Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi267RoundedFacts
    innerPair286RoundedFacts leaf5778RoundedFacts (by rfl)

private theorem leaf5778FlatSound : Sound leaf5778Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5778CertificateValid
    leaf5778InnerLogValid leaf5778CoversExact leaf5778LowerChecked

private noncomputable def leaf5779Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (57/128), chiHi := (29/64) }

private noncomputable def leaf5779Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435789/268435456) }, vSqrt := { lower := (65529/65536), upper := (5285876657/5285615616) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (671817349/536870912) }, upper := { exponent := 1, mantissa := (5209/4096) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi268LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (10571492273/10571231232) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf5779InnerLog : WideLogData :=
  innerPair293Data

set_option maxRecDepth 1000000 in
private theorem leaf5779LocalValidity :
    LeafFacts leaf5779Box leaf5779Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5779Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (5285876657/5285615616) }) = true
      norm_num [leaf5779Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5779CertificateValid :
    WideCertificateValid leaf5779Box leaf5779Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi268ValidityFacts
    leaf5779LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5779CoverageChecked :
    coverageCheck (innerAD leaf5779Box) leaf5779InnerLog = true := by
  rfl'

private theorem leaf5779InnerLogValid :
    leaf5779InnerLog.Valid 8 (innerAD leaf5779Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint90PositiveFacts.valid leaf5779CoverageChecked

private noncomputable def leaf5779InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629495/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5779InputLogOnePlusV_eq :
    leaf5779InputLogOnePlusV = outerEnclosure 24
      (leaf5779Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5779RoundedFacts : LeafRoundedFacts 8
    leaf5779Certificate.logOnePlusV leaf5779InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5779InputLogOnePlusV_eq }

private noncomputable def leaf5779Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi268InputQChi innerPair293Input
    leaf5779InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5779LowerChecked :
    lowerCheck 24 leaf5779Box leaf5779Inputs = true := by
  rfl'

private theorem leaf5779CoversExact : CoversExact 8
    leaf5779Box leaf5779Certificate leaf5779InnerLog leaf5779Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi268RoundedFacts
    innerPair293RoundedFacts leaf5779RoundedFacts (by rfl)

private theorem leaf5779FlatSound : Sound leaf5779Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5779CertificateValid
    leaf5779InnerLogValid leaf5779CoversExact leaf5779LowerChecked

private noncomputable def leaf5780Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (57/128), chiHi := (29/64) }

private noncomputable def leaf5780Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435791/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712943616) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (675552671/536870912) }, upper := { exponent := 1, mantissa := (2619/2048) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi268LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429340157/137425887232) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf5780InnerLog : WideLogData :=
  innerPair293Data

set_option maxRecDepth 1000000 in
private theorem leaf5780LocalValidity :
    LeafFacts leaf5780Box leaf5780Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5780Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712943616) }) = true
      norm_num [leaf5780Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5780CertificateValid :
    WideCertificateValid leaf5780Box leaf5780Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi268ValidityFacts
    leaf5780LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5780CoverageChecked :
    coverageCheck (innerAD leaf5780Box) leaf5780InnerLog = true := by
  rfl'

private theorem leaf5780InnerLogValid :
    leaf5780InnerLog.Valid 8 (innerAD leaf5780Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint90PositiveFacts.valid leaf5780CoverageChecked

private noncomputable def leaf5780InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814751/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5780InputLogOnePlusV_eq :
    leaf5780InputLogOnePlusV = outerEnclosure 24
      (leaf5780Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5780RoundedFacts : LeafRoundedFacts 8
    leaf5780Certificate.logOnePlusV leaf5780InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5780InputLogOnePlusV_eq }

private noncomputable def leaf5780Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi268InputQChi innerPair293Input
    leaf5780InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5780LowerChecked :
    lowerCheck 24 leaf5780Box leaf5780Inputs = true := by
  rfl'

private theorem leaf5780CoversExact : CoversExact 8
    leaf5780Box leaf5780Certificate leaf5780InnerLog leaf5780Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi268RoundedFacts
    innerPair293RoundedFacts leaf5780RoundedFacts (by rfl)

private theorem leaf5780FlatSound : Sound leaf5780Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5780CertificateValid
    leaf5780InnerLogValid leaf5780CoversExact leaf5780LowerChecked

private noncomputable def leaf5781Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (7/16), chiHi := (57/128) }

private noncomputable def leaf5781Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435791/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712997888) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (672079475/536870912) }, upper := { exponent := 1, mantissa := (10423/8192) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi267LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429394429/137425995776) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf5781InnerLog : WideLogData :=
  innerPair293Data

set_option maxRecDepth 1000000 in
private theorem leaf5781LocalValidity :
    LeafFacts leaf5781Box leaf5781Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5781Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712997888) }) = true
      norm_num [leaf5781Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5781CertificateValid :
    WideCertificateValid leaf5781Box leaf5781Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi267ValidityFacts
    leaf5781LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5781CoverageChecked :
    coverageCheck (innerAD leaf5781Box) leaf5781InnerLog = true := by
  rfl'

private theorem leaf5781InnerLogValid :
    leaf5781InnerLog.Valid 8 (innerAD leaf5781Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint90PositiveFacts.valid leaf5781CoverageChecked

private noncomputable def leaf5781InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453687/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5781InputLogOnePlusV_eq :
    leaf5781InputLogOnePlusV = outerEnclosure 24
      (leaf5781Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5781RoundedFacts : LeafRoundedFacts 8
    leaf5781Certificate.logOnePlusV leaf5781InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5781InputLogOnePlusV_eq }

private noncomputable def leaf5781Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi267InputQChi innerPair293Input
    leaf5781InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5781LowerChecked :
    lowerCheck 24 leaf5781Box leaf5781Inputs = true := by
  rfl'

private theorem leaf5781CoversExact : CoversExact 8
    leaf5781Box leaf5781Certificate leaf5781InnerLog leaf5781Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi267RoundedFacts
    innerPair293RoundedFacts leaf5781RoundedFacts (by rfl)

private theorem leaf5781FlatSound : Sound leaf5781Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5781CertificateValid
    leaf5781InnerLogValid leaf5781CoversExact leaf5781LowerChecked

private noncomputable def leaf5782Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (7/16), chiHi := (57/128) }

private noncomputable def leaf5782Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435793/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712939520) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (675749265/536870912) }, upper := { exponent := 1, mantissa := (655/512) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi267LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429336061/137425879040) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf5782InnerLog : WideLogData :=
  innerPair293Data

set_option maxRecDepth 1000000 in
private theorem leaf5782LocalValidity :
    LeafFacts leaf5782Box leaf5782Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5782Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712939520) }) = true
      norm_num [leaf5782Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5782CertificateValid :
    WideCertificateValid leaf5782Box leaf5782Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi267ValidityFacts
    leaf5782LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5782CoverageChecked :
    coverageCheck (innerAD leaf5782Box) leaf5782InnerLog = true := by
  rfl'

private theorem leaf5782InnerLogValid :
    leaf5782InnerLog.Valid 8 (innerAD leaf5782Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint90PositiveFacts.valid leaf5782CoverageChecked

private noncomputable def leaf5782InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629503/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5782InputLogOnePlusV_eq :
    leaf5782InputLogOnePlusV = outerEnclosure 24
      (leaf5782Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5782RoundedFacts : LeafRoundedFacts 8
    leaf5782Certificate.logOnePlusV leaf5782InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5782InputLogOnePlusV_eq }

private noncomputable def leaf5782Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi267InputQChi innerPair293Input
    leaf5782InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5782LowerChecked :
    lowerCheck 24 leaf5782Box leaf5782Inputs = true := by
  rfl'

private theorem leaf5782CoversExact : CoversExact 8
    leaf5782Box leaf5782Certificate leaf5782InnerLog leaf5782Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi267RoundedFacts
    innerPair293RoundedFacts leaf5782RoundedFacts (by rfl)

private theorem leaf5782FlatSound : Sound leaf5782Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5782CertificateValid
    leaf5782InnerLogValid leaf5782CoversExact leaf5782LowerChecked

private noncomputable def leaf5783Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (57/128), chiHi := (29/64) }

private noncomputable def leaf5783Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435793/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712884224) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (679287993/536870912) }, upper := { exponent := 1, mantissa := (5267/4096) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi268LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429280765/137425768448) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf5783InnerLog : WideLogData :=
  innerPair294Data

set_option maxRecDepth 1000000 in
private theorem leaf5783LocalValidity :
    LeafFacts leaf5783Box leaf5783Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5783Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712884224) }) = true
      norm_num [leaf5783Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5783CertificateValid :
    WideCertificateValid leaf5783Box leaf5783Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi268ValidityFacts
    leaf5783LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5783CoverageChecked :
    coverageCheck (innerAD leaf5783Box) leaf5783InnerLog = true := by
  rfl'

private theorem leaf5783InnerLogValid :
    leaf5783InnerLog.Valid 8 (innerAD leaf5783Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint91PositiveFacts.valid leaf5783CoverageChecked

private noncomputable def leaf5783InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814755/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5783InputLogOnePlusV_eq :
    leaf5783InputLogOnePlusV = outerEnclosure 24
      (leaf5783Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5783RoundedFacts : LeafRoundedFacts 8
    leaf5783Certificate.logOnePlusV leaf5783InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5783InputLogOnePlusV_eq }

private noncomputable def leaf5783Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi268InputQChi innerPair294Input
    leaf5783InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5783LowerChecked :
    lowerCheck 24 leaf5783Box leaf5783Inputs = true := by
  rfl'

private theorem leaf5783CoversExact : CoversExact 8
    leaf5783Box leaf5783Certificate leaf5783InnerLog leaf5783Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi268RoundedFacts
    innerPair294RoundedFacts leaf5783RoundedFacts (by rfl)

private theorem leaf5783FlatSound : Sound leaf5783Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5783CertificateValid
    leaf5783InnerLogValid leaf5783CoversExact leaf5783LowerChecked

private noncomputable def leaf5784Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (57/128), chiHi := (29/64) }

private noncomputable def leaf5784Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435795/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712824832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (683023315/536870912) }, upper := { exponent := 1, mantissa := (331/256) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi268LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429221373/137425649664) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf5784InnerLog : WideLogData :=
  innerPair294Data

set_option maxRecDepth 1000000 in
private theorem leaf5784LocalValidity :
    LeafFacts leaf5784Box leaf5784Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5784Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712824832) }) = true
      norm_num [leaf5784Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5784CertificateValid :
    WideCertificateValid leaf5784Box leaf5784Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi268ValidityFacts
    leaf5784LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5784CoverageChecked :
    coverageCheck (innerAD leaf5784Box) leaf5784InnerLog = true := by
  rfl'

private theorem leaf5784InnerLogValid :
    leaf5784InnerLog.Valid 8 (innerAD leaf5784Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint91PositiveFacts.valid leaf5784CoverageChecked

private noncomputable def leaf5784InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629517/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5784InputLogOnePlusV_eq :
    leaf5784InputLogOnePlusV = outerEnclosure 24
      (leaf5784Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5784RoundedFacts : LeafRoundedFacts 8
    leaf5784Certificate.logOnePlusV leaf5784InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5784InputLogOnePlusV_eq }

private noncomputable def leaf5784Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi268InputQChi innerPair294Input
    leaf5784InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5784LowerChecked :
    lowerCheck 24 leaf5784Box leaf5784Inputs = true := by
  rfl'

private theorem leaf5784CoversExact : CoversExact 8
    leaf5784Box leaf5784Certificate leaf5784InnerLog leaf5784Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi268RoundedFacts
    innerPair294RoundedFacts leaf5784RoundedFacts (by rfl)

private theorem leaf5784FlatSound : Sound leaf5784Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5784CertificateValid
    leaf5784InnerLogValid leaf5784CoversExact leaf5784LowerChecked

private noncomputable def leaf5785Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (29/64), chiHi := (59/128) }

private noncomputable def leaf5785Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435791/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712891392) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (678894803/536870912) }, upper := { exponent := 1, mantissa := (10527/8192) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi269LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429287933/137425782784) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf5785InnerLog : WideLogData :=
  innerPair294Data

set_option maxRecDepth 1000000 in
private theorem leaf5785LocalValidity :
    LeafFacts leaf5785Box leaf5785Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5785Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712891392) }) = true
      norm_num [leaf5785Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5785CertificateValid :
    WideCertificateValid leaf5785Box leaf5785Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi269ValidityFacts
    leaf5785LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5785CoverageChecked :
    coverageCheck (innerAD leaf5785Box) leaf5785InnerLog = true := by
  rfl'

private theorem leaf5785InnerLogValid :
    leaf5785InnerLog.Valid 8 (innerAD leaf5785Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint91PositiveFacts.valid leaf5785CoverageChecked

private noncomputable def leaf5785InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629509/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5785InputLogOnePlusV_eq :
    leaf5785InputLogOnePlusV = outerEnclosure 24
      (leaf5785Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5785RoundedFacts : LeafRoundedFacts 8
    leaf5785Certificate.logOnePlusV leaf5785InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5785InputLogOnePlusV_eq }

private noncomputable def leaf5785Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi269InputQChi innerPair294Input
    leaf5785InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5785LowerChecked :
    lowerCheck 24 leaf5785Box leaf5785Inputs = true := by
  rfl'

private theorem leaf5785CoversExact : CoversExact 8
    leaf5785Box leaf5785Certificate leaf5785InnerLog leaf5785Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi269RoundedFacts
    innerPair294RoundedFacts leaf5785RoundedFacts (by rfl)

private theorem leaf5785FlatSound : Sound leaf5785Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5785CertificateValid
    leaf5785InnerLogValid leaf5785CoversExact leaf5785LowerChecked

private noncomputable def leaf5786Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (29/64), chiHi := (59/128) }

private noncomputable def leaf5786Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435793/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712830976) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (682695657/536870912) }, upper := { exponent := 1, mantissa := (5293/4096) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi269LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429227517/137425661952) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf5786InnerLog : WideLogData :=
  innerPair294Data

set_option maxRecDepth 1000000 in
private theorem leaf5786LocalValidity :
    LeafFacts leaf5786Box leaf5786Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5786Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712830976) }) = true
      norm_num [leaf5786Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5786CertificateValid :
    WideCertificateValid leaf5786Box leaf5786Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi269ValidityFacts
    leaf5786LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5786CoverageChecked :
    coverageCheck (innerAD leaf5786Box) leaf5786InnerLog = true := by
  rfl'

private theorem leaf5786InnerLogValid :
    leaf5786InnerLog.Valid 8 (innerAD leaf5786Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint91PositiveFacts.valid leaf5786CoverageChecked

private noncomputable def leaf5786InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907379/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5786InputLogOnePlusV_eq :
    leaf5786InputLogOnePlusV = outerEnclosure 24
      (leaf5786Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5786RoundedFacts : LeafRoundedFacts 8
    leaf5786Certificate.logOnePlusV leaf5786InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5786InputLogOnePlusV_eq }

private noncomputable def leaf5786Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi269InputQChi innerPair294Input
    leaf5786InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5786LowerChecked :
    lowerCheck 24 leaf5786Box leaf5786Inputs = true := by
  rfl'

private theorem leaf5786CoversExact : CoversExact 8
    leaf5786Box leaf5786Certificate leaf5786InnerLog leaf5786Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi269RoundedFacts
    innerPair294RoundedFacts leaf5786RoundedFacts (by rfl)

private theorem leaf5786FlatSound : Sound leaf5786Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5786CertificateValid
    leaf5786InnerLogValid leaf5786CoversExact leaf5786LowerChecked

private noncomputable def leaf5787Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (59/128), chiHi := (15/32) }

private noncomputable def leaf5787Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435793/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712779776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (685972257/536870912) }, upper := { exponent := 1, mantissa := (2659/2048) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi270LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429176317/137425559552) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf5787InnerLog : WideLogData :=
  innerPair294Data

set_option maxRecDepth 1000000 in
private theorem leaf5787LocalValidity :
    LeafFacts leaf5787Box leaf5787Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5787Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712779776) }) = true
      norm_num [leaf5787Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5787CertificateValid :
    WideCertificateValid leaf5787Box leaf5787Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi270ValidityFacts
    leaf5787LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5787CoverageChecked :
    coverageCheck (innerAD leaf5787Box) leaf5787InnerLog = true := by
  rfl'

private theorem leaf5787InnerLogValid :
    leaf5787InnerLog.Valid 8 (innerAD leaf5787Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint91PositiveFacts.valid leaf5787CoverageChecked

private noncomputable def leaf5787InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814761/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5787InputLogOnePlusV_eq :
    leaf5787InputLogOnePlusV = outerEnclosure 24
      (leaf5787Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5787RoundedFacts : LeafRoundedFacts 8
    leaf5787Certificate.logOnePlusV leaf5787InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5787InputLogOnePlusV_eq }

private noncomputable def leaf5787Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi270InputQChi innerPair294Input
    leaf5787InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5787LowerChecked :
    lowerCheck 24 leaf5787Box leaf5787Inputs = true := by
  rfl'

private theorem leaf5787CoversExact : CoversExact 8
    leaf5787Box leaf5787Certificate leaf5787InnerLog leaf5787Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi270RoundedFacts
    innerPair294RoundedFacts leaf5787RoundedFacts (by rfl)

private theorem leaf5787FlatSound : Sound leaf5787Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5787CertificateValid
    leaf5787InnerLogValid leaf5787CoversExact leaf5787LowerChecked

private noncomputable def leaf5788Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (59/128), chiHi := (15/32) }

private noncomputable def leaf5788Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435795/268435456) }, vSqrt := { lower := (65529/65536), upper := (4042140973/4041924608) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (689838643/536870912) }, upper := { exponent := 1, mantissa := (1337/1024) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi270LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (8084065581/8083849216) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf5788InnerLog : WideLogData :=
  innerPair339Data

set_option maxRecDepth 1000000 in
private theorem leaf5788LocalValidity :
    LeafFacts leaf5788Box leaf5788Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5788Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4042140973/4041924608) }) = true
      norm_num [leaf5788Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5788CertificateValid :
    WideCertificateValid leaf5788Box leaf5788Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi270ValidityFacts
    leaf5788LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5788CoverageChecked :
    coverageCheck (innerAD leaf5788Box) leaf5788InnerLog = true := by
  rfl'

private theorem leaf5788InnerLogValid :
    leaf5788InnerLog.Valid 8 (innerAD leaf5788Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint91PositiveFacts.valid leaf5788CoverageChecked

private noncomputable def leaf5788InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814765/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5788InputLogOnePlusV_eq :
    leaf5788InputLogOnePlusV = outerEnclosure 24
      (leaf5788Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5788RoundedFacts : LeafRoundedFacts 8
    leaf5788Certificate.logOnePlusV leaf5788InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5788InputLogOnePlusV_eq }

private noncomputable def leaf5788Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi270InputQChi innerPair339Input
    leaf5788InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5788LowerChecked :
    lowerCheck 24 leaf5788Box leaf5788Inputs = true := by
  rfl'

private theorem leaf5788CoversExact : CoversExact 8
    leaf5788Box leaf5788Certificate leaf5788InnerLog leaf5788Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi270RoundedFacts
    innerPair339RoundedFacts leaf5788RoundedFacts (by rfl)

private theorem leaf5788FlatSound : Sound leaf5788Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5788CertificateValid
    leaf5788InnerLogValid leaf5788CoversExact leaf5788LowerChecked

private noncomputable def leaf5789Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (29/64), chiHi := (59/128) }

private noncomputable def leaf5789Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435795/268435456) }, vSqrt := { lower := (65529/65536), upper := (4042140973/4041927680) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (686496511/536870912) }, upper := { exponent := 1, mantissa := (10645/8192) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi269LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (8084068653/8083855360) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf5789InnerLog : WideLogData :=
  innerPair294Data

set_option maxRecDepth 1000000 in
private theorem leaf5789LocalValidity :
    LeafFacts leaf5789Box leaf5789Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5789Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4042140973/4041927680) }) = true
      norm_num [leaf5789Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5789CertificateValid :
    WideCertificateValid leaf5789Box leaf5789Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi269ValidityFacts
    leaf5789LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5789CoverageChecked :
    coverageCheck (innerAD leaf5789Box) leaf5789InnerLog = true := by
  rfl'

private theorem leaf5789InnerLogValid :
    leaf5789InnerLog.Valid 8 (innerAD leaf5789Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint91PositiveFacts.valid leaf5789CoverageChecked

private noncomputable def leaf5789InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629523/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5789InputLogOnePlusV_eq :
    leaf5789InputLogOnePlusV = outerEnclosure 24
      (leaf5789Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5789RoundedFacts : LeafRoundedFacts 8
    leaf5789Certificate.logOnePlusV leaf5789InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5789InputLogOnePlusV_eq }

private noncomputable def leaf5789Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi269InputQChi innerPair294Input
    leaf5789InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5789LowerChecked :
    lowerCheck 24 leaf5789Box leaf5789Inputs = true := by
  rfl'

private theorem leaf5789CoversExact : CoversExact 8
    leaf5789Box leaf5789Certificate leaf5789InnerLog leaf5789Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi269RoundedFacts
    innerPair294RoundedFacts leaf5789RoundedFacts (by rfl)

private theorem leaf5789FlatSound : Sound leaf5789Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5789CertificateValid
    leaf5789InnerLogValid leaf5789CoversExact leaf5789LowerChecked

private noncomputable def leaf5790Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (29/64), chiHi := (59/128) }

private noncomputable def leaf5790Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435797/268435456) }, vSqrt := { lower := (8191/8192), upper := (5285876657/5285593088) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (690297365/536870912) }, upper := { exponent := 1, mantissa := (669/512) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi269LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (10571469745/10571186176) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf5790InnerLog : WideLogData :=
  innerPair339Data

set_option maxRecDepth 1000000 in
private theorem leaf5790LocalValidity :
    LeafFacts leaf5790Box leaf5790Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5790Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5285876657/5285593088) }) = true
      norm_num [leaf5790Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5790CertificateValid :
    WideCertificateValid leaf5790Box leaf5790Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi269ValidityFacts
    leaf5790LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5790CoverageChecked :
    coverageCheck (innerAD leaf5790Box) leaf5790InnerLog = true := by
  rfl'

private theorem leaf5790InnerLogValid :
    leaf5790InnerLog.Valid 8 (innerAD leaf5790Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint91PositiveFacts.valid leaf5790CoverageChecked

private noncomputable def leaf5790InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629531/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5790InputLogOnePlusV_eq :
    leaf5790InputLogOnePlusV = outerEnclosure 24
      (leaf5790Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5790RoundedFacts : LeafRoundedFacts 8
    leaf5790Certificate.logOnePlusV leaf5790InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5790InputLogOnePlusV_eq }

private noncomputable def leaf5790Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi269InputQChi innerPair339Input
    leaf5790InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5790LowerChecked :
    lowerCheck 24 leaf5790Box leaf5790Inputs = true := by
  rfl'

private theorem leaf5790CoversExact : CoversExact 8
    leaf5790Box leaf5790Certificate leaf5790InnerLog leaf5790Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi269RoundedFacts
    innerPair339RoundedFacts leaf5790RoundedFacts (by rfl)

private theorem leaf5790FlatSound : Sound leaf5790Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5790CertificateValid
    leaf5790InnerLogValid leaf5790CoversExact leaf5790LowerChecked

private noncomputable def leaf5791Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (59/128), chiHi := (15/32) }

private noncomputable def leaf5791Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435797/268435456) }, vSqrt := { lower := (65529/65536), upper := (5285876657/5285588992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (693705029/536870912) }, upper := { exponent := 1, mantissa := (2689/2048) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi270LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (10571465649/10571177984) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf5791InnerLog : WideLogData :=
  innerPair340Data

set_option maxRecDepth 1000000 in
private theorem leaf5791LocalValidity :
    LeafFacts leaf5791Box leaf5791Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5791Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (5285876657/5285588992) }) = true
      norm_num [leaf5791Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5791CertificateValid :
    WideCertificateValid leaf5791Box leaf5791Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi270ValidityFacts
    leaf5791LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5791CoverageChecked :
    coverageCheck (innerAD leaf5791Box) leaf5791InnerLog = true := by
  rfl'

private theorem leaf5791InnerLogValid :
    leaf5791InnerLog.Valid 8 (innerAD leaf5791Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint92PositiveFacts.valid leaf5791CoverageChecked

private noncomputable def leaf5791InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629537/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5791InputLogOnePlusV_eq :
    leaf5791InputLogOnePlusV = outerEnclosure 24
      (leaf5791Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5791RoundedFacts : LeafRoundedFacts 8
    leaf5791Certificate.logOnePlusV leaf5791InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5791InputLogOnePlusV_eq }

private noncomputable def leaf5791Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi270InputQChi innerPair340Input
    leaf5791InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5791LowerChecked :
    lowerCheck 24 leaf5791Box leaf5791Inputs = true := by
  rfl'

private theorem leaf5791CoversExact : CoversExact 8
    leaf5791Box leaf5791Certificate leaf5791InnerLog leaf5791Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi270RoundedFacts
    innerPair340RoundedFacts leaf5791RoundedFacts (by rfl)

private theorem leaf5791FlatSound : Sound leaf5791Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5791CertificateValid
    leaf5791InnerLogValid leaf5791CoversExact leaf5791LowerChecked

private noncomputable def leaf5792Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (59/128), chiHi := (15/32) }

private noncomputable def leaf5792Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435799/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712595456) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (697571415/536870912) }, upper := { exponent := 1, mantissa := (169/128) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi270LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428991997/137425190912) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf5792InnerLog : WideLogData :=
  innerPair340Data

set_option maxRecDepth 1000000 in
private theorem leaf5792LocalValidity :
    LeafFacts leaf5792Box leaf5792Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5792Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712595456) }) = true
      norm_num [leaf5792Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5792CertificateValid :
    WideCertificateValid leaf5792Box leaf5792Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi270ValidityFacts
    leaf5792LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5792CoverageChecked :
    coverageCheck (innerAD leaf5792Box) leaf5792InnerLog = true := by
  rfl'

private theorem leaf5792InnerLogValid :
    leaf5792InnerLog.Valid 8 (innerAD leaf5792Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint92PositiveFacts.valid leaf5792CoverageChecked

private noncomputable def leaf5792InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629545/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5792InputLogOnePlusV_eq :
    leaf5792InputLogOnePlusV = outerEnclosure 24
      (leaf5792Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5792RoundedFacts : LeafRoundedFacts 8
    leaf5792Certificate.logOnePlusV leaf5792InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5792InputLogOnePlusV_eq }

private noncomputable def leaf5792Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi270InputQChi innerPair340Input
    leaf5792InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5792LowerChecked :
    lowerCheck 24 leaf5792Box leaf5792Inputs = true := by
  rfl'

private theorem leaf5792CoversExact : CoversExact 8
    leaf5792Box leaf5792Certificate leaf5792InnerLog leaf5792Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi270RoundedFacts
    innerPair340RoundedFacts leaf5792RoundedFacts (by rfl)

private theorem leaf5792FlatSound : Sound leaf5792Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5792CertificateValid
    leaf5792InnerLogValid leaf5792CoversExact leaf5792LowerChecked

private noncomputable def leaf5793Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (15/32), chiHi := (61/128) }

private noncomputable def leaf5793Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435787/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712918016) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (677322039/536870912) }, upper := { exponent := 1, mantissa := (10501/8192) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi271LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429314557/137425836032) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf5793InnerLog : WideLogData :=
  innerPair294Data

set_option maxRecDepth 1000000 in
private theorem leaf5793LocalValidity :
    LeafFacts leaf5793Box leaf5793Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5793Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712918016) }) = true
      norm_num [leaf5793Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5793CertificateValid :
    WideCertificateValid leaf5793Box leaf5793Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi271ValidityFacts
    leaf5793LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5793CoverageChecked :
    coverageCheck (innerAD leaf5793Box) leaf5793InnerLog = true := by
  rfl'

private theorem leaf5793InnerLogValid :
    leaf5793InnerLog.Valid 8 (innerAD leaf5793Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint91PositiveFacts.valid leaf5793CoverageChecked

private noncomputable def leaf5793InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629505/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5793InputLogOnePlusV_eq :
    leaf5793InputLogOnePlusV = outerEnclosure 24
      (leaf5793Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5793RoundedFacts : LeafRoundedFacts 8
    leaf5793Certificate.logOnePlusV leaf5793InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5793InputLogOnePlusV_eq }

private noncomputable def leaf5793Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi271InputQChi innerPair294Input
    leaf5793InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5793LowerChecked :
    lowerCheck 24 leaf5793Box leaf5793Inputs = true := by
  rfl'

private theorem leaf5793CoversExact : CoversExact 8
    leaf5793Box leaf5793Certificate leaf5793InnerLog leaf5793Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi271RoundedFacts
    innerPair294RoundedFacts leaf5793RoundedFacts (by rfl)

private theorem leaf5793FlatSound : Sound leaf5793Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5793CertificateValid
    leaf5793InnerLogValid leaf5793CoversExact leaf5793LowerChecked

private noncomputable def leaf5794Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (15/32), chiHi := (61/128) }

private noncomputable def leaf5794Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435789/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712855552) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (681253957/536870912) }, upper := { exponent := 1, mantissa := (5281/4096) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi271LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429252093/137425711104) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf5794InnerLog : WideLogData :=
  innerPair294Data

set_option maxRecDepth 1000000 in
private theorem leaf5794LocalValidity :
    LeafFacts leaf5794Box leaf5794Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5794Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712855552) }) = true
      norm_num [leaf5794Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5794CertificateValid :
    WideCertificateValid leaf5794Box leaf5794Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi271ValidityFacts
    leaf5794LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5794CoverageChecked :
    coverageCheck (innerAD leaf5794Box) leaf5794InnerLog = true := by
  rfl'

private theorem leaf5794InnerLogValid :
    leaf5794InnerLog.Valid 8 (innerAD leaf5794Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint91PositiveFacts.valid leaf5794CoverageChecked

private noncomputable def leaf5794InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629513/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5794InputLogOnePlusV_eq :
    leaf5794InputLogOnePlusV = outerEnclosure 24
      (leaf5794Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5794RoundedFacts : LeafRoundedFacts 8
    leaf5794Certificate.logOnePlusV leaf5794InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5794InputLogOnePlusV_eq }

private noncomputable def leaf5794Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi271InputQChi innerPair294Input
    leaf5794InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5794LowerChecked :
    lowerCheck 24 leaf5794Box leaf5794Inputs = true := by
  rfl'

private theorem leaf5794CoversExact : CoversExact 8
    leaf5794Box leaf5794Certificate leaf5794InnerLog leaf5794Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi271RoundedFacts
    innerPair294RoundedFacts leaf5794RoundedFacts (by rfl)

private theorem leaf5794FlatSound : Sound leaf5794Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5794CertificateValid
    leaf5794InnerLogValid leaf5794CoversExact leaf5794LowerChecked

private noncomputable def leaf5795Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (61/128), chiHi := (31/64) }

private noncomputable def leaf5795Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435789/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712810496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (684137365/536870912) }, upper := { exponent := 1, mantissa := (5303/4096) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi272LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429207037/137425620992) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf5795InnerLog : WideLogData :=
  innerPair294Data

set_option maxRecDepth 1000000 in
private theorem leaf5795LocalValidity :
    LeafFacts leaf5795Box leaf5795Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5795Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712810496) }) = true
      norm_num [leaf5795Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5795CertificateValid :
    WideCertificateValid leaf5795Box leaf5795Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi272ValidityFacts
    leaf5795LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5795CoverageChecked :
    coverageCheck (innerAD leaf5795Box) leaf5795InnerLog = true := by
  rfl'

private theorem leaf5795InnerLogValid :
    leaf5795InnerLog.Valid 8 (innerAD leaf5795Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint91PositiveFacts.valid leaf5795CoverageChecked

private noncomputable def leaf5795InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629519/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5795InputLogOnePlusV_eq :
    leaf5795InputLogOnePlusV = outerEnclosure 24
      (leaf5795Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5795RoundedFacts : LeafRoundedFacts 8
    leaf5795Certificate.logOnePlusV leaf5795InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5795InputLogOnePlusV_eq }

private noncomputable def leaf5795Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi272InputQChi innerPair294Input
    leaf5795InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5795LowerChecked :
    lowerCheck 24 leaf5795Box leaf5795Inputs = true := by
  rfl'

private theorem leaf5795CoversExact : CoversExact 8
    leaf5795Box leaf5795Certificate leaf5795InnerLog leaf5795Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi272RoundedFacts
    innerPair294RoundedFacts leaf5795RoundedFacts (by rfl)

private theorem leaf5795FlatSound : Sound leaf5795Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5795CertificateValid
    leaf5795InnerLogValid leaf5795CoversExact leaf5795LowerChecked

private noncomputable def leaf5796Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (61/128), chiHi := (31/64) }

private noncomputable def leaf5796Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435791/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712747008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (688134815/536870912) }, upper := { exponent := 1, mantissa := (2667/2048) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi272LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429143549/137425494016) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf5796InnerLog : WideLogData :=
  innerPair339Data

set_option maxRecDepth 1000000 in
private theorem leaf5796LocalValidity :
    LeafFacts leaf5796Box leaf5796Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5796Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712747008) }) = true
      norm_num [leaf5796Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5796CertificateValid :
    WideCertificateValid leaf5796Box leaf5796Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi272ValidityFacts
    leaf5796LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5796CoverageChecked :
    coverageCheck (innerAD leaf5796Box) leaf5796InnerLog = true := by
  rfl'

private theorem leaf5796InnerLogValid :
    leaf5796InnerLog.Valid 8 (innerAD leaf5796Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint91PositiveFacts.valid leaf5796CoverageChecked

private noncomputable def leaf5796InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814763/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5796InputLogOnePlusV_eq :
    leaf5796InputLogOnePlusV = outerEnclosure 24
      (leaf5796Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5796RoundedFacts : LeafRoundedFacts 8
    leaf5796Certificate.logOnePlusV leaf5796InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5796InputLogOnePlusV_eq }

private noncomputable def leaf5796Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi272InputQChi innerPair339Input
    leaf5796InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5796LowerChecked :
    lowerCheck 24 leaf5796Box leaf5796Inputs = true := by
  rfl'

private theorem leaf5796CoversExact : CoversExact 8
    leaf5796Box leaf5796Certificate leaf5796InnerLog leaf5796Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi272RoundedFacts
    innerPair339RoundedFacts leaf5796RoundedFacts (by rfl)

private theorem leaf5796FlatSound : Sound leaf5796Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5796CertificateValid
    leaf5796InnerLogValid leaf5796CoversExact leaf5796LowerChecked

private noncomputable def leaf5797Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (15/32), chiHi := (61/128) }

private noncomputable def leaf5797Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435791/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712793088) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (685185875/536870912) }, upper := { exponent := 1, mantissa := (10623/8192) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi271LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429189629/137425586176) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf5797InnerLog : WideLogData :=
  innerPair294Data

set_option maxRecDepth 1000000 in
private theorem leaf5797LocalValidity :
    LeafFacts leaf5797Box leaf5797Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5797Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712793088) }) = true
      norm_num [leaf5797Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5797CertificateValid :
    WideCertificateValid leaf5797Box leaf5797Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi271ValidityFacts
    leaf5797LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5797CoverageChecked :
    coverageCheck (innerAD leaf5797Box) leaf5797InnerLog = true := by
  rfl'

private theorem leaf5797InnerLogValid :
    leaf5797InnerLog.Valid 8 (innerAD leaf5797Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint91PositiveFacts.valid leaf5797CoverageChecked

private noncomputable def leaf5797InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629521/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5797InputLogOnePlusV_eq :
    leaf5797InputLogOnePlusV = outerEnclosure 24
      (leaf5797Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5797RoundedFacts : LeafRoundedFacts 8
    leaf5797Certificate.logOnePlusV leaf5797InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5797InputLogOnePlusV_eq }

private noncomputable def leaf5797Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi271InputQChi innerPair294Input
    leaf5797InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5797LowerChecked :
    lowerCheck 24 leaf5797Box leaf5797Inputs = true := by
  rfl'

private theorem leaf5797CoversExact : CoversExact 8
    leaf5797Box leaf5797Certificate leaf5797InnerLog leaf5797Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi271RoundedFacts
    innerPair294RoundedFacts leaf5797RoundedFacts (by rfl)

private theorem leaf5797FlatSound : Sound leaf5797Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5797CertificateValid
    leaf5797InnerLogValid leaf5797CoversExact leaf5797LowerChecked

private noncomputable def leaf5798Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (15/32), chiHi := (61/128) }

private noncomputable def leaf5798Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435793/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712730624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (689117793/536870912) }, upper := { exponent := 1, mantissa := (2671/2048) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi271LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429127165/137425461248) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf5798InnerLog : WideLogData :=
  innerPair339Data

set_option maxRecDepth 1000000 in
private theorem leaf5798LocalValidity :
    LeafFacts leaf5798Box leaf5798Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5798Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712730624) }) = true
      norm_num [leaf5798Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5798CertificateValid :
    WideCertificateValid leaf5798Box leaf5798Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi271ValidityFacts
    leaf5798LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5798CoverageChecked :
    coverageCheck (innerAD leaf5798Box) leaf5798InnerLog = true := by
  rfl'

private theorem leaf5798InnerLogValid :
    leaf5798InnerLog.Valid 8 (innerAD leaf5798Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint91PositiveFacts.valid leaf5798CoverageChecked

private noncomputable def leaf5798InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453691/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5798InputLogOnePlusV_eq :
    leaf5798InputLogOnePlusV = outerEnclosure 24
      (leaf5798Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5798RoundedFacts : LeafRoundedFacts 8
    leaf5798Certificate.logOnePlusV leaf5798InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5798InputLogOnePlusV_eq }

private noncomputable def leaf5798Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi271InputQChi innerPair339Input
    leaf5798InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5798LowerChecked :
    lowerCheck 24 leaf5798Box leaf5798Inputs = true := by
  rfl'

private theorem leaf5798CoversExact : CoversExact 8
    leaf5798Box leaf5798Certificate leaf5798InnerLog leaf5798Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi271RoundedFacts
    innerPair339RoundedFacts leaf5798RoundedFacts (by rfl)

private theorem leaf5798FlatSound : Sound leaf5798Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5798CertificateValid
    leaf5798InnerLogValid leaf5798CoversExact leaf5798LowerChecked

private noncomputable def leaf5799Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (61/128), chiHi := (31/64) }

private noncomputable def leaf5799Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435793/268435456) }, vSqrt := { lower := (65529/65536), upper := (310933921/310917120) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (692132265/536870912) }, upper := { exponent := 1, mantissa := (5365/4096) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi272LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (621851041/621834240) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf5799InnerLog : WideLogData :=
  innerPair339Data

set_option maxRecDepth 1000000 in
private theorem leaf5799LocalValidity :
    LeafFacts leaf5799Box leaf5799Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5799Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (310933921/310917120) }) = true
      norm_num [leaf5799Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5799CertificateValid :
    WideCertificateValid leaf5799Box leaf5799Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi272ValidityFacts
    leaf5799LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5799CoverageChecked :
    coverageCheck (innerAD leaf5799Box) leaf5799InnerLog = true := by
  rfl'

private theorem leaf5799InnerLogValid :
    leaf5799InnerLog.Valid 8 (innerAD leaf5799Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint91PositiveFacts.valid leaf5799CoverageChecked

private noncomputable def leaf5799InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814767/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5799InputLogOnePlusV_eq :
    leaf5799InputLogOnePlusV = outerEnclosure 24
      (leaf5799Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5799RoundedFacts : LeafRoundedFacts 8
    leaf5799Certificate.logOnePlusV leaf5799InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5799InputLogOnePlusV_eq }

private noncomputable def leaf5799Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi272InputQChi innerPair339Input
    leaf5799InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5799LowerChecked :
    lowerCheck 24 leaf5799Box leaf5799Inputs = true := by
  rfl'

private theorem leaf5799CoversExact : CoversExact 8
    leaf5799Box leaf5799Certificate leaf5799InnerLog leaf5799Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi272RoundedFacts
    innerPair339RoundedFacts leaf5799RoundedFacts (by rfl)

private theorem leaf5799FlatSound : Sound leaf5799Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5799CertificateValid
    leaf5799InnerLogValid leaf5799CoversExact leaf5799LowerChecked

private noncomputable def leaf5800Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (61/128), chiHi := (31/64) }

private noncomputable def leaf5800Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435795/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712620032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (696129715/536870912) }, upper := { exponent := 1, mantissa := (1349/1024) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi272LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429016573/137425240064) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf5800InnerLog : WideLogData :=
  innerPair340Data

set_option maxRecDepth 1000000 in
private theorem leaf5800LocalValidity :
    LeafFacts leaf5800Box leaf5800Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5800Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712620032) }) = true
      norm_num [leaf5800Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5800CertificateValid :
    WideCertificateValid leaf5800Box leaf5800Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi272ValidityFacts
    leaf5800LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5800CoverageChecked :
    coverageCheck (innerAD leaf5800Box) leaf5800InnerLog = true := by
  rfl'

private theorem leaf5800InnerLogValid :
    leaf5800InnerLog.Valid 8 (innerAD leaf5800Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint92PositiveFacts.valid leaf5800CoverageChecked

private noncomputable def leaf5800InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814771/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5800InputLogOnePlusV_eq :
    leaf5800InputLogOnePlusV = outerEnclosure 24
      (leaf5800Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5800RoundedFacts : LeafRoundedFacts 8
    leaf5800Certificate.logOnePlusV leaf5800InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5800InputLogOnePlusV_eq }

private noncomputable def leaf5800Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi272InputQChi innerPair340Input
    leaf5800InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5800LowerChecked :
    lowerCheck 24 leaf5800Box leaf5800Inputs = true := by
  rfl'

private theorem leaf5800CoversExact : CoversExact 8
    leaf5800Box leaf5800Certificate leaf5800InnerLog leaf5800Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi272RoundedFacts
    innerPair340RoundedFacts leaf5800RoundedFacts (by rfl)

private theorem leaf5800FlatSound : Sound leaf5800Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5800CertificateValid
    leaf5800InnerLogValid leaf5800CoversExact leaf5800LowerChecked

private noncomputable def leaf5801Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (31/64), chiHi := (63/128) }

private noncomputable def leaf5801Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435791/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712702976) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (690952691/536870912) }, upper := { exponent := 1, mantissa := (10711/8192) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi273LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429099517/137425405952) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf5801InnerLog : WideLogData :=
  innerPair339Data

set_option maxRecDepth 1000000 in
private theorem leaf5801LocalValidity :
    LeafFacts leaf5801Box leaf5801Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5801Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712702976) }) = true
      norm_num [leaf5801Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5801CertificateValid :
    WideCertificateValid leaf5801Box leaf5801Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi273ValidityFacts
    leaf5801LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5801CoverageChecked :
    coverageCheck (innerAD leaf5801Box) leaf5801InnerLog = true := by
  rfl'

private theorem leaf5801InnerLogValid :
    leaf5801InnerLog.Valid 8 (innerAD leaf5801Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint91PositiveFacts.valid leaf5801CoverageChecked

private noncomputable def leaf5801InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907383/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5801InputLogOnePlusV_eq :
    leaf5801InputLogOnePlusV = outerEnclosure 24
      (leaf5801Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5801RoundedFacts : LeafRoundedFacts 8
    leaf5801Certificate.logOnePlusV leaf5801InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5801InputLogOnePlusV_eq }

private noncomputable def leaf5801Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi273InputQChi innerPair339Input
    leaf5801InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5801LowerChecked :
    lowerCheck 24 leaf5801Box leaf5801Inputs = true := by
  rfl'

private theorem leaf5801CoversExact : CoversExact 8
    leaf5801Box leaf5801Certificate leaf5801InnerLog leaf5801Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi273RoundedFacts
    innerPair339RoundedFacts leaf5801RoundedFacts (by rfl)

private theorem leaf5801FlatSound : Sound leaf5801Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5801CertificateValid
    leaf5801InnerLogValid leaf5801CoversExact leaf5801LowerChecked

private noncomputable def leaf5802Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (31/64), chiHi := (63/128) }

private noncomputable def leaf5802Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435793/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712638464) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (695015673/536870912) }, upper := { exponent := 1, mantissa := (5387/4096) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi273LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429035005/137425276928) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf5802InnerLog : WideLogData :=
  innerPair340Data

set_option maxRecDepth 1000000 in
private theorem leaf5802LocalValidity :
    LeafFacts leaf5802Box leaf5802Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5802Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712638464) }) = true
      norm_num [leaf5802Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5802CertificateValid :
    WideCertificateValid leaf5802Box leaf5802Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi273ValidityFacts
    leaf5802LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5802CoverageChecked :
    coverageCheck (innerAD leaf5802Box) leaf5802InnerLog = true := by
  rfl'

private theorem leaf5802InnerLogValid :
    leaf5802InnerLog.Valid 8 (innerAD leaf5802Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint92PositiveFacts.valid leaf5802CoverageChecked

private noncomputable def leaf5802InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907385/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5802InputLogOnePlusV_eq :
    leaf5802InputLogOnePlusV = outerEnclosure 24
      (leaf5802Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5802RoundedFacts : LeafRoundedFacts 8
    leaf5802Certificate.logOnePlusV leaf5802InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5802InputLogOnePlusV_eq }

private noncomputable def leaf5802Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi273InputQChi innerPair340Input
    leaf5802InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5802LowerChecked :
    lowerCheck 24 leaf5802Box leaf5802Inputs = true := by
  rfl'

private theorem leaf5802CoversExact : CoversExact 8
    leaf5802Box leaf5802Certificate leaf5802InnerLog leaf5802Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi273RoundedFacts
    innerPair340RoundedFacts leaf5802RoundedFacts (by rfl)

private theorem leaf5802FlatSound : Sound leaf5802Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5802CertificateValid
    leaf5802InnerLogValid leaf5802CoversExact leaf5802LowerChecked

private noncomputable def leaf5803Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (63/128), chiHi := (1/2) }

private noncomputable def leaf5803Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435793/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712595456) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (697768017/536870912) }, upper := { exponent := 1, mantissa := (169/128) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi274LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137428991997/137425190912) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf5803InnerLog : WideLogData :=
  innerPair340Data

set_option maxRecDepth 1000000 in
private theorem leaf5803LocalValidity :
    LeafFacts leaf5803Box leaf5803Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5803Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712595456) }) = true
      norm_num [leaf5803Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5803CertificateValid :
    WideCertificateValid leaf5803Box leaf5803Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi274ValidityFacts
    leaf5803LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5803CoverageChecked :
    coverageCheck (innerAD leaf5803Box) leaf5803InnerLog = true := by
  rfl'

private theorem leaf5803InnerLogValid :
    leaf5803InnerLog.Valid 8 (innerAD leaf5803Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint92PositiveFacts.valid leaf5803CoverageChecked

private noncomputable def leaf5803InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629545/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5803InputLogOnePlusV_eq :
    leaf5803InputLogOnePlusV = outerEnclosure 24
      (leaf5803Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5803RoundedFacts : LeafRoundedFacts 8
    leaf5803Certificate.logOnePlusV leaf5803InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5803InputLogOnePlusV_eq }

private noncomputable def leaf5803Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi274InputQChi innerPair340Input
    leaf5803InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5803LowerChecked :
    lowerCheck 24 leaf5803Box leaf5803Inputs = true := by
  rfl'

private theorem leaf5803CoversExact : CoversExact 8
    leaf5803Box leaf5803Certificate leaf5803InnerLog leaf5803Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi274RoundedFacts
    innerPair340RoundedFacts leaf5803RoundedFacts (by rfl)

private theorem leaf5803FlatSound : Sound leaf5803Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5803CertificateValid
    leaf5803InnerLogValid leaf5803CoversExact leaf5803LowerChecked

private noncomputable def leaf5804Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (63/128), chiHi := (1/2) }

private noncomputable def leaf5804Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435795/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712529920) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (701896531/536870912) }, upper := { exponent := 1, mantissa := (85/64) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi274LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137428926461/137425059840) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf5804InnerLog : WideLogData :=
  innerPair340Data

set_option maxRecDepth 1000000 in
private theorem leaf5804LocalValidity :
    LeafFacts leaf5804Box leaf5804Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5804Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712529920) }) = true
      norm_num [leaf5804Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5804CertificateValid :
    WideCertificateValid leaf5804Box leaf5804Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi274ValidityFacts
    leaf5804LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5804CoverageChecked :
    coverageCheck (innerAD leaf5804Box) leaf5804InnerLog = true := by
  rfl'

private theorem leaf5804InnerLogValid :
    leaf5804InnerLog.Valid 8 (innerAD leaf5804Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint92PositiveFacts.valid leaf5804CoverageChecked

private noncomputable def leaf5804InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629553/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5804InputLogOnePlusV_eq :
    leaf5804InputLogOnePlusV = outerEnclosure 24
      (leaf5804Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5804RoundedFacts : LeafRoundedFacts 8
    leaf5804Certificate.logOnePlusV leaf5804InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5804InputLogOnePlusV_eq }

private noncomputable def leaf5804Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi274InputQChi innerPair340Input
    leaf5804InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5804LowerChecked :
    lowerCheck 24 leaf5804Box leaf5804Inputs = true := by
  rfl'

private theorem leaf5804CoversExact : CoversExact 8
    leaf5804Box leaf5804Certificate leaf5804InnerLog leaf5804Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi274RoundedFacts
    innerPair340RoundedFacts leaf5804RoundedFacts (by rfl)

private theorem leaf5804FlatSound : Sound leaf5804Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5804CertificateValid
    leaf5804InnerLogValid leaf5804CoversExact leaf5804LowerChecked

private noncomputable def leaf5805Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (31/64), chiHi := (63/128) }

private noncomputable def leaf5805Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435795/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712573952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (699078655/536870912) }, upper := { exponent := 1, mantissa := (10837/8192) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi273LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137428970493/137425147904) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf5805InnerLog : WideLogData :=
  innerPair340Data

set_option maxRecDepth 1000000 in
private theorem leaf5805LocalValidity :
    LeafFacts leaf5805Box leaf5805Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5805Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712573952) }) = true
      norm_num [leaf5805Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5805CertificateValid :
    WideCertificateValid leaf5805Box leaf5805Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi273ValidityFacts
    leaf5805LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5805CoverageChecked :
    coverageCheck (innerAD leaf5805Box) leaf5805InnerLog = true := by
  rfl'

private theorem leaf5805InnerLogValid :
    leaf5805InnerLog.Valid 8 (innerAD leaf5805Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint92PositiveFacts.valid leaf5805CoverageChecked

private noncomputable def leaf5805InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629547/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5805InputLogOnePlusV_eq :
    leaf5805InputLogOnePlusV = outerEnclosure 24
      (leaf5805Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5805RoundedFacts : LeafRoundedFacts 8
    leaf5805Certificate.logOnePlusV leaf5805InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5805InputLogOnePlusV_eq }

private noncomputable def leaf5805Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi273InputQChi innerPair340Input
    leaf5805InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5805LowerChecked :
    lowerCheck 24 leaf5805Box leaf5805Inputs = true := by
  rfl'

private theorem leaf5805CoversExact : CoversExact 8
    leaf5805Box leaf5805Certificate leaf5805InnerLog leaf5805Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi273RoundedFacts
    innerPair340RoundedFacts leaf5805RoundedFacts (by rfl)

private theorem leaf5805FlatSound : Sound leaf5805Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5805CertificateValid
    leaf5805InnerLogValid leaf5805CoversExact leaf5805LowerChecked

private noncomputable def leaf5806Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (31/64), chiHi := (63/128) }

private noncomputable def leaf5806Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435797/268435456) }, vSqrt := { lower := (65529/65536), upper := (4042140973/4041912320) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (703141637/536870912) }, upper := { exponent := 1, mantissa := (2725/2048) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi273LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (8084053293/8083824640) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf5806InnerLog : WideLogData :=
  innerPair340Data

set_option maxRecDepth 1000000 in
private theorem leaf5806LocalValidity :
    LeafFacts leaf5806Box leaf5806Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5806Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4042140973/4041912320) }) = true
      norm_num [leaf5806Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5806CertificateValid :
    WideCertificateValid leaf5806Box leaf5806Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi273ValidityFacts
    leaf5806LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5806CoverageChecked :
    coverageCheck (innerAD leaf5806Box) leaf5806InnerLog = true := by
  rfl'

private theorem leaf5806InnerLogValid :
    leaf5806InnerLog.Valid 8 (innerAD leaf5806Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint92PositiveFacts.valid leaf5806CoverageChecked

private noncomputable def leaf5806InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629555/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5806InputLogOnePlusV_eq :
    leaf5806InputLogOnePlusV = outerEnclosure 24
      (leaf5806Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5806RoundedFacts : LeafRoundedFacts 8
    leaf5806Certificate.logOnePlusV leaf5806InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5806InputLogOnePlusV_eq }

private noncomputable def leaf5806Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi273InputQChi innerPair340Input
    leaf5806InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5806LowerChecked :
    lowerCheck 24 leaf5806Box leaf5806Inputs = true := by
  rfl'

private theorem leaf5806CoversExact : CoversExact 8
    leaf5806Box leaf5806Certificate leaf5806InnerLog leaf5806Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi273RoundedFacts
    innerPair340RoundedFacts leaf5806RoundedFacts (by rfl)

private theorem leaf5806FlatSound : Sound leaf5806Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5806CertificateValid
    leaf5806InnerLogValid leaf5806CoversExact leaf5806LowerChecked

private noncomputable def leaf5807Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (63/128), chiHi := (1/2) }

private noncomputable def leaf5807Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435797/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712464384) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (706025045/536870912) }, upper := { exponent := 1, mantissa := (171/128) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi274LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137428860925/137424928768) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf5807InnerLog : WideLogData :=
  innerPair345Data

set_option maxRecDepth 1000000 in
private theorem leaf5807LocalValidity :
    LeafFacts leaf5807Box leaf5807Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5807Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712464384) }) = true
      norm_num [leaf5807Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5807CertificateValid :
    WideCertificateValid leaf5807Box leaf5807Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi274ValidityFacts
    leaf5807LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5807CoverageChecked :
    coverageCheck (innerAD leaf5807Box) leaf5807InnerLog = true := by
  rfl'

private theorem leaf5807InnerLogValid :
    leaf5807InnerLog.Valid 8 (innerAD leaf5807Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint92PositiveFacts.valid leaf5807CoverageChecked

private noncomputable def leaf5807InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629561/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5807InputLogOnePlusV_eq :
    leaf5807InputLogOnePlusV = outerEnclosure 24
      (leaf5807Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5807RoundedFacts : LeafRoundedFacts 8
    leaf5807Certificate.logOnePlusV leaf5807InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5807InputLogOnePlusV_eq }

private noncomputable def leaf5807Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi274InputQChi innerPair345Input
    leaf5807InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5807LowerChecked :
    lowerCheck 24 leaf5807Box leaf5807Inputs = true := by
  rfl'

private theorem leaf5807CoversExact : CoversExact 8
    leaf5807Box leaf5807Certificate leaf5807InnerLog leaf5807Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi274RoundedFacts
    innerPair345RoundedFacts leaf5807RoundedFacts (by rfl)

private theorem leaf5807FlatSound : Sound leaf5807Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5807CertificateValid
    leaf5807InnerLogValid leaf5807CoversExact leaf5807LowerChecked

private noncomputable def leaf5808Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (63/128), chiHi := (1/2) }

private noncomputable def leaf5808Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435799/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712398848) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (710153559/536870912) }, upper := { exponent := 1, mantissa := (43/32) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi274LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137428795389/137424797696) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf5808InnerLog : WideLogData :=
  innerPair345Data

set_option maxRecDepth 1000000 in
private theorem leaf5808LocalValidity :
    LeafFacts leaf5808Box leaf5808Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5808Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712398848) }) = true
      norm_num [leaf5808Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5808CertificateValid :
    WideCertificateValid leaf5808Box leaf5808Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi274ValidityFacts
    leaf5808LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5808CoverageChecked :
    coverageCheck (innerAD leaf5808Box) leaf5808InnerLog = true := by
  rfl'

private theorem leaf5808InnerLogValid :
    leaf5808InnerLog.Valid 8 (innerAD leaf5808Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint92PositiveFacts.valid leaf5808CoverageChecked

private noncomputable def leaf5808InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629569/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5808InputLogOnePlusV_eq :
    leaf5808InputLogOnePlusV = outerEnclosure 24
      (leaf5808Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5808RoundedFacts : LeafRoundedFacts 8
    leaf5808Certificate.logOnePlusV leaf5808InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5808InputLogOnePlusV_eq }

private noncomputable def leaf5808Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi274InputQChi innerPair345Input
    leaf5808InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5808LowerChecked :
    lowerCheck 24 leaf5808Box leaf5808Inputs = true := by
  rfl'

private theorem leaf5808CoversExact : CoversExact 8
    leaf5808Box leaf5808Certificate leaf5808InnerLog leaf5808Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi274RoundedFacts
    innerPair345RoundedFacts leaf5808RoundedFacts (by rfl)

private theorem leaf5808FlatSound : Sound leaf5808Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5808CertificateValid
    leaf5808InnerLogValid leaf5808CoversExact leaf5808LowerChecked

private noncomputable def leaf5809Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (15/32), chiHi := (61/128) }

private noncomputable def leaf5809Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435795/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712668160) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (693049711/536870912) }, upper := { exponent := 1, mantissa := (10745/8192) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi271LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429064701/137425336320) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf5809InnerLog : WideLogData :=
  innerPair339Data

set_option maxRecDepth 1000000 in
private theorem leaf5809LocalValidity :
    LeafFacts leaf5809Box leaf5809Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5809Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712668160) }) = true
      norm_num [leaf5809Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5809CertificateValid :
    WideCertificateValid leaf5809Box leaf5809Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi271ValidityFacts
    leaf5809LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5809CoverageChecked :
    coverageCheck (innerAD leaf5809Box) leaf5809InnerLog = true := by
  rfl'

private theorem leaf5809InnerLogValid :
    leaf5809InnerLog.Valid 8 (innerAD leaf5809Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint91PositiveFacts.valid leaf5809CoverageChecked

private noncomputable def leaf5809InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (363423/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf5809InputLogOnePlusV_eq :
    leaf5809InputLogOnePlusV = outerEnclosure 24
      (leaf5809Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5809RoundedFacts : LeafRoundedFacts 8
    leaf5809Certificate.logOnePlusV leaf5809InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5809InputLogOnePlusV_eq }

private noncomputable def leaf5809Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi271InputQChi innerPair339Input
    leaf5809InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5809LowerChecked :
    lowerCheck 24 leaf5809Box leaf5809Inputs = true := by
  rfl'

private theorem leaf5809CoversExact : CoversExact 8
    leaf5809Box leaf5809Certificate leaf5809InnerLog leaf5809Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi271RoundedFacts
    innerPair339RoundedFacts leaf5809RoundedFacts (by rfl)

private theorem leaf5809FlatSound : Sound leaf5809Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5809CertificateValid
    leaf5809InnerLogValid leaf5809CoversExact leaf5809LowerChecked

private noncomputable def leaf5810Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (15/32), chiHi := (61/128) }

private noncomputable def leaf5810Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435797/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712605696) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (696981629/536870912) }, upper := { exponent := 1, mantissa := (5403/4096) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi271LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429002237/137425211392) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf5810InnerLog : WideLogData :=
  innerPair340Data

set_option maxRecDepth 1000000 in
private theorem leaf5810LocalValidity :
    LeafFacts leaf5810Box leaf5810Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5810Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712605696) }) = true
      norm_num [leaf5810Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5810CertificateValid :
    WideCertificateValid leaf5810Box leaf5810Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi271ValidityFacts
    leaf5810LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5810CoverageChecked :
    coverageCheck (innerAD leaf5810Box) leaf5810InnerLog = true := by
  rfl'

private theorem leaf5810InnerLogValid :
    leaf5810InnerLog.Valid 8 (innerAD leaf5810Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint92PositiveFacts.valid leaf5810CoverageChecked

private noncomputable def leaf5810InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453693/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5810InputLogOnePlusV_eq :
    leaf5810InputLogOnePlusV = outerEnclosure 24
      (leaf5810Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5810RoundedFacts : LeafRoundedFacts 8
    leaf5810Certificate.logOnePlusV leaf5810InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5810InputLogOnePlusV_eq }

private noncomputable def leaf5810Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi271InputQChi innerPair340Input
    leaf5810InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5810LowerChecked :
    lowerCheck 24 leaf5810Box leaf5810Inputs = true := by
  rfl'

private theorem leaf5810CoversExact : CoversExact 8
    leaf5810Box leaf5810Certificate leaf5810InnerLog leaf5810Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi271RoundedFacts
    innerPair340RoundedFacts leaf5810RoundedFacts (by rfl)

private theorem leaf5810FlatSound : Sound leaf5810Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5810CertificateValid
    leaf5810InnerLogValid leaf5810CoversExact leaf5810LowerChecked

private noncomputable def leaf5811Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (61/128), chiHi := (31/64) }

private noncomputable def leaf5811Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435797/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712556544) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (700127165/536870912) }, upper := { exponent := 1, mantissa := (5427/4096) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi272LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137428953085/137425113088) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf5811InnerLog : WideLogData :=
  innerPair340Data

set_option maxRecDepth 1000000 in
private theorem leaf5811LocalValidity :
    LeafFacts leaf5811Box leaf5811Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5811Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712556544) }) = true
      norm_num [leaf5811Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5811CertificateValid :
    WideCertificateValid leaf5811Box leaf5811Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi272ValidityFacts
    leaf5811LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5811CoverageChecked :
    coverageCheck (innerAD leaf5811Box) leaf5811InnerLog = true := by
  rfl'

private theorem leaf5811InnerLogValid :
    leaf5811InnerLog.Valid 8 (innerAD leaf5811Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint92PositiveFacts.valid leaf5811CoverageChecked

private noncomputable def leaf5811InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814775/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5811InputLogOnePlusV_eq :
    leaf5811InputLogOnePlusV = outerEnclosure 24
      (leaf5811Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5811RoundedFacts : LeafRoundedFacts 8
    leaf5811Certificate.logOnePlusV leaf5811InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5811InputLogOnePlusV_eq }

private noncomputable def leaf5811Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi272InputQChi innerPair340Input
    leaf5811InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5811LowerChecked :
    lowerCheck 24 leaf5811Box leaf5811Inputs = true := by
  rfl'

private theorem leaf5811CoversExact : CoversExact 8
    leaf5811Box leaf5811Certificate leaf5811InnerLog leaf5811Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi272RoundedFacts
    innerPair340RoundedFacts leaf5811RoundedFacts (by rfl)

private theorem leaf5811FlatSound : Sound leaf5811Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5811CertificateValid
    leaf5811InnerLogValid leaf5811CoversExact leaf5811LowerChecked

private noncomputable def leaf5812Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (61/128), chiHi := (31/64) }

private noncomputable def leaf5812Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435799/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712493056) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (704124615/536870912) }, upper := { exponent := 1, mantissa := (2729/2048) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi272LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137428889597/137424986112) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf5812InnerLog : WideLogData :=
  innerPair340Data

set_option maxRecDepth 1000000 in
private theorem leaf5812LocalValidity :
    LeafFacts leaf5812Box leaf5812Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5812Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712493056) }) = true
      norm_num [leaf5812Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5812CertificateValid :
    WideCertificateValid leaf5812Box leaf5812Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi272ValidityFacts
    leaf5812LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5812CoverageChecked :
    coverageCheck (innerAD leaf5812Box) leaf5812InnerLog = true := by
  rfl'

private theorem leaf5812InnerLogValid :
    leaf5812InnerLog.Valid 8 (innerAD leaf5812Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint92PositiveFacts.valid leaf5812CoverageChecked

private noncomputable def leaf5812InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629557/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5812InputLogOnePlusV_eq :
    leaf5812InputLogOnePlusV = outerEnclosure 24
      (leaf5812Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5812RoundedFacts : LeafRoundedFacts 8
    leaf5812Certificate.logOnePlusV leaf5812InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5812InputLogOnePlusV_eq }

private noncomputable def leaf5812Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi272InputQChi innerPair340Input
    leaf5812InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5812LowerChecked :
    lowerCheck 24 leaf5812Box leaf5812Inputs = true := by
  rfl'

private theorem leaf5812CoversExact : CoversExact 8
    leaf5812Box leaf5812Certificate leaf5812InnerLog leaf5812Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi272RoundedFacts
    innerPair340RoundedFacts leaf5812RoundedFacts (by rfl)

private theorem leaf5812FlatSound : Sound leaf5812Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5812CertificateValid
    leaf5812InnerLogValid leaf5812CoversExact leaf5812LowerChecked

private noncomputable def leaf5813Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (15/32), chiHi := (61/128) }

private noncomputable def leaf5813Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435799/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712543232) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (700913547/536870912) }, upper := { exponent := 1, mantissa := (10867/8192) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi271LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137428939773/137425086464) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf5813InnerLog : WideLogData :=
  innerPair340Data

set_option maxRecDepth 1000000 in
private theorem leaf5813LocalValidity :
    LeafFacts leaf5813Box leaf5813Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5813Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712543232) }) = true
      norm_num [leaf5813Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5813CertificateValid :
    WideCertificateValid leaf5813Box leaf5813Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi271ValidityFacts
    leaf5813LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5813CoverageChecked :
    coverageCheck (innerAD leaf5813Box) leaf5813InnerLog = true := by
  rfl'

private theorem leaf5813InnerLogValid :
    leaf5813InnerLog.Valid 8 (innerAD leaf5813Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint92PositiveFacts.valid leaf5813CoverageChecked

private noncomputable def leaf5813InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629551/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5813InputLogOnePlusV_eq :
    leaf5813InputLogOnePlusV = outerEnclosure 24
      (leaf5813Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5813RoundedFacts : LeafRoundedFacts 8
    leaf5813Certificate.logOnePlusV leaf5813InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5813InputLogOnePlusV_eq }

private noncomputable def leaf5813Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi271InputQChi innerPair340Input
    leaf5813InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5813LowerChecked :
    lowerCheck 24 leaf5813Box leaf5813Inputs = true := by
  rfl'

private theorem leaf5813CoversExact : CoversExact 8
    leaf5813Box leaf5813Certificate leaf5813InnerLog leaf5813Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi271RoundedFacts
    innerPair340RoundedFacts leaf5813RoundedFacts (by rfl)

private theorem leaf5813FlatSound : Sound leaf5813Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5813CertificateValid
    leaf5813InnerLogValid leaf5813CoversExact leaf5813LowerChecked

private noncomputable def leaf5814Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (15/32), chiHi := (61/128) }

private noncomputable def leaf5814Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435801/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712480768) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (704845465/536870912) }, upper := { exponent := 1, mantissa := (683/512) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi271LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428877309/137424961536) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf5814InnerLog : WideLogData :=
  innerPair345Data

set_option maxRecDepth 1000000 in
private theorem leaf5814LocalValidity :
    LeafFacts leaf5814Box leaf5814Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5814Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712480768) }) = true
      norm_num [leaf5814Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5814CertificateValid :
    WideCertificateValid leaf5814Box leaf5814Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi271ValidityFacts
    leaf5814LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5814CoverageChecked :
    coverageCheck (innerAD leaf5814Box) leaf5814InnerLog = true := by
  rfl'

private theorem leaf5814InnerLogValid :
    leaf5814InnerLog.Valid 8 (innerAD leaf5814Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint92PositiveFacts.valid leaf5814CoverageChecked

private noncomputable def leaf5814InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629559/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5814InputLogOnePlusV_eq :
    leaf5814InputLogOnePlusV = outerEnclosure 24
      (leaf5814Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5814RoundedFacts : LeafRoundedFacts 8
    leaf5814Certificate.logOnePlusV leaf5814InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5814InputLogOnePlusV_eq }

private noncomputable def leaf5814Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi271InputQChi innerPair345Input
    leaf5814InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5814LowerChecked :
    lowerCheck 24 leaf5814Box leaf5814Inputs = true := by
  rfl'

private theorem leaf5814CoversExact : CoversExact 8
    leaf5814Box leaf5814Certificate leaf5814InnerLog leaf5814Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi271RoundedFacts
    innerPair345RoundedFacts leaf5814RoundedFacts (by rfl)

private theorem leaf5814FlatSound : Sound leaf5814Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5814CertificateValid
    leaf5814InnerLogValid leaf5814CoversExact leaf5814LowerChecked

private noncomputable def leaf5815Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (61/128), chiHi := (31/64) }

private noncomputable def leaf5815Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435801/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712429568) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (708122065/536870912) }, upper := { exponent := 1, mantissa := (5489/4096) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi272LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137428826109/137424859136) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf5815InnerLog : WideLogData :=
  innerPair345Data

set_option maxRecDepth 1000000 in
private theorem leaf5815LocalValidity :
    LeafFacts leaf5815Box leaf5815Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5815Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712429568) }) = true
      norm_num [leaf5815Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5815CertificateValid :
    WideCertificateValid leaf5815Box leaf5815Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi272ValidityFacts
    leaf5815LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5815CoverageChecked :
    coverageCheck (innerAD leaf5815Box) leaf5815InnerLog = true := by
  rfl'

private theorem leaf5815InnerLogValid :
    leaf5815InnerLog.Valid 8 (innerAD leaf5815Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint92PositiveFacts.valid leaf5815CoverageChecked

private noncomputable def leaf5815InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629565/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5815InputLogOnePlusV_eq :
    leaf5815InputLogOnePlusV = outerEnclosure 24
      (leaf5815Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5815RoundedFacts : LeafRoundedFacts 8
    leaf5815Certificate.logOnePlusV leaf5815InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5815InputLogOnePlusV_eq }

private noncomputable def leaf5815Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi272InputQChi innerPair345Input
    leaf5815InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5815LowerChecked :
    lowerCheck 24 leaf5815Box leaf5815Inputs = true := by
  rfl'

private theorem leaf5815CoversExact : CoversExact 8
    leaf5815Box leaf5815Certificate leaf5815InnerLog leaf5815Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi272RoundedFacts
    innerPair345RoundedFacts leaf5815RoundedFacts (by rfl)

private theorem leaf5815FlatSound : Sound leaf5815Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5815CertificateValid
    leaf5815InnerLogValid leaf5815CoversExact leaf5815LowerChecked

private noncomputable def leaf5816Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (61/128), chiHi := (31/64) }

private noncomputable def leaf5816Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435803/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712366080) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (712119515/536870912) }, upper := { exponent := 1, mantissa := (345/256) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi272LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428762621/137424732160) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf5816InnerLog : WideLogData :=
  innerPair346Data

set_option maxRecDepth 1000000 in
private theorem leaf5816LocalValidity :
    LeafFacts leaf5816Box leaf5816Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5816Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712366080) }) = true
      norm_num [leaf5816Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5816CertificateValid :
    WideCertificateValid leaf5816Box leaf5816Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi272ValidityFacts
    leaf5816LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5816CoverageChecked :
    coverageCheck (innerAD leaf5816Box) leaf5816InnerLog = true := by
  rfl'

private theorem leaf5816InnerLogValid :
    leaf5816InnerLog.Valid 8 (innerAD leaf5816Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint93PositiveFacts.valid leaf5816CoverageChecked

private noncomputable def leaf5816InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629573/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5816InputLogOnePlusV_eq :
    leaf5816InputLogOnePlusV = outerEnclosure 24
      (leaf5816Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5816RoundedFacts : LeafRoundedFacts 8
    leaf5816Certificate.logOnePlusV leaf5816InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5816InputLogOnePlusV_eq }

private noncomputable def leaf5816Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi272InputQChi innerPair346Input
    leaf5816InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5816LowerChecked :
    lowerCheck 24 leaf5816Box leaf5816Inputs = true := by
  rfl'

private theorem leaf5816CoversExact : CoversExact 8
    leaf5816Box leaf5816Certificate leaf5816InnerLog leaf5816Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi272RoundedFacts
    innerPair346RoundedFacts leaf5816RoundedFacts (by rfl)

private theorem leaf5816FlatSound : Sound leaf5816Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5816CertificateValid
    leaf5816InnerLogValid leaf5816CoversExact leaf5816LowerChecked

private noncomputable def leaf5817Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (31/64), chiHi := (63/128) }

private noncomputable def leaf5817Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435799/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712444928) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (707204619/536870912) }, upper := { exponent := 1, mantissa := (10963/8192) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi273LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137428841469/137424889856) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf5817InnerLog : WideLogData :=
  innerPair345Data

set_option maxRecDepth 1000000 in
private theorem leaf5817LocalValidity :
    LeafFacts leaf5817Box leaf5817Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5817Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712444928) }) = true
      norm_num [leaf5817Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5817CertificateValid :
    WideCertificateValid leaf5817Box leaf5817Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi273ValidityFacts
    leaf5817LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5817CoverageChecked :
    coverageCheck (innerAD leaf5817Box) leaf5817InnerLog = true := by
  rfl'

private theorem leaf5817InnerLogValid :
    leaf5817InnerLog.Valid 8 (innerAD leaf5817Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint92PositiveFacts.valid leaf5817CoverageChecked

private noncomputable def leaf5817InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629563/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5817InputLogOnePlusV_eq :
    leaf5817InputLogOnePlusV = outerEnclosure 24
      (leaf5817Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5817RoundedFacts : LeafRoundedFacts 8
    leaf5817Certificate.logOnePlusV leaf5817InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5817InputLogOnePlusV_eq }

private noncomputable def leaf5817Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi273InputQChi innerPair345Input
    leaf5817InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5817LowerChecked :
    lowerCheck 24 leaf5817Box leaf5817Inputs = true := by
  rfl'

private theorem leaf5817CoversExact : CoversExact 8
    leaf5817Box leaf5817Certificate leaf5817InnerLog leaf5817Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi273RoundedFacts
    innerPair345RoundedFacts leaf5817RoundedFacts (by rfl)

private theorem leaf5817FlatSound : Sound leaf5817Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5817CertificateValid
    leaf5817InnerLogValid leaf5817CoversExact leaf5817LowerChecked

private noncomputable def leaf5818Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (31/64), chiHi := (63/128) }

private noncomputable def leaf5818Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435801/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712380416) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (711267601/536870912) }, upper := { exponent := 1, mantissa := (5513/4096) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi273LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137428776957/137424760832) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf5818InnerLog : WideLogData :=
  innerPair346Data

set_option maxRecDepth 1000000 in
private theorem leaf5818LocalValidity :
    LeafFacts leaf5818Box leaf5818Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5818Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712380416) }) = true
      norm_num [leaf5818Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5818CertificateValid :
    WideCertificateValid leaf5818Box leaf5818Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi273ValidityFacts
    leaf5818LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5818CoverageChecked :
    coverageCheck (innerAD leaf5818Box) leaf5818InnerLog = true := by
  rfl'

private theorem leaf5818InnerLogValid :
    leaf5818InnerLog.Valid 8 (innerAD leaf5818Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint93PositiveFacts.valid leaf5818CoverageChecked

private noncomputable def leaf5818InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629571/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5818InputLogOnePlusV_eq :
    leaf5818InputLogOnePlusV = outerEnclosure 24
      (leaf5818Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5818RoundedFacts : LeafRoundedFacts 8
    leaf5818Certificate.logOnePlusV leaf5818InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5818InputLogOnePlusV_eq }

private noncomputable def leaf5818Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi273InputQChi innerPair346Input
    leaf5818InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5818LowerChecked :
    lowerCheck 24 leaf5818Box leaf5818Inputs = true := by
  rfl'

private theorem leaf5818CoversExact : CoversExact 8
    leaf5818Box leaf5818Certificate leaf5818InnerLog leaf5818Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi273RoundedFacts
    innerPair346RoundedFacts leaf5818RoundedFacts (by rfl)

private theorem leaf5818FlatSound : Sound leaf5818Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5818CertificateValid
    leaf5818InnerLogValid leaf5818CoversExact leaf5818LowerChecked

private noncomputable def leaf5819Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (63/128), chiHi := (1/2) }

private noncomputable def leaf5819Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435801/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712333312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (714282073/536870912) }, upper := { exponent := 1, mantissa := (173/128) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi274LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137428729853/137424666624) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf5819InnerLog : WideLogData :=
  innerPair346Data

set_option maxRecDepth 1000000 in
private theorem leaf5819LocalValidity :
    LeafFacts leaf5819Box leaf5819Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5819Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712333312) }) = true
      norm_num [leaf5819Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5819CertificateValid :
    WideCertificateValid leaf5819Box leaf5819Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi274ValidityFacts
    leaf5819LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5819CoverageChecked :
    coverageCheck (innerAD leaf5819Box) leaf5819InnerLog = true := by
  rfl'

private theorem leaf5819InnerLogValid :
    leaf5819InnerLog.Valid 8 (innerAD leaf5819Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint93PositiveFacts.valid leaf5819CoverageChecked

private noncomputable def leaf5819InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629577/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5819InputLogOnePlusV_eq :
    leaf5819InputLogOnePlusV = outerEnclosure 24
      (leaf5819Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5819RoundedFacts : LeafRoundedFacts 8
    leaf5819Certificate.logOnePlusV leaf5819InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5819InputLogOnePlusV_eq }

private noncomputable def leaf5819Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi274InputQChi innerPair346Input
    leaf5819InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5819LowerChecked :
    lowerCheck 24 leaf5819Box leaf5819Inputs = true := by
  rfl'

private theorem leaf5819CoversExact : CoversExact 8
    leaf5819Box leaf5819Certificate leaf5819InnerLog leaf5819Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi274RoundedFacts
    innerPair346RoundedFacts leaf5819RoundedFacts (by rfl)

private theorem leaf5819FlatSound : Sound leaf5819Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5819CertificateValid
    leaf5819InnerLogValid leaf5819CoversExact leaf5819LowerChecked

private noncomputable def leaf5820Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (63/128), chiHi := (1/2) }

private noncomputable def leaf5820Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435803/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712267776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (718410587/536870912) }, upper := { exponent := 1, mantissa := (87/64) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi274LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137428664317/137424535552) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf5820InnerLog : WideLogData :=
  innerPair346Data

set_option maxRecDepth 1000000 in
private theorem leaf5820LocalValidity :
    LeafFacts leaf5820Box leaf5820Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5820Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712267776) }) = true
      norm_num [leaf5820Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5820CertificateValid :
    WideCertificateValid leaf5820Box leaf5820Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi274ValidityFacts
    leaf5820LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5820CoverageChecked :
    coverageCheck (innerAD leaf5820Box) leaf5820InnerLog = true := by
  rfl'

private theorem leaf5820InnerLogValid :
    leaf5820InnerLog.Valid 8 (innerAD leaf5820Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint93PositiveFacts.valid leaf5820CoverageChecked

private noncomputable def leaf5820InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629585/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5820InputLogOnePlusV_eq :
    leaf5820InputLogOnePlusV = outerEnclosure 24
      (leaf5820Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5820RoundedFacts : LeafRoundedFacts 8
    leaf5820Certificate.logOnePlusV leaf5820InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5820InputLogOnePlusV_eq }

private noncomputable def leaf5820Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi274InputQChi innerPair346Input
    leaf5820InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5820LowerChecked :
    lowerCheck 24 leaf5820Box leaf5820Inputs = true := by
  rfl'

private theorem leaf5820CoversExact : CoversExact 8
    leaf5820Box leaf5820Certificate leaf5820InnerLog leaf5820Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi274RoundedFacts
    innerPair346RoundedFacts leaf5820RoundedFacts (by rfl)

private theorem leaf5820FlatSound : Sound leaf5820Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5820CertificateValid
    leaf5820InnerLogValid leaf5820CoversExact leaf5820LowerChecked

private noncomputable def leaf5821Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (31/64), chiHi := (63/128) }

private noncomputable def leaf5821Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435803/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712315904) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (715330583/536870912) }, upper := { exponent := 1, mantissa := (11089/8192) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi273LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137428712445/137424631808) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf5821InnerLog : WideLogData :=
  innerPair346Data

set_option maxRecDepth 1000000 in
private theorem leaf5821LocalValidity :
    LeafFacts leaf5821Box leaf5821Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5821Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712315904) }) = true
      norm_num [leaf5821Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5821CertificateValid :
    WideCertificateValid leaf5821Box leaf5821Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi273ValidityFacts
    leaf5821LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5821CoverageChecked :
    coverageCheck (innerAD leaf5821Box) leaf5821InnerLog = true := by
  rfl'

private theorem leaf5821InnerLogValid :
    leaf5821InnerLog.Valid 8 (innerAD leaf5821Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint93PositiveFacts.valid leaf5821CoverageChecked

private noncomputable def leaf5821InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629579/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5821InputLogOnePlusV_eq :
    leaf5821InputLogOnePlusV = outerEnclosure 24
      (leaf5821Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5821RoundedFacts : LeafRoundedFacts 8
    leaf5821Certificate.logOnePlusV leaf5821InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5821InputLogOnePlusV_eq }

private noncomputable def leaf5821Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi273InputQChi innerPair346Input
    leaf5821InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5821LowerChecked :
    lowerCheck 24 leaf5821Box leaf5821Inputs = true := by
  rfl'

private theorem leaf5821CoversExact : CoversExact 8
    leaf5821Box leaf5821Certificate leaf5821InnerLog leaf5821Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi273RoundedFacts
    innerPair346RoundedFacts leaf5821RoundedFacts (by rfl)

private theorem leaf5821FlatSound : Sound leaf5821Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5821CertificateValid
    leaf5821InnerLogValid leaf5821CoversExact leaf5821LowerChecked

private noncomputable def leaf5822Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (31/64), chiHi := (63/128) }

private noncomputable def leaf5822Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435805/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712251392) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (719393565/536870912) }, upper := { exponent := 1, mantissa := (697/512) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi273LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428647933/137424502784) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf5822InnerLog : WideLogData :=
  innerPair346Data

set_option maxRecDepth 1000000 in
private theorem leaf5822LocalValidity :
    LeafFacts leaf5822Box leaf5822Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5822Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712251392) }) = true
      norm_num [leaf5822Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5822CertificateValid :
    WideCertificateValid leaf5822Box leaf5822Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi273ValidityFacts
    leaf5822LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5822CoverageChecked :
    coverageCheck (innerAD leaf5822Box) leaf5822InnerLog = true := by
  rfl'

private theorem leaf5822InnerLogValid :
    leaf5822InnerLog.Valid 8 (innerAD leaf5822Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint93PositiveFacts.valid leaf5822CoverageChecked

private noncomputable def leaf5822InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629587/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5822InputLogOnePlusV_eq :
    leaf5822InputLogOnePlusV = outerEnclosure 24
      (leaf5822Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5822RoundedFacts : LeafRoundedFacts 8
    leaf5822Certificate.logOnePlusV leaf5822InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5822InputLogOnePlusV_eq }

private noncomputable def leaf5822Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi273InputQChi innerPair346Input
    leaf5822InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5822LowerChecked :
    lowerCheck 24 leaf5822Box leaf5822Inputs = true := by
  rfl'

private theorem leaf5822CoversExact : CoversExact 8
    leaf5822Box leaf5822Certificate leaf5822InnerLog leaf5822Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi273RoundedFacts
    innerPair346RoundedFacts leaf5822RoundedFacts (by rfl)

private theorem leaf5822FlatSound : Sound leaf5822Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5822CertificateValid
    leaf5822InnerLogValid leaf5822CoversExact leaf5822LowerChecked

private noncomputable def leaf5823Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (63/128), chiHi := (1/2) }

private noncomputable def leaf5823Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435805/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712202240) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (722539101/536870912) }, upper := { exponent := 1, mantissa := (175/128) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi274LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137428598781/137424404480) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf5823InnerLog : WideLogData :=
  innerPair352Data

set_option maxRecDepth 1000000 in
private theorem leaf5823LocalValidity :
    LeafFacts leaf5823Box leaf5823Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5823Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712202240) }) = true
      norm_num [leaf5823Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5823CertificateValid :
    WideCertificateValid leaf5823Box leaf5823Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi274ValidityFacts
    leaf5823LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5823CoverageChecked :
    coverageCheck (innerAD leaf5823Box) leaf5823InnerLog = true := by
  rfl'

private theorem leaf5823InnerLogValid :
    leaf5823InnerLog.Valid 8 (innerAD leaf5823Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint93PositiveFacts.valid leaf5823CoverageChecked

private noncomputable def leaf5823InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629593/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5823InputLogOnePlusV_eq :
    leaf5823InputLogOnePlusV = outerEnclosure 24
      (leaf5823Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5823RoundedFacts : LeafRoundedFacts 8
    leaf5823Certificate.logOnePlusV leaf5823InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5823InputLogOnePlusV_eq }

private noncomputable def leaf5823Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi274InputQChi innerPair352Input
    leaf5823InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5823LowerChecked :
    lowerCheck 24 leaf5823Box leaf5823Inputs = true := by
  rfl'

private theorem leaf5823CoversExact : CoversExact 8
    leaf5823Box leaf5823Certificate leaf5823InnerLog leaf5823Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi274RoundedFacts
    innerPair352RoundedFacts leaf5823RoundedFacts (by rfl)

private theorem leaf5823FlatSound : Sound leaf5823Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5823CertificateValid
    leaf5823InnerLogValid leaf5823CoversExact leaf5823LowerChecked

private noncomputable def leaf5824Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (63/128), chiHi := (1/2) }

private noncomputable def leaf5824Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435807/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712136704) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (726667615/536870912) }, upper := { exponent := 1, mantissa := (11/8) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi274LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428533245/137424273408) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf5824InnerLog : WideLogData :=
  innerPair352Data

set_option maxRecDepth 1000000 in
private theorem leaf5824LocalValidity :
    LeafFacts leaf5824Box leaf5824Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5824Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712136704) }) = true
      norm_num [leaf5824Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5824CertificateValid :
    WideCertificateValid leaf5824Box leaf5824Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi274ValidityFacts
    leaf5824LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5824CoverageChecked :
    coverageCheck (innerAD leaf5824Box) leaf5824InnerLog = true := by
  rfl'

private theorem leaf5824InnerLogValid :
    leaf5824InnerLog.Valid 8 (innerAD leaf5824Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint93PositiveFacts.valid leaf5824CoverageChecked

private noncomputable def leaf5824InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629601/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5824InputLogOnePlusV_eq :
    leaf5824InputLogOnePlusV = outerEnclosure 24
      (leaf5824Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5824RoundedFacts : LeafRoundedFacts 8
    leaf5824Certificate.logOnePlusV leaf5824InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5824InputLogOnePlusV_eq }

private noncomputable def leaf5824Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi274InputQChi innerPair352Input
    leaf5824InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5824LowerChecked :
    lowerCheck 24 leaf5824Box leaf5824Inputs = true := by
  rfl'

private theorem leaf5824CoversExact : CoversExact 8
    leaf5824Box leaf5824Certificate leaf5824InnerLog leaf5824Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi274RoundedFacts
    innerPair352RoundedFacts leaf5824RoundedFacts (by rfl)

private theorem leaf5824FlatSound : Sound leaf5824Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5824CertificateValid
    leaf5824InnerLogValid leaf5824CoversExact leaf5824LowerChecked

private noncomputable def component116Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (7/16), chiHi := (57/128) }

set_option maxRecDepth 1000000 in
private theorem component116Node0_sound : Sound component116Node0Box :=
  sound_of_literal_split component116Node0Box leaf5761Box leaf5762Box
    .k (105/32) (by rfl) (by rfl)
    leaf5761FlatSound leaf5762FlatSound

private noncomputable def component116Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (57/128), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component116Node1_sound : Sound component116Node1Box :=
  sound_of_literal_split component116Node1Box leaf5763Box leaf5764Box
    .k (105/32) (by rfl) (by rfl)
    leaf5763FlatSound leaf5764FlatSound

private noncomputable def component116Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (7/16), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component116Node2_sound : Sound component116Node2Box :=
  sound_of_literal_split component116Node2Box component116Node0Box component116Node1Box
    .chi (57/128) (by rfl) (by rfl)
    component116Node0_sound component116Node1_sound

private noncomputable def component116Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (7/16), chiHi := (57/128) }

set_option maxRecDepth 1000000 in
private theorem component116Node3_sound : Sound component116Node3Box :=
  sound_of_literal_split component116Node3Box leaf5765Box leaf5766Box
    .k (107/32) (by rfl) (by rfl)
    leaf5765FlatSound leaf5766FlatSound

private noncomputable def component116Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (57/128), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component116Node4_sound : Sound component116Node4Box :=
  sound_of_literal_split component116Node4Box leaf5767Box leaf5768Box
    .k (107/32) (by rfl) (by rfl)
    leaf5767FlatSound leaf5768FlatSound

private noncomputable def component116Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (7/16), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component116Node5_sound : Sound component116Node5Box :=
  sound_of_literal_split component116Node5Box component116Node3Box component116Node4Box
    .chi (57/128) (by rfl) (by rfl)
    component116Node3_sound component116Node4_sound

private noncomputable def component116Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (7/16), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component116Node6_sound : Sound component116Node6Box :=
  sound_of_literal_split component116Node6Box component116Node2Box component116Node5Box
    .k (53/16) (by rfl) (by rfl)
    component116Node2_sound component116Node5_sound

private noncomputable def component116Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (29/64), chiHi := (59/128) }

set_option maxRecDepth 1000000 in
private theorem component116Node7_sound : Sound component116Node7Box :=
  sound_of_literal_split component116Node7Box leaf5769Box leaf5770Box
    .k (105/32) (by rfl) (by rfl)
    leaf5769FlatSound leaf5770FlatSound

private noncomputable def component116Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (59/128), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component116Node8_sound : Sound component116Node8Box :=
  sound_of_literal_split component116Node8Box leaf5771Box leaf5772Box
    .k (105/32) (by rfl) (by rfl)
    leaf5771FlatSound leaf5772FlatSound

private noncomputable def component116Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (29/64), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component116Node9_sound : Sound component116Node9Box :=
  sound_of_literal_split component116Node9Box component116Node7Box component116Node8Box
    .chi (59/128) (by rfl) (by rfl)
    component116Node7_sound component116Node8_sound

private noncomputable def component116Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (29/64), chiHi := (59/128) }

set_option maxRecDepth 1000000 in
private theorem component116Node10_sound : Sound component116Node10Box :=
  sound_of_literal_split component116Node10Box leaf5773Box leaf5774Box
    .k (107/32) (by rfl) (by rfl)
    leaf5773FlatSound leaf5774FlatSound

private noncomputable def component116Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (59/128), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component116Node11_sound : Sound component116Node11Box :=
  sound_of_literal_split component116Node11Box leaf5775Box leaf5776Box
    .k (107/32) (by rfl) (by rfl)
    leaf5775FlatSound leaf5776FlatSound

private noncomputable def component116Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (29/64), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component116Node12_sound : Sound component116Node12Box :=
  sound_of_literal_split component116Node12Box component116Node10Box component116Node11Box
    .chi (59/128) (by rfl) (by rfl)
    component116Node10_sound component116Node11_sound

private noncomputable def component116Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (29/64), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component116Node13_sound : Sound component116Node13Box :=
  sound_of_literal_split component116Node13Box component116Node9Box component116Node12Box
    .k (53/16) (by rfl) (by rfl)
    component116Node9_sound component116Node12_sound

private noncomputable def component116Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (7/16), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component116Node14_sound : Sound component116Node14Box :=
  sound_of_literal_split component116Node14Box component116Node6Box component116Node13Box
    .chi (29/64) (by rfl) (by rfl)
    component116Node6_sound component116Node13_sound

private noncomputable def component116Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (7/16), chiHi := (57/128) }

set_option maxRecDepth 1000000 in
private theorem component116Node15_sound : Sound component116Node15Box :=
  sound_of_literal_split component116Node15Box leaf5777Box leaf5778Box
    .k (109/32) (by rfl) (by rfl)
    leaf5777FlatSound leaf5778FlatSound

private noncomputable def component116Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (57/128), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component116Node16_sound : Sound component116Node16Box :=
  sound_of_literal_split component116Node16Box leaf5779Box leaf5780Box
    .k (109/32) (by rfl) (by rfl)
    leaf5779FlatSound leaf5780FlatSound

private noncomputable def component116Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (7/16), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component116Node17_sound : Sound component116Node17Box :=
  sound_of_literal_split component116Node17Box component116Node15Box component116Node16Box
    .chi (57/128) (by rfl) (by rfl)
    component116Node15_sound component116Node16_sound

private noncomputable def component116Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (7/16), chiHi := (57/128) }

set_option maxRecDepth 1000000 in
private theorem component116Node18_sound : Sound component116Node18Box :=
  sound_of_literal_split component116Node18Box leaf5781Box leaf5782Box
    .k (111/32) (by rfl) (by rfl)
    leaf5781FlatSound leaf5782FlatSound

private noncomputable def component116Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (57/128), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component116Node19_sound : Sound component116Node19Box :=
  sound_of_literal_split component116Node19Box leaf5783Box leaf5784Box
    .k (111/32) (by rfl) (by rfl)
    leaf5783FlatSound leaf5784FlatSound

private noncomputable def component116Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (7/16), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component116Node20_sound : Sound component116Node20Box :=
  sound_of_literal_split component116Node20Box component116Node18Box component116Node19Box
    .chi (57/128) (by rfl) (by rfl)
    component116Node18_sound component116Node19_sound

private noncomputable def component116Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (7/16), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component116Node21_sound : Sound component116Node21Box :=
  sound_of_literal_split component116Node21Box component116Node17Box component116Node20Box
    .k (55/16) (by rfl) (by rfl)
    component116Node17_sound component116Node20_sound

private noncomputable def component116Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (29/64), chiHi := (59/128) }

set_option maxRecDepth 1000000 in
private theorem component116Node22_sound : Sound component116Node22Box :=
  sound_of_literal_split component116Node22Box leaf5785Box leaf5786Box
    .k (109/32) (by rfl) (by rfl)
    leaf5785FlatSound leaf5786FlatSound

private noncomputable def component116Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (59/128), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component116Node23_sound : Sound component116Node23Box :=
  sound_of_literal_split component116Node23Box leaf5787Box leaf5788Box
    .k (109/32) (by rfl) (by rfl)
    leaf5787FlatSound leaf5788FlatSound

private noncomputable def component116Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (29/64), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component116Node24_sound : Sound component116Node24Box :=
  sound_of_literal_split component116Node24Box component116Node22Box component116Node23Box
    .chi (59/128) (by rfl) (by rfl)
    component116Node22_sound component116Node23_sound

private noncomputable def component116Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (29/64), chiHi := (59/128) }

set_option maxRecDepth 1000000 in
private theorem component116Node25_sound : Sound component116Node25Box :=
  sound_of_literal_split component116Node25Box leaf5789Box leaf5790Box
    .k (111/32) (by rfl) (by rfl)
    leaf5789FlatSound leaf5790FlatSound

private noncomputable def component116Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (59/128), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component116Node26_sound : Sound component116Node26Box :=
  sound_of_literal_split component116Node26Box leaf5791Box leaf5792Box
    .k (111/32) (by rfl) (by rfl)
    leaf5791FlatSound leaf5792FlatSound

private noncomputable def component116Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (29/64), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component116Node27_sound : Sound component116Node27Box :=
  sound_of_literal_split component116Node27Box component116Node25Box component116Node26Box
    .chi (59/128) (by rfl) (by rfl)
    component116Node25_sound component116Node26_sound

private noncomputable def component116Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (29/64), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component116Node28_sound : Sound component116Node28Box :=
  sound_of_literal_split component116Node28Box component116Node24Box component116Node27Box
    .k (55/16) (by rfl) (by rfl)
    component116Node24_sound component116Node27_sound

private noncomputable def component116Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (7/16), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component116Node29_sound : Sound component116Node29Box :=
  sound_of_literal_split component116Node29Box component116Node21Box component116Node28Box
    .chi (29/64) (by rfl) (by rfl)
    component116Node21_sound component116Node28_sound

private noncomputable def component116Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (7/2), chiLo := (7/16), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component116Node30_sound : Sound component116Node30Box :=
  sound_of_literal_split component116Node30Box component116Node14Box component116Node29Box
    .k (27/8) (by rfl) (by rfl)
    component116Node14_sound component116Node29_sound

private noncomputable def component116Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (15/32), chiHi := (61/128) }

set_option maxRecDepth 1000000 in
private theorem component116Node31_sound : Sound component116Node31Box :=
  sound_of_literal_split component116Node31Box leaf5793Box leaf5794Box
    .k (105/32) (by rfl) (by rfl)
    leaf5793FlatSound leaf5794FlatSound

private noncomputable def component116Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (61/128), chiHi := (31/64) }

set_option maxRecDepth 1000000 in
private theorem component116Node32_sound : Sound component116Node32Box :=
  sound_of_literal_split component116Node32Box leaf5795Box leaf5796Box
    .k (105/32) (by rfl) (by rfl)
    leaf5795FlatSound leaf5796FlatSound

private noncomputable def component116Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (15/32), chiHi := (31/64) }

set_option maxRecDepth 1000000 in
private theorem component116Node33_sound : Sound component116Node33Box :=
  sound_of_literal_split component116Node33Box component116Node31Box component116Node32Box
    .chi (61/128) (by rfl) (by rfl)
    component116Node31_sound component116Node32_sound

private noncomputable def component116Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (15/32), chiHi := (61/128) }

set_option maxRecDepth 1000000 in
private theorem component116Node34_sound : Sound component116Node34Box :=
  sound_of_literal_split component116Node34Box leaf5797Box leaf5798Box
    .k (107/32) (by rfl) (by rfl)
    leaf5797FlatSound leaf5798FlatSound

private noncomputable def component116Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (61/128), chiHi := (31/64) }

set_option maxRecDepth 1000000 in
private theorem component116Node35_sound : Sound component116Node35Box :=
  sound_of_literal_split component116Node35Box leaf5799Box leaf5800Box
    .k (107/32) (by rfl) (by rfl)
    leaf5799FlatSound leaf5800FlatSound

private noncomputable def component116Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (15/32), chiHi := (31/64) }

set_option maxRecDepth 1000000 in
private theorem component116Node36_sound : Sound component116Node36Box :=
  sound_of_literal_split component116Node36Box component116Node34Box component116Node35Box
    .chi (61/128) (by rfl) (by rfl)
    component116Node34_sound component116Node35_sound

private noncomputable def component116Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (15/32), chiHi := (31/64) }

set_option maxRecDepth 1000000 in
private theorem component116Node37_sound : Sound component116Node37Box :=
  sound_of_literal_split component116Node37Box component116Node33Box component116Node36Box
    .k (53/16) (by rfl) (by rfl)
    component116Node33_sound component116Node36_sound

private noncomputable def component116Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (31/64), chiHi := (63/128) }

set_option maxRecDepth 1000000 in
private theorem component116Node38_sound : Sound component116Node38Box :=
  sound_of_literal_split component116Node38Box leaf5801Box leaf5802Box
    .k (105/32) (by rfl) (by rfl)
    leaf5801FlatSound leaf5802FlatSound

private noncomputable def component116Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (63/128), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component116Node39_sound : Sound component116Node39Box :=
  sound_of_literal_split component116Node39Box leaf5803Box leaf5804Box
    .k (105/32) (by rfl) (by rfl)
    leaf5803FlatSound leaf5804FlatSound

private noncomputable def component116Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (31/64), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component116Node40_sound : Sound component116Node40Box :=
  sound_of_literal_split component116Node40Box component116Node38Box component116Node39Box
    .chi (63/128) (by rfl) (by rfl)
    component116Node38_sound component116Node39_sound

private noncomputable def component116Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (31/64), chiHi := (63/128) }

set_option maxRecDepth 1000000 in
private theorem component116Node41_sound : Sound component116Node41Box :=
  sound_of_literal_split component116Node41Box leaf5805Box leaf5806Box
    .k (107/32) (by rfl) (by rfl)
    leaf5805FlatSound leaf5806FlatSound

private noncomputable def component116Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (63/128), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component116Node42_sound : Sound component116Node42Box :=
  sound_of_literal_split component116Node42Box leaf5807Box leaf5808Box
    .k (107/32) (by rfl) (by rfl)
    leaf5807FlatSound leaf5808FlatSound

private noncomputable def component116Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (31/64), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component116Node43_sound : Sound component116Node43Box :=
  sound_of_literal_split component116Node43Box component116Node41Box component116Node42Box
    .chi (63/128) (by rfl) (by rfl)
    component116Node41_sound component116Node42_sound

private noncomputable def component116Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (31/64), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component116Node44_sound : Sound component116Node44Box :=
  sound_of_literal_split component116Node44Box component116Node40Box component116Node43Box
    .k (53/16) (by rfl) (by rfl)
    component116Node40_sound component116Node43_sound

private noncomputable def component116Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (15/32), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component116Node45_sound : Sound component116Node45Box :=
  sound_of_literal_split component116Node45Box component116Node37Box component116Node44Box
    .chi (31/64) (by rfl) (by rfl)
    component116Node37_sound component116Node44_sound

private noncomputable def component116Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (15/32), chiHi := (61/128) }

set_option maxRecDepth 1000000 in
private theorem component116Node46_sound : Sound component116Node46Box :=
  sound_of_literal_split component116Node46Box leaf5809Box leaf5810Box
    .k (109/32) (by rfl) (by rfl)
    leaf5809FlatSound leaf5810FlatSound

private noncomputable def component116Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (61/128), chiHi := (31/64) }

set_option maxRecDepth 1000000 in
private theorem component116Node47_sound : Sound component116Node47Box :=
  sound_of_literal_split component116Node47Box leaf5811Box leaf5812Box
    .k (109/32) (by rfl) (by rfl)
    leaf5811FlatSound leaf5812FlatSound

private noncomputable def component116Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (15/32), chiHi := (31/64) }

set_option maxRecDepth 1000000 in
private theorem component116Node48_sound : Sound component116Node48Box :=
  sound_of_literal_split component116Node48Box component116Node46Box component116Node47Box
    .chi (61/128) (by rfl) (by rfl)
    component116Node46_sound component116Node47_sound

private noncomputable def component116Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (15/32), chiHi := (61/128) }

set_option maxRecDepth 1000000 in
private theorem component116Node49_sound : Sound component116Node49Box :=
  sound_of_literal_split component116Node49Box leaf5813Box leaf5814Box
    .k (111/32) (by rfl) (by rfl)
    leaf5813FlatSound leaf5814FlatSound

private noncomputable def component116Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (61/128), chiHi := (31/64) }

set_option maxRecDepth 1000000 in
private theorem component116Node50_sound : Sound component116Node50Box :=
  sound_of_literal_split component116Node50Box leaf5815Box leaf5816Box
    .k (111/32) (by rfl) (by rfl)
    leaf5815FlatSound leaf5816FlatSound

private noncomputable def component116Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (15/32), chiHi := (31/64) }

set_option maxRecDepth 1000000 in
private theorem component116Node51_sound : Sound component116Node51Box :=
  sound_of_literal_split component116Node51Box component116Node49Box component116Node50Box
    .chi (61/128) (by rfl) (by rfl)
    component116Node49_sound component116Node50_sound

private noncomputable def component116Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (15/32), chiHi := (31/64) }

set_option maxRecDepth 1000000 in
private theorem component116Node52_sound : Sound component116Node52Box :=
  sound_of_literal_split component116Node52Box component116Node48Box component116Node51Box
    .k (55/16) (by rfl) (by rfl)
    component116Node48_sound component116Node51_sound

private noncomputable def component116Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (31/64), chiHi := (63/128) }

set_option maxRecDepth 1000000 in
private theorem component116Node53_sound : Sound component116Node53Box :=
  sound_of_literal_split component116Node53Box leaf5817Box leaf5818Box
    .k (109/32) (by rfl) (by rfl)
    leaf5817FlatSound leaf5818FlatSound

private noncomputable def component116Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (63/128), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component116Node54_sound : Sound component116Node54Box :=
  sound_of_literal_split component116Node54Box leaf5819Box leaf5820Box
    .k (109/32) (by rfl) (by rfl)
    leaf5819FlatSound leaf5820FlatSound

private noncomputable def component116Node55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (31/64), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component116Node55_sound : Sound component116Node55Box :=
  sound_of_literal_split component116Node55Box component116Node53Box component116Node54Box
    .chi (63/128) (by rfl) (by rfl)
    component116Node53_sound component116Node54_sound

private noncomputable def component116Node56Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (31/64), chiHi := (63/128) }

set_option maxRecDepth 1000000 in
private theorem component116Node56_sound : Sound component116Node56Box :=
  sound_of_literal_split component116Node56Box leaf5821Box leaf5822Box
    .k (111/32) (by rfl) (by rfl)
    leaf5821FlatSound leaf5822FlatSound

private noncomputable def component116Node57Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (63/128), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component116Node57_sound : Sound component116Node57Box :=
  sound_of_literal_split component116Node57Box leaf5823Box leaf5824Box
    .k (111/32) (by rfl) (by rfl)
    leaf5823FlatSound leaf5824FlatSound

private noncomputable def component116Node58Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (31/64), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component116Node58_sound : Sound component116Node58Box :=
  sound_of_literal_split component116Node58Box component116Node56Box component116Node57Box
    .chi (63/128) (by rfl) (by rfl)
    component116Node56_sound component116Node57_sound

private noncomputable def component116Node59Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (31/64), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component116Node59_sound : Sound component116Node59Box :=
  sound_of_literal_split component116Node59Box component116Node55Box component116Node58Box
    .k (55/16) (by rfl) (by rfl)
    component116Node55_sound component116Node58_sound

private noncomputable def component116Node60Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (15/32), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component116Node60_sound : Sound component116Node60Box :=
  sound_of_literal_split component116Node60Box component116Node52Box component116Node59Box
    .chi (31/64) (by rfl) (by rfl)
    component116Node52_sound component116Node59_sound

private noncomputable def component116Node61Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (7/2), chiLo := (15/32), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component116Node61_sound : Sound component116Node61Box :=
  sound_of_literal_split component116Node61Box component116Node45Box component116Node60Box
    .k (27/8) (by rfl) (by rfl)
    component116Node45_sound component116Node60_sound

noncomputable def component116Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (7/2), chiLo := (7/16), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
theorem component116_sound : Sound component116Box :=
  sound_of_literal_split component116Box component116Node30Box component116Node61Box
    .chi (15/32) (by rfl) (by rfl)
    component116Node30_sound component116Node61_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
