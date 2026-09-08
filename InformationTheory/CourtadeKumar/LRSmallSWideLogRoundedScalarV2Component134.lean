import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch7
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch8
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch11
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch12
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

private noncomputable def leaf6618Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (1/2), chiHi := (65/128) }

private noncomputable def leaf6618Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435795/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712487936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (704583343/536870912) }, upper := { exponent := 1, mantissa := (10921/8192) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi329LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137428884477/137424975872) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf6618InnerLog : WideLogData :=
  innerPair340Data

set_option maxRecDepth 1000000 in
private theorem leaf6618LocalValidity :
    LeafFacts leaf6618Box leaf6618Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6618Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712487936) }) = true
      norm_num [leaf6618Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6618CertificateValid :
    WideCertificateValid leaf6618Box leaf6618Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi329ValidityFacts
    leaf6618LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6618CoverageChecked :
    coverageCheck (innerAD leaf6618Box) leaf6618InnerLog = true := by
  rfl'

private theorem leaf6618InnerLogValid :
    leaf6618InnerLog.Valid 8 (innerAD leaf6618Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint92PositiveFacts.valid leaf6618CoverageChecked

private noncomputable def leaf6618InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814779/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6618InputLogOnePlusV_eq :
    leaf6618InputLogOnePlusV = outerEnclosure 24
      (leaf6618Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6618RoundedFacts : LeafRoundedFacts 8
    leaf6618Certificate.logOnePlusV leaf6618InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6618InputLogOnePlusV_eq }

private noncomputable def leaf6618Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi329InputQChi innerPair340Input
    leaf6618InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6618LowerChecked :
    lowerCheck 24 leaf6618Box leaf6618Inputs = true := by
  rfl'

private theorem leaf6618CoversExact : CoversExact 8
    leaf6618Box leaf6618Certificate leaf6618InnerLog leaf6618Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi329RoundedFacts
    innerPair340RoundedFacts leaf6618RoundedFacts (by rfl)

private theorem leaf6618FlatSound : Sound leaf6618Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6618CertificateValid
    leaf6618InnerLogValid leaf6618CoversExact leaf6618LowerChecked

private noncomputable def leaf6619Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (1/2), chiHi := (65/128) }

private noncomputable def leaf6619Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435797/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712421376) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (708777389/536870912) }, upper := { exponent := 1, mantissa := (5493/4096) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi329LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137428817917/137424842752) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf6619InnerLog : WideLogData :=
  innerPair345Data

set_option maxRecDepth 1000000 in
private theorem leaf6619LocalValidity :
    LeafFacts leaf6619Box leaf6619Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6619Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712421376) }) = true
      norm_num [leaf6619Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6619CertificateValid :
    WideCertificateValid leaf6619Box leaf6619Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi329ValidityFacts
    leaf6619LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6619CoverageChecked :
    coverageCheck (innerAD leaf6619Box) leaf6619InnerLog = true := by
  rfl'

private theorem leaf6619InnerLogValid :
    leaf6619InnerLog.Valid 8 (innerAD leaf6619Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint92PositiveFacts.valid leaf6619CoverageChecked

private noncomputable def leaf6619InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814783/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6619InputLogOnePlusV_eq :
    leaf6619InputLogOnePlusV = outerEnclosure 24
      (leaf6619Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6619RoundedFacts : LeafRoundedFacts 8
    leaf6619Certificate.logOnePlusV leaf6619InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6619InputLogOnePlusV_eq }

private noncomputable def leaf6619Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi329InputQChi innerPair345Input
    leaf6619InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6619LowerChecked :
    lowerCheck 24 leaf6619Box leaf6619Inputs = true := by
  rfl'

private theorem leaf6619CoversExact : CoversExact 8
    leaf6619Box leaf6619Certificate leaf6619InnerLog leaf6619Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi329RoundedFacts
    innerPair345RoundedFacts leaf6619RoundedFacts (by rfl)

private theorem leaf6619FlatSound : Sound leaf6619Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6619CertificateValid
    leaf6619InnerLogValid leaf6619CoversExact leaf6619LowerChecked

private noncomputable def leaf6620Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (65/128), chiHi := (33/64) }

private noncomputable def leaf6620Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435797/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712380416) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (711398669/536870912) }, upper := { exponent := 1, mantissa := (5513/4096) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi330LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137428776957/137424760832) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf6620InnerLog : WideLogData :=
  innerPair346Data

set_option maxRecDepth 1000000 in
private theorem leaf6620LocalValidity :
    LeafFacts leaf6620Box leaf6620Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6620Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712380416) }) = true
      norm_num [leaf6620Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6620CertificateValid :
    WideCertificateValid leaf6620Box leaf6620Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi330ValidityFacts
    leaf6620LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6620CoverageChecked :
    coverageCheck (innerAD leaf6620Box) leaf6620InnerLog = true := by
  rfl'

private theorem leaf6620InnerLogValid :
    leaf6620InnerLog.Valid 8 (innerAD leaf6620Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint93PositiveFacts.valid leaf6620CoverageChecked

private noncomputable def leaf6620InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629571/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6620InputLogOnePlusV_eq :
    leaf6620InputLogOnePlusV = outerEnclosure 24
      (leaf6620Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6620RoundedFacts : LeafRoundedFacts 8
    leaf6620Certificate.logOnePlusV leaf6620InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6620InputLogOnePlusV_eq }

private noncomputable def leaf6620Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi330InputQChi innerPair346Input
    leaf6620InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6620LowerChecked :
    lowerCheck 24 leaf6620Box leaf6620Inputs = true := by
  rfl'

private theorem leaf6620CoversExact : CoversExact 8
    leaf6620Box leaf6620Certificate leaf6620InnerLog leaf6620Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi330RoundedFacts
    innerPair346RoundedFacts leaf6620RoundedFacts (by rfl)

private theorem leaf6620FlatSound : Sound leaf6620Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6620CertificateValid
    leaf6620InnerLogValid leaf6620CoversExact leaf6620LowerChecked

private noncomputable def leaf6621Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (65/128), chiHi := (33/64) }

private noncomputable def leaf6621Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435799/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712312832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (715658247/536870912) }, upper := { exponent := 1, mantissa := (2773/2048) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi330LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137428709373/137424625664) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf6621InnerLog : WideLogData :=
  innerPair346Data

set_option maxRecDepth 1000000 in
private theorem leaf6621LocalValidity :
    LeafFacts leaf6621Box leaf6621Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6621Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712312832) }) = true
      norm_num [leaf6621Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6621CertificateValid :
    WideCertificateValid leaf6621Box leaf6621Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi330ValidityFacts
    leaf6621LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6621CoverageChecked :
    coverageCheck (innerAD leaf6621Box) leaf6621InnerLog = true := by
  rfl'

private theorem leaf6621InnerLogValid :
    leaf6621InnerLog.Valid 8 (innerAD leaf6621Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint93PositiveFacts.valid leaf6621CoverageChecked

private noncomputable def leaf6621InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629579/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6621InputLogOnePlusV_eq :
    leaf6621InputLogOnePlusV = outerEnclosure 24
      (leaf6621Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6621RoundedFacts : LeafRoundedFacts 8
    leaf6621Certificate.logOnePlusV leaf6621InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6621InputLogOnePlusV_eq }

private noncomputable def leaf6621Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi330InputQChi innerPair346Input
    leaf6621InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6621LowerChecked :
    lowerCheck 24 leaf6621Box leaf6621Inputs = true := by
  rfl'

private theorem leaf6621CoversExact : CoversExact 8
    leaf6621Box leaf6621Certificate leaf6621InnerLog leaf6621Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi330RoundedFacts
    innerPair346RoundedFacts leaf6621RoundedFacts (by rfl)

private theorem leaf6621FlatSound : Sound leaf6621Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6621CertificateValid
    leaf6621InnerLogValid leaf6621CoversExact leaf6621LowerChecked

private noncomputable def leaf6622Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (1/2), chiHi := (65/128) }

private noncomputable def leaf6622Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435799/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712354816) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (712971435/536870912) }, upper := { exponent := 1, mantissa := (11051/8192) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi329LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137428751357/137424709632) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf6622InnerLog : WideLogData :=
  innerPair346Data

set_option maxRecDepth 1000000 in
private theorem leaf6622LocalValidity :
    LeafFacts leaf6622Box leaf6622Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6622Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712354816) }) = true
      norm_num [leaf6622Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6622CertificateValid :
    WideCertificateValid leaf6622Box leaf6622Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi329ValidityFacts
    leaf6622LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6622CoverageChecked :
    coverageCheck (innerAD leaf6622Box) leaf6622InnerLog = true := by
  rfl'

private theorem leaf6622InnerLogValid :
    leaf6622InnerLog.Valid 8 (innerAD leaf6622Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint93PositiveFacts.valid leaf6622CoverageChecked

private noncomputable def leaf6622InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814787/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6622InputLogOnePlusV_eq :
    leaf6622InputLogOnePlusV = outerEnclosure 24
      (leaf6622Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6622RoundedFacts : LeafRoundedFacts 8
    leaf6622Certificate.logOnePlusV leaf6622InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6622InputLogOnePlusV_eq }

private noncomputable def leaf6622Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi329InputQChi innerPair346Input
    leaf6622InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6622LowerChecked :
    lowerCheck 24 leaf6622Box leaf6622Inputs = true := by
  rfl'

private theorem leaf6622CoversExact : CoversExact 8
    leaf6622Box leaf6622Certificate leaf6622InnerLog leaf6622Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi329RoundedFacts
    innerPair346RoundedFacts leaf6622RoundedFacts (by rfl)

private theorem leaf6622FlatSound : Sound leaf6622Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6622CertificateValid
    leaf6622InnerLogValid leaf6622CoversExact leaf6622LowerChecked

private noncomputable def leaf6623Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (1/2), chiHi := (65/128) }

private noncomputable def leaf6623Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435801/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712288256) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (717165481/536870912) }, upper := { exponent := 1, mantissa := (2779/2048) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi329LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137428684797/137424576512) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf6623InnerLog : WideLogData :=
  innerPair346Data

set_option maxRecDepth 1000000 in
private theorem leaf6623LocalValidity :
    LeafFacts leaf6623Box leaf6623Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6623Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712288256) }) = true
      norm_num [leaf6623Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6623CertificateValid :
    WideCertificateValid leaf6623Box leaf6623Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi329ValidityFacts
    leaf6623LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6623CoverageChecked :
    coverageCheck (innerAD leaf6623Box) leaf6623InnerLog = true := by
  rfl'

private theorem leaf6623InnerLogValid :
    leaf6623InnerLog.Valid 8 (innerAD leaf6623Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint93PositiveFacts.valid leaf6623CoverageChecked

private noncomputable def leaf6623InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814791/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6623InputLogOnePlusV_eq :
    leaf6623InputLogOnePlusV = outerEnclosure 24
      (leaf6623Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6623RoundedFacts : LeafRoundedFacts 8
    leaf6623Certificate.logOnePlusV leaf6623InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6623InputLogOnePlusV_eq }

private noncomputable def leaf6623Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi329InputQChi innerPair346Input
    leaf6623InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6623LowerChecked :
    lowerCheck 24 leaf6623Box leaf6623Inputs = true := by
  rfl'

private theorem leaf6623CoversExact : CoversExact 8
    leaf6623Box leaf6623Certificate leaf6623InnerLog leaf6623Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi329RoundedFacts
    innerPair346RoundedFacts leaf6623RoundedFacts (by rfl)

private theorem leaf6623FlatSound : Sound leaf6623Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6623CertificateValid
    leaf6623InnerLogValid leaf6623CoversExact leaf6623LowerChecked

private noncomputable def leaf6624Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (65/128), chiHi := (33/64) }

private noncomputable def leaf6624Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435801/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712245248) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (719917825/536870912) }, upper := { exponent := 1, mantissa := (5579/4096) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi330LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137428641789/137424490496) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf6624InnerLog : WideLogData :=
  innerPair346Data

set_option maxRecDepth 1000000 in
private theorem leaf6624LocalValidity :
    LeafFacts leaf6624Box leaf6624Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6624Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712245248) }) = true
      norm_num [leaf6624Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6624CertificateValid :
    WideCertificateValid leaf6624Box leaf6624Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi330ValidityFacts
    leaf6624LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6624CoverageChecked :
    coverageCheck (innerAD leaf6624Box) leaf6624InnerLog = true := by
  rfl'

private theorem leaf6624InnerLogValid :
    leaf6624InnerLog.Valid 8 (innerAD leaf6624Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint93PositiveFacts.valid leaf6624CoverageChecked

private noncomputable def leaf6624InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907397/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6624InputLogOnePlusV_eq :
    leaf6624InputLogOnePlusV = outerEnclosure 24
      (leaf6624Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6624RoundedFacts : LeafRoundedFacts 8
    leaf6624Certificate.logOnePlusV leaf6624InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6624InputLogOnePlusV_eq }

private noncomputable def leaf6624Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi330InputQChi innerPair346Input
    leaf6624InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6624LowerChecked :
    lowerCheck 24 leaf6624Box leaf6624Inputs = true := by
  rfl'

private theorem leaf6624CoversExact : CoversExact 8
    leaf6624Box leaf6624Certificate leaf6624InnerLog leaf6624Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi330RoundedFacts
    innerPair346RoundedFacts leaf6624RoundedFacts (by rfl)

private theorem leaf6624FlatSound : Sound leaf6624Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6624CertificateValid
    leaf6624InnerLogValid leaf6624CoversExact leaf6624LowerChecked

private noncomputable def leaf6625Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (65/128), chiHi := (33/64) }

private noncomputable def leaf6625Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435803/268435456) }, vSqrt := { lower := (65529/65536), upper := (5285876657/5285552128) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (724177403/536870912) }, upper := { exponent := 1, mantissa := (1403/1024) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi330LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (10571428785/10571104256) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf6625InnerLog : WideLogData :=
  innerPair352Data

set_option maxRecDepth 1000000 in
private theorem leaf6625LocalValidity :
    LeafFacts leaf6625Box leaf6625Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6625Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (5285876657/5285552128) }) = true
      norm_num [leaf6625Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6625CertificateValid :
    WideCertificateValid leaf6625Box leaf6625Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi330ValidityFacts
    leaf6625LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6625CoverageChecked :
    coverageCheck (innerAD leaf6625Box) leaf6625InnerLog = true := by
  rfl'

private theorem leaf6625InnerLogValid :
    leaf6625InnerLog.Valid 8 (innerAD leaf6625Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint93PositiveFacts.valid leaf6625CoverageChecked

private noncomputable def leaf6625InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907399/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6625InputLogOnePlusV_eq :
    leaf6625InputLogOnePlusV = outerEnclosure 24
      (leaf6625Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6625RoundedFacts : LeafRoundedFacts 8
    leaf6625Certificate.logOnePlusV leaf6625InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6625InputLogOnePlusV_eq }

private noncomputable def leaf6625Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi330InputQChi innerPair352Input
    leaf6625InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6625LowerChecked :
    lowerCheck 24 leaf6625Box leaf6625Inputs = true := by
  rfl'

private theorem leaf6625CoversExact : CoversExact 8
    leaf6625Box leaf6625Certificate leaf6625InnerLog leaf6625Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi330RoundedFacts
    innerPair352RoundedFacts leaf6625RoundedFacts (by rfl)

private theorem leaf6625FlatSound : Sound leaf6625Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6625CertificateValid
    leaf6625InnerLogValid leaf6625CoversExact leaf6625LowerChecked

private noncomputable def leaf6626Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (33/64), chiHi := (67/128) }

private noncomputable def leaf6626Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435799/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712272896) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (718213995/536870912) }, upper := { exponent := 1, mantissa := (11131/8192) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi331LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137428669437/137424545792) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf6626InnerLog : WideLogData :=
  innerPair346Data

set_option maxRecDepth 1000000 in
private theorem leaf6626LocalValidity :
    LeafFacts leaf6626Box leaf6626Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6626Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712272896) }) = true
      norm_num [leaf6626Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6626CertificateValid :
    WideCertificateValid leaf6626Box leaf6626Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi331ValidityFacts
    leaf6626LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6626CoverageChecked :
    coverageCheck (innerAD leaf6626Box) leaf6626InnerLog = true := by
  rfl'

private theorem leaf6626InnerLogValid :
    leaf6626InnerLog.Valid 8 (innerAD leaf6626Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint93PositiveFacts.valid leaf6626CoverageChecked

private noncomputable def leaf6626InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (726849/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf6626InputLogOnePlusV_eq :
    leaf6626InputLogOnePlusV = outerEnclosure 24
      (leaf6626Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6626RoundedFacts : LeafRoundedFacts 8
    leaf6626Certificate.logOnePlusV leaf6626InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6626InputLogOnePlusV_eq }

private noncomputable def leaf6626Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi331InputQChi innerPair346Input
    leaf6626InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6626LowerChecked :
    lowerCheck 24 leaf6626Box leaf6626Inputs = true := by
  rfl'

private theorem leaf6626CoversExact : CoversExact 8
    leaf6626Box leaf6626Certificate leaf6626InnerLog leaf6626Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi331RoundedFacts
    innerPair346RoundedFacts leaf6626RoundedFacts (by rfl)

private theorem leaf6626FlatSound : Sound leaf6626Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6626CertificateValid
    leaf6626InnerLogValid leaf6626CoversExact leaf6626LowerChecked

private noncomputable def leaf6627Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (33/64), chiHi := (67/128) }

private noncomputable def leaf6627Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435801/268435456) }, vSqrt := { lower := (65529/65536), upper := (5285876657/5285554176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (722539105/536870912) }, upper := { exponent := 1, mantissa := (5599/4096) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi331LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (10571430833/10571108352) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf6627InnerLog : WideLogData :=
  innerPair352Data

set_option maxRecDepth 1000000 in
private theorem leaf6627LocalValidity :
    LeafFacts leaf6627Box leaf6627Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6627Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (5285876657/5285554176) }) = true
      norm_num [leaf6627Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6627CertificateValid :
    WideCertificateValid leaf6627Box leaf6627Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi331ValidityFacts
    leaf6627LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6627CoverageChecked :
    coverageCheck (innerAD leaf6627Box) leaf6627InnerLog = true := by
  rfl'

private theorem leaf6627InnerLogValid :
    leaf6627InnerLog.Valid 8 (innerAD leaf6627Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint93PositiveFacts.valid leaf6627CoverageChecked

private noncomputable def leaf6627InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629593/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6627InputLogOnePlusV_eq :
    leaf6627InputLogOnePlusV = outerEnclosure 24
      (leaf6627Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6627RoundedFacts : LeafRoundedFacts 8
    leaf6627Certificate.logOnePlusV leaf6627InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6627InputLogOnePlusV_eq }

private noncomputable def leaf6627Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi331InputQChi innerPair352Input
    leaf6627InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6627LowerChecked :
    lowerCheck 24 leaf6627Box leaf6627Inputs = true := by
  rfl'

private theorem leaf6627CoversExact : CoversExact 8
    leaf6627Box leaf6627Certificate leaf6627InnerLog leaf6627Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi331RoundedFacts
    innerPair352RoundedFacts leaf6627RoundedFacts (by rfl)

private theorem leaf6627FlatSound : Sound leaf6627Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6627CertificateValid
    leaf6627InnerLogValid leaf6627CoversExact leaf6627LowerChecked

private noncomputable def leaf6628Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (67/128), chiHi := (17/32) }

private noncomputable def leaf6628Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435801/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712165376) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (725029321/536870912) }, upper := { exponent := 1, mantissa := (2809/2048) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi332LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137428561917/137424330752) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf6628InnerLog : WideLogData :=
  innerPair352Data

set_option maxRecDepth 1000000 in
private theorem leaf6628LocalValidity :
    LeafFacts leaf6628Box leaf6628Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6628Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712165376) }) = true
      norm_num [leaf6628Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6628CertificateValid :
    WideCertificateValid leaf6628Box leaf6628Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi332ValidityFacts
    leaf6628LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6628CoverageChecked :
    coverageCheck (innerAD leaf6628Box) leaf6628InnerLog = true := by
  rfl'

private theorem leaf6628InnerLogValid :
    leaf6628InnerLog.Valid 8 (innerAD leaf6628Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint93PositiveFacts.valid leaf6628CoverageChecked

private noncomputable def leaf6628InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629597/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6628InputLogOnePlusV_eq :
    leaf6628InputLogOnePlusV = outerEnclosure 24
      (leaf6628Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6628RoundedFacts : LeafRoundedFacts 8
    leaf6628Certificate.logOnePlusV leaf6628InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6628InputLogOnePlusV_eq }

private noncomputable def leaf6628Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi332InputQChi innerPair352Input
    leaf6628InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6628LowerChecked :
    lowerCheck 24 leaf6628Box leaf6628Inputs = true := by
  rfl'

private theorem leaf6628CoversExact : CoversExact 8
    leaf6628Box leaf6628Certificate leaf6628InnerLog leaf6628Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi332RoundedFacts
    innerPair352RoundedFacts leaf6628RoundedFacts (by rfl)

private theorem leaf6628FlatSound : Sound leaf6628Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6628CertificateValid
    leaf6628InnerLogValid leaf6628CoversExact leaf6628LowerChecked

private noncomputable def leaf6629Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (67/128), chiHi := (17/32) }

private noncomputable def leaf6629Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435803/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712095744) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (729419963/536870912) }, upper := { exponent := 1, mantissa := (1413/1024) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi332LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137428492285/137424191488) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf6629InnerLog : WideLogData :=
  innerPair353Data

set_option maxRecDepth 1000000 in
private theorem leaf6629LocalValidity :
    LeafFacts leaf6629Box leaf6629Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6629Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712095744) }) = true
      norm_num [leaf6629Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6629CertificateValid :
    WideCertificateValid leaf6629Box leaf6629Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi332ValidityFacts
    leaf6629LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6629CoverageChecked :
    coverageCheck (innerAD leaf6629Box) leaf6629InnerLog = true := by
  rfl'

private theorem leaf6629InnerLogValid :
    leaf6629InnerLog.Valid 8 (innerAD leaf6629Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint96PositiveFacts.valid leaf6629CoverageChecked

private noncomputable def leaf6629InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814803/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6629InputLogOnePlusV_eq :
    leaf6629InputLogOnePlusV = outerEnclosure 24
      (leaf6629Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6629RoundedFacts : LeafRoundedFacts 8
    leaf6629Certificate.logOnePlusV leaf6629InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6629InputLogOnePlusV_eq }

private noncomputable def leaf6629Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi332InputQChi innerPair353Input
    leaf6629InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6629LowerChecked :
    lowerCheck 24 leaf6629Box leaf6629Inputs = true := by
  rfl'

private theorem leaf6629CoversExact : CoversExact 8
    leaf6629Box leaf6629Certificate leaf6629InnerLog leaf6629Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi332RoundedFacts
    innerPair353RoundedFacts leaf6629RoundedFacts (by rfl)

private theorem leaf6629FlatSound : Sound leaf6629Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6629CertificateValid
    leaf6629InnerLogValid leaf6629CoversExact leaf6629LowerChecked

private noncomputable def leaf6630Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (33/64), chiHi := (67/128) }

private noncomputable def leaf6630Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435803/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712135680) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (726864215/536870912) }, upper := { exponent := 1, mantissa := (11265/8192) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi331LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137428532221/137424271360) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf6630InnerLog : WideLogData :=
  innerPair353Data

set_option maxRecDepth 1000000 in
private theorem leaf6630LocalValidity :
    LeafFacts leaf6630Box leaf6630Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6630Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712135680) }) = true
      norm_num [leaf6630Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6630CertificateValid :
    WideCertificateValid leaf6630Box leaf6630Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi331ValidityFacts
    leaf6630LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6630CoverageChecked :
    coverageCheck (innerAD leaf6630Box) leaf6630InnerLog = true := by
  rfl'

private theorem leaf6630InnerLogValid :
    leaf6630InnerLog.Valid 8 (innerAD leaf6630Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint96PositiveFacts.valid leaf6630CoverageChecked

private noncomputable def leaf6630InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629601/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6630InputLogOnePlusV_eq :
    leaf6630InputLogOnePlusV = outerEnclosure 24
      (leaf6630Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6630RoundedFacts : LeafRoundedFacts 8
    leaf6630Certificate.logOnePlusV leaf6630InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6630InputLogOnePlusV_eq }

private noncomputable def leaf6630Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi331InputQChi innerPair353Input
    leaf6630InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6630LowerChecked :
    lowerCheck 24 leaf6630Box leaf6630Inputs = true := by
  rfl'

private theorem leaf6630CoversExact : CoversExact 8
    leaf6630Box leaf6630Certificate leaf6630InnerLog leaf6630Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi331RoundedFacts
    innerPair353RoundedFacts leaf6630RoundedFacts (by rfl)

private theorem leaf6630FlatSound : Sound leaf6630Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6630CertificateValid
    leaf6630InnerLogValid leaf6630CoversExact leaf6630LowerChecked

private noncomputable def leaf6631Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (33/64), chiHi := (67/128) }

private noncomputable def leaf6631Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435805/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712067072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (731189325/536870912) }, upper := { exponent := 1, mantissa := (2833/2048) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi331LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137428463613/137424134144) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf6631InnerLog : WideLogData :=
  innerPair353Data

set_option maxRecDepth 1000000 in
private theorem leaf6631LocalValidity :
    LeafFacts leaf6631Box leaf6631Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6631Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712067072) }) = true
      norm_num [leaf6631Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6631CertificateValid :
    WideCertificateValid leaf6631Box leaf6631Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi331ValidityFacts
    leaf6631LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6631CoverageChecked :
    coverageCheck (innerAD leaf6631Box) leaf6631InnerLog = true := by
  rfl'

private theorem leaf6631InnerLogValid :
    leaf6631InnerLog.Valid 8 (innerAD leaf6631Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint96PositiveFacts.valid leaf6631CoverageChecked

private noncomputable def leaf6631InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629609/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6631InputLogOnePlusV_eq :
    leaf6631InputLogOnePlusV = outerEnclosure 24
      (leaf6631Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6631RoundedFacts : LeafRoundedFacts 8
    leaf6631Certificate.logOnePlusV leaf6631InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6631InputLogOnePlusV_eq }

private noncomputable def leaf6631Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi331InputQChi innerPair353Input
    leaf6631InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6631LowerChecked :
    lowerCheck 24 leaf6631Box leaf6631Inputs = true := by
  rfl'

private theorem leaf6631CoversExact : CoversExact 8
    leaf6631Box leaf6631Certificate leaf6631InnerLog leaf6631Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi331RoundedFacts
    innerPair353RoundedFacts leaf6631RoundedFacts (by rfl)

private theorem leaf6631FlatSound : Sound leaf6631Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6631CertificateValid
    leaf6631InnerLogValid leaf6631CoversExact leaf6631LowerChecked

private noncomputable def leaf6632Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (67/128), chiHi := (17/32) }

private noncomputable def leaf6632Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435805/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712026112) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (733810605/536870912) }, upper := { exponent := 1, mantissa := (2843/2048) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi332LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137428422653/137424052224) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf6632InnerLog : WideLogData :=
  innerPair353Data

set_option maxRecDepth 1000000 in
private theorem leaf6632LocalValidity :
    LeafFacts leaf6632Box leaf6632Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6632Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712026112) }) = true
      norm_num [leaf6632Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6632CertificateValid :
    WideCertificateValid leaf6632Box leaf6632Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi332ValidityFacts
    leaf6632LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6632CoverageChecked :
    coverageCheck (innerAD leaf6632Box) leaf6632InnerLog = true := by
  rfl'

private theorem leaf6632InnerLogValid :
    leaf6632InnerLog.Valid 8 (innerAD leaf6632Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint96PositiveFacts.valid leaf6632CoverageChecked

private noncomputable def leaf6632InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814807/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6632InputLogOnePlusV_eq :
    leaf6632InputLogOnePlusV = outerEnclosure 24
      (leaf6632Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6632RoundedFacts : LeafRoundedFacts 8
    leaf6632Certificate.logOnePlusV leaf6632InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6632InputLogOnePlusV_eq }

private noncomputable def leaf6632Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi332InputQChi innerPair353Input
    leaf6632InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6632LowerChecked :
    lowerCheck 24 leaf6632Box leaf6632Inputs = true := by
  rfl'

private theorem leaf6632CoversExact : CoversExact 8
    leaf6632Box leaf6632Certificate leaf6632InnerLog leaf6632Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi332RoundedFacts
    innerPair353RoundedFacts leaf6632RoundedFacts (by rfl)

private theorem leaf6632FlatSound : Sound leaf6632Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6632CertificateValid
    leaf6632InnerLogValid leaf6632CoversExact leaf6632LowerChecked

private noncomputable def leaf6633Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (67/128), chiHi := (17/32) }

private noncomputable def leaf6633Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435807/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68711956480) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (738201247/536870912) }, upper := { exponent := 1, mantissa := (715/512) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi332LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137428353021/137423912960) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf6633InnerLog : WideLogData :=
  innerPair356Data

set_option maxRecDepth 1000000 in
private theorem leaf6633LocalValidity :
    LeafFacts leaf6633Box leaf6633Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6633Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68711956480) }) = true
      norm_num [leaf6633Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6633CertificateValid :
    WideCertificateValid leaf6633Box leaf6633Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi332ValidityFacts
    leaf6633LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6633CoverageChecked :
    coverageCheck (innerAD leaf6633Box) leaf6633InnerLog = true := by
  rfl'

private theorem leaf6633InnerLogValid :
    leaf6633InnerLog.Valid 8 (innerAD leaf6633Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint96PositiveFacts.valid leaf6633CoverageChecked

private noncomputable def leaf6633InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629623/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6633InputLogOnePlusV_eq :
    leaf6633InputLogOnePlusV = outerEnclosure 24
      (leaf6633Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6633RoundedFacts : LeafRoundedFacts 8
    leaf6633Certificate.logOnePlusV leaf6633InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6633InputLogOnePlusV_eq }

private noncomputable def leaf6633Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi332InputQChi innerPair356Input
    leaf6633InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6633LowerChecked :
    lowerCheck 24 leaf6633Box leaf6633Inputs = true := by
  rfl'

private theorem leaf6633CoversExact : CoversExact 8
    leaf6633Box leaf6633Certificate leaf6633InnerLog leaf6633Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi332RoundedFacts
    innerPair356RoundedFacts leaf6633RoundedFacts (by rfl)

private theorem leaf6633FlatSound : Sound leaf6633Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6633CertificateValid
    leaf6633InnerLogValid leaf6633CoversExact leaf6633LowerChecked

private noncomputable def leaf6634Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (17/32), chiHi := (69/128) }

private noncomputable def leaf6634Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217971/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34355993600) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (365905871/268435456) }, upper := { exponent := 1, mantissa := (5705/4096) } }, logOuter := sk131LogOuterCertificate, logK := sk131LogKCertificate, logChi := chi327LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68714224637/68711987200) } }, logDArg := sk131LogDArgCertificate }

private noncomputable def leaf6634InnerLog : WideLogData :=
  innerPair715Data

set_option maxRecDepth 1000000 in
private theorem leaf6634LocalValidity :
    LeafFacts leaf6634Box leaf6634Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6634Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34355993600) }) = true
      norm_num [leaf6634Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6634CertificateValid :
    WideCertificateValid leaf6634Box leaf6634Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk131ValidityFacts chi327ValidityFacts
    leaf6634LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6634CoverageChecked :
    coverageCheck (innerAD leaf6634Box) leaf6634InnerLog = true := by
  rfl'

private theorem leaf6634InnerLogValid :
    leaf6634InnerLog.Valid 8 (innerAD leaf6634Box) :=
  wideLogDataValid_of_cachedCheck endpoint457PositiveFacts
    endpoint518PositiveFacts.valid leaf6634CoverageChecked

private noncomputable def leaf6634InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629627/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6634InputLogOnePlusV_eq :
    leaf6634InputLogOnePlusV = outerEnclosure 24
      (leaf6634Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6634RoundedFacts : LeafRoundedFacts 8
    leaf6634Certificate.logOnePlusV leaf6634InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6634InputLogOnePlusV_eq }

private noncomputable def leaf6634Inputs : Inputs :=
  inputsOfCaches globalInput sk131RoundedInputs
    chi327InputQChi innerPair715Input
    leaf6634InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6634LowerChecked :
    lowerCheck 24 leaf6634Box leaf6634Inputs = true := by
  rfl'

private theorem leaf6634CoversExact : CoversExact 8
    leaf6634Box leaf6634Certificate leaf6634InnerLog leaf6634Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk131RoundedFacts chi327RoundedFacts
    innerPair715RoundedFacts leaf6634RoundedFacts (by rfl)

private theorem leaf6634FlatSound : Sound leaf6634Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6634CertificateValid
    leaf6634InnerLogValid leaf6634CoversExact leaf6634LowerChecked

private noncomputable def leaf6635Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (69/128), chiHi := (35/64) }

private noncomputable def leaf6635Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217973/134217728) }, vSqrt := { lower := (65529/65536), upper := (11452743679/11451979776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (369313533/268435456) }, upper := { exponent := 1, mantissa := (2879/2048) } }, logOuter := sk131LogOuterCertificate, logK := sk131LogKCertificate, logChi := chi328LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (22904723455/22903959552) } }, logDArg := sk131LogDArgCertificate }

private noncomputable def leaf6635InnerLog : WideLogData :=
  innerPair356Data

set_option maxRecDepth 1000000 in
private theorem leaf6635LocalValidity :
    LeafFacts leaf6635Box leaf6635Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6635Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (11452743679/11451979776) }) = true
      norm_num [leaf6635Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6635CertificateValid :
    WideCertificateValid leaf6635Box leaf6635Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk131ValidityFacts chi328ValidityFacts
    leaf6635LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6635CoverageChecked :
    coverageCheck (innerAD leaf6635Box) leaf6635InnerLog = true := by
  rfl'

private theorem leaf6635InnerLogValid :
    leaf6635InnerLog.Valid 8 (innerAD leaf6635Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint96PositiveFacts.valid leaf6635CoverageChecked

private noncomputable def leaf6635InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453705/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf6635InputLogOnePlusV_eq :
    leaf6635InputLogOnePlusV = outerEnclosure 24
      (leaf6635Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6635RoundedFacts : LeafRoundedFacts 8
    leaf6635Certificate.logOnePlusV leaf6635InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6635InputLogOnePlusV_eq }

private noncomputable def leaf6635Inputs : Inputs :=
  inputsOfCaches globalInput sk131RoundedInputs
    chi328InputQChi innerPair356Input
    leaf6635InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6635LowerChecked :
    lowerCheck 24 leaf6635Box leaf6635Inputs = true := by
  rfl'

private theorem leaf6635CoversExact : CoversExact 8
    leaf6635Box leaf6635Certificate leaf6635InnerLog leaf6635Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk131RoundedFacts chi328RoundedFacts
    innerPair356RoundedFacts leaf6635RoundedFacts (by rfl)

private theorem leaf6635FlatSound : Sound leaf6635Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6635CertificateValid
    leaf6635InnerLogValid leaf6635CoversExact leaf6635LowerChecked

private noncomputable def leaf6636Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (17/32), chiHi := (69/128) }

private noncomputable def leaf6636Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435807/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68711916544) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (740756995/536870912) }, upper := { exponent := 1, mantissa := (11479/8192) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi327LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137428313085/137423833088) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf6636InnerLog : WideLogData :=
  innerPair356Data

set_option maxRecDepth 1000000 in
private theorem leaf6636LocalValidity :
    LeafFacts leaf6636Box leaf6636Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6636Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68711916544) }) = true
      norm_num [leaf6636Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6636CertificateValid :
    WideCertificateValid leaf6636Box leaf6636Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi327ValidityFacts
    leaf6636LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6636CoverageChecked :
    coverageCheck (innerAD leaf6636Box) leaf6636InnerLog = true := by
  rfl'

private theorem leaf6636InnerLogValid :
    leaf6636InnerLog.Valid 8 (innerAD leaf6636Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint96PositiveFacts.valid leaf6636CoverageChecked

private noncomputable def leaf6636InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907407/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6636InputLogOnePlusV_eq :
    leaf6636InputLogOnePlusV = outerEnclosure 24
      (leaf6636Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6636RoundedFacts : LeafRoundedFacts 8
    leaf6636Certificate.logOnePlusV leaf6636InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6636InputLogOnePlusV_eq }

private noncomputable def leaf6636Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi327InputQChi innerPair356Input
    leaf6636InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6636LowerChecked :
    lowerCheck 24 leaf6636Box leaf6636Inputs = true := by
  rfl'

private theorem leaf6636CoversExact : CoversExact 8
    leaf6636Box leaf6636Certificate leaf6636InnerLog leaf6636Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi327RoundedFacts
    innerPair356RoundedFacts leaf6636RoundedFacts (by rfl)

private theorem leaf6636FlatSound : Sound leaf6636Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6636CertificateValid
    leaf6636InnerLogValid leaf6636CoversExact leaf6636LowerChecked

private noncomputable def leaf6637Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (17/32), chiHi := (69/128) }

private noncomputable def leaf6637Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435809/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68711845888) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (745213169/536870912) }, upper := { exponent := 1, mantissa := (2887/2048) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi327LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137428242429/137423691776) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf6637InnerLog : WideLogData :=
  innerPair357Data

set_option maxRecDepth 1000000 in
private theorem leaf6637LocalValidity :
    LeafFacts leaf6637Box leaf6637Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6637Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68711845888) }) = true
      norm_num [leaf6637Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6637CertificateValid :
    WideCertificateValid leaf6637Box leaf6637Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi327ValidityFacts
    leaf6637LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6637CoverageChecked :
    coverageCheck (innerAD leaf6637Box) leaf6637InnerLog = true := by
  rfl'

private theorem leaf6637InnerLogValid :
    leaf6637InnerLog.Valid 8 (innerAD leaf6637Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint97PositiveFacts.valid leaf6637CoverageChecked

private noncomputable def leaf6637InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907409/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6637InputLogOnePlusV_eq :
    leaf6637InputLogOnePlusV = outerEnclosure 24
      (leaf6637Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6637RoundedFacts : LeafRoundedFacts 8
    leaf6637Certificate.logOnePlusV leaf6637InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6637InputLogOnePlusV_eq }

private noncomputable def leaf6637Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi327InputQChi innerPair357Input
    leaf6637InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6637LowerChecked :
    lowerCheck 24 leaf6637Box leaf6637Inputs = true := by
  rfl'

private theorem leaf6637CoversExact : CoversExact 8
    leaf6637Box leaf6637Certificate leaf6637InnerLog leaf6637Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi327RoundedFacts
    innerPair357RoundedFacts leaf6637RoundedFacts (by rfl)

private theorem leaf6637FlatSound : Sound leaf6637Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6637CertificateValid
    leaf6637InnerLogValid leaf6637CoversExact leaf6637LowerChecked

private noncomputable def leaf6638Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (69/128), chiHi := (35/64) }

private noncomputable def leaf6638Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217975/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34355867648) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (373835239/268435456) }, upper := { exponent := 1, mantissa := (1457/1024) } }, logOuter := sk132LogOuterCertificate, logK := sk132LogKCertificate, logChi := chi328LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68714098685/68711735296) } }, logDArg := sk132LogDArgCertificate }

private noncomputable def leaf6638InnerLog : WideLogData :=
  innerPair826Data

set_option maxRecDepth 1000000 in
private theorem leaf6638LocalValidity :
    LeafFacts leaf6638Box leaf6638Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6638Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34355867648) }) = true
      norm_num [leaf6638Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6638CertificateValid :
    WideCertificateValid leaf6638Box leaf6638Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk132ValidityFacts chi328ValidityFacts
    leaf6638LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6638CoverageChecked :
    coverageCheck (innerAD leaf6638Box) leaf6638InnerLog = true := by
  rfl'

private theorem leaf6638InnerLogValid :
    leaf6638InnerLog.Valid 8 (innerAD leaf6638Box) :=
  wideLogDataValid_of_cachedCheck endpoint519PositiveFacts
    endpoint520PositiveFacts.valid leaf6638CoverageChecked

private noncomputable def leaf6638InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814829/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6638InputLogOnePlusV_eq :
    leaf6638InputLogOnePlusV = outerEnclosure 24
      (leaf6638Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6638RoundedFacts : LeafRoundedFacts 8
    leaf6638Certificate.logOnePlusV leaf6638InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6638InputLogOnePlusV_eq }

private noncomputable def leaf6638Inputs : Inputs :=
  inputsOfCaches globalInput sk132RoundedInputs
    chi328InputQChi innerPair826Input
    leaf6638InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6638LowerChecked :
    lowerCheck 24 leaf6638Box leaf6638Inputs = true := by
  rfl'

private theorem leaf6638CoversExact : CoversExact 8
    leaf6638Box leaf6638Certificate leaf6638InnerLog leaf6638Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk132RoundedFacts chi328RoundedFacts
    innerPair826RoundedFacts leaf6638RoundedFacts (by rfl)

private theorem leaf6638FlatSound : Sound leaf6638Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6638CertificateValid
    leaf6638InnerLogValid leaf6638CoversExact leaf6638LowerChecked

private noncomputable def leaf6639Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (35/64), chiHi := (71/128) }

private noncomputable def leaf6639Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217975/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34355885056) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (372721195/268435456) }, upper := { exponent := 1, mantissa := (5811/4096) } }, logOuter := sk131LogOuterCertificate, logK := sk131LogKCertificate, logChi := chi333LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68714116093/68711770112) } }, logDArg := sk131LogDArgCertificate }

private noncomputable def leaf6639InnerLog : WideLogData :=
  innerPair719Data

set_option maxRecDepth 1000000 in
private theorem leaf6639LocalValidity :
    LeafFacts leaf6639Box leaf6639Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6639Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34355885056) }) = true
      norm_num [leaf6639Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6639CertificateValid :
    WideCertificateValid leaf6639Box leaf6639Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk131ValidityFacts chi333ValidityFacts
    leaf6639LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6639CoverageChecked :
    coverageCheck (innerAD leaf6639Box) leaf6639InnerLog = true := by
  rfl'

private theorem leaf6639InnerLogValid :
    leaf6639InnerLog.Valid 8 (innerAD leaf6639Box) :=
  wideLogDataValid_of_cachedCheck endpoint460PositiveFacts
    endpoint469PositiveFacts.valid leaf6639CoverageChecked

private noncomputable def leaf6639InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814827/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6639InputLogOnePlusV_eq :
    leaf6639InputLogOnePlusV = outerEnclosure 24
      (leaf6639Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6639RoundedFacts : LeafRoundedFacts 8
    leaf6639Certificate.logOnePlusV leaf6639InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6639InputLogOnePlusV_eq }

private noncomputable def leaf6639Inputs : Inputs :=
  inputsOfCaches globalInput sk131RoundedInputs
    chi333InputQChi innerPair719Input
    leaf6639InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6639LowerChecked :
    lowerCheck 24 leaf6639Box leaf6639Inputs = true := by
  rfl'

private theorem leaf6639CoversExact : CoversExact 8
    leaf6639Box leaf6639Certificate leaf6639InnerLog leaf6639Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk131RoundedFacts chi333RoundedFacts
    innerPair719RoundedFacts leaf6639RoundedFacts (by rfl)

private theorem leaf6639FlatSound : Sound leaf6639Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6639CertificateValid
    leaf6639InnerLogValid leaf6639CoversExact leaf6639LowerChecked

private noncomputable def leaf6640Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (71/128), chiHi := (9/16) }

private noncomputable def leaf6640Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217977/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34355830784) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (376128857/268435456) }, upper := { exponent := 1, mantissa := (733/512) } }, logOuter := sk131LogOuterCertificate, logK := sk131LogKCertificate, logChi := chi334LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68714061821/68711661568) } }, logDArg := sk131LogDArgCertificate }

private noncomputable def leaf6640InnerLog : WideLogData :=
  innerPair357Data

set_option maxRecDepth 1000000 in
private theorem leaf6640LocalValidity :
    LeafFacts leaf6640Box leaf6640Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6640Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34355830784) }) = true
      norm_num [leaf6640Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6640CertificateValid :
    WideCertificateValid leaf6640Box leaf6640Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk131ValidityFacts chi334ValidityFacts
    leaf6640LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6640CoverageChecked :
    coverageCheck (innerAD leaf6640Box) leaf6640InnerLog = true := by
  rfl'

private theorem leaf6640InnerLogValid :
    leaf6640InnerLog.Valid 8 (innerAD leaf6640Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint97PositiveFacts.valid leaf6640CoverageChecked

private noncomputable def leaf6640InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629667/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6640InputLogOnePlusV_eq :
    leaf6640InputLogOnePlusV = outerEnclosure 24
      (leaf6640Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6640RoundedFacts : LeafRoundedFacts 8
    leaf6640Certificate.logOnePlusV leaf6640InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6640InputLogOnePlusV_eq }

private noncomputable def leaf6640Inputs : Inputs :=
  inputsOfCaches globalInput sk131RoundedInputs
    chi334InputQChi innerPair357Input
    leaf6640InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6640LowerChecked :
    lowerCheck 24 leaf6640Box leaf6640Inputs = true := by
  rfl'

private theorem leaf6640CoversExact : CoversExact 8
    leaf6640Box leaf6640Certificate leaf6640InnerLog leaf6640Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk131RoundedFacts chi334RoundedFacts
    innerPair357RoundedFacts leaf6640RoundedFacts (by rfl)

private theorem leaf6640FlatSound : Sound leaf6640Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6640CertificateValid
    leaf6640InnerLogValid leaf6640CoversExact leaf6640LowerChecked

private noncomputable def leaf6641Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (35/64), chiHi := (71/128) }

private noncomputable def leaf6641Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217977/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34355812352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (377308433/268435456) }, upper := { exponent := 1, mantissa := (2941/2048) } }, logOuter := sk132LogOuterCertificate, logK := sk132LogKCertificate, logChi := chi333LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68714043389/68711624704) } }, logDArg := sk132LogDArgCertificate }

private noncomputable def leaf6641InnerLog : WideLogData :=
  innerPair357Data

set_option maxRecDepth 1000000 in
private theorem leaf6641LocalValidity :
    LeafFacts leaf6641Box leaf6641Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6641Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34355812352) }) = true
      norm_num [leaf6641Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6641CertificateValid :
    WideCertificateValid leaf6641Box leaf6641Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk132ValidityFacts chi333ValidityFacts
    leaf6641LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6641CoverageChecked :
    coverageCheck (innerAD leaf6641Box) leaf6641InnerLog = true := by
  rfl'

private theorem leaf6641InnerLogValid :
    leaf6641InnerLog.Valid 8 (innerAD leaf6641Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint97PositiveFacts.valid leaf6641CoverageChecked

private noncomputable def leaf6641InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629671/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6641InputLogOnePlusV_eq :
    leaf6641InputLogOnePlusV = outerEnclosure 24
      (leaf6641Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6641RoundedFacts : LeafRoundedFacts 8
    leaf6641Certificate.logOnePlusV leaf6641InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6641InputLogOnePlusV_eq }

private noncomputable def leaf6641Inputs : Inputs :=
  inputsOfCaches globalInput sk132RoundedInputs
    chi333InputQChi innerPair357Input
    leaf6641InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6641LowerChecked :
    lowerCheck 24 leaf6641Box leaf6641Inputs = true := by
  rfl'

private theorem leaf6641CoversExact : CoversExact 8
    leaf6641Box leaf6641Certificate leaf6641InnerLog leaf6641Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk132RoundedFacts chi333RoundedFacts
    innerPair357RoundedFacts leaf6641RoundedFacts (by rfl)

private theorem leaf6641FlatSound : Sound leaf6641Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6641CertificateValid
    leaf6641InnerLogValid leaf6641CoversExact leaf6641LowerChecked

private noncomputable def leaf6642Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (71/128), chiHi := (9/16) }

private noncomputable def leaf6642Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217979/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34355757056) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (380781627/268435456) }, upper := { exponent := 1, mantissa := (371/256) } }, logOuter := sk132LogOuterCertificate, logK := sk132LogKCertificate, logChi := chi334LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68713988093/68711514112) } }, logDArg := sk132LogDArgCertificate }

private noncomputable def leaf6642InnerLog : WideLogData :=
  innerPair727Data

set_option maxRecDepth 1000000 in
private theorem leaf6642LocalValidity :
    LeafFacts leaf6642Box leaf6642Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6642Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34355757056) }) = true
      norm_num [leaf6642Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6642CertificateValid :
    WideCertificateValid leaf6642Box leaf6642Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk132ValidityFacts chi334ValidityFacts
    leaf6642LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6642CoverageChecked :
    coverageCheck (innerAD leaf6642Box) leaf6642InnerLog = true := by
  rfl'

private theorem leaf6642InnerLogValid :
    leaf6642InnerLog.Valid 8 (innerAD leaf6642Box) :=
  wideLogDataValid_of_cachedCheck endpoint464PositiveFacts
    endpoint471PositiveFacts.valid leaf6642CoverageChecked

private noncomputable def leaf6642InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629685/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6642InputLogOnePlusV_eq :
    leaf6642InputLogOnePlusV = outerEnclosure 24
      (leaf6642Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6642RoundedFacts : LeafRoundedFacts 8
    leaf6642Certificate.logOnePlusV leaf6642InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6642InputLogOnePlusV_eq }

private noncomputable def leaf6642Inputs : Inputs :=
  inputsOfCaches globalInput sk132RoundedInputs
    chi334InputQChi innerPair727Input
    leaf6642InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6642LowerChecked :
    lowerCheck 24 leaf6642Box leaf6642Inputs = true := by
  rfl'

private theorem leaf6642CoversExact : CoversExact 8
    leaf6642Box leaf6642Certificate leaf6642InnerLog leaf6642Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk132RoundedFacts chi334RoundedFacts
    innerPair727RoundedFacts leaf6642RoundedFacts (by rfl)

private theorem leaf6642FlatSound : Sound leaf6642Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6642CertificateValid
    leaf6642InnerLogValid leaf6642CoversExact leaf6642LowerChecked

private noncomputable def leaf6643Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (1/2), chiHi := (65/128) }

private noncomputable def leaf6643Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435803/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712221696) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (721359527/536870912) }, upper := { exponent := 1, mantissa := (11181/8192) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi329LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137428618237/137424443392) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf6643InnerLog : WideLogData :=
  innerPair346Data

set_option maxRecDepth 1000000 in
private theorem leaf6643LocalValidity :
    LeafFacts leaf6643Box leaf6643Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6643Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712221696) }) = true
      norm_num [leaf6643Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6643CertificateValid :
    WideCertificateValid leaf6643Box leaf6643Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi329ValidityFacts
    leaf6643LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6643CoverageChecked :
    coverageCheck (innerAD leaf6643Box) leaf6643InnerLog = true := by
  rfl'

private theorem leaf6643InnerLogValid :
    leaf6643InnerLog.Valid 8 (innerAD leaf6643Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint93PositiveFacts.valid leaf6643CoverageChecked

private noncomputable def leaf6643InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814795/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6643InputLogOnePlusV_eq :
    leaf6643InputLogOnePlusV = outerEnclosure 24
      (leaf6643Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6643RoundedFacts : LeafRoundedFacts 8
    leaf6643Certificate.logOnePlusV leaf6643InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6643InputLogOnePlusV_eq }

private noncomputable def leaf6643Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi329InputQChi innerPair346Input
    leaf6643InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6643LowerChecked :
    lowerCheck 24 leaf6643Box leaf6643Inputs = true := by
  rfl'

private theorem leaf6643CoversExact : CoversExact 8
    leaf6643Box leaf6643Certificate leaf6643InnerLog leaf6643Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi329RoundedFacts
    innerPair346RoundedFacts leaf6643RoundedFacts (by rfl)

private theorem leaf6643FlatSound : Sound leaf6643Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6643CertificateValid
    leaf6643InnerLogValid leaf6643CoversExact leaf6643LowerChecked

private noncomputable def leaf6644Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (1/2), chiHi := (65/128) }

private noncomputable def leaf6644Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435805/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712155136) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (725553573/536870912) }, upper := { exponent := 1, mantissa := (5623/4096) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi329LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137428551677/137424310272) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf6644InnerLog : WideLogData :=
  innerPair352Data

set_option maxRecDepth 1000000 in
private theorem leaf6644LocalValidity :
    LeafFacts leaf6644Box leaf6644Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6644Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712155136) }) = true
      norm_num [leaf6644Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6644CertificateValid :
    WideCertificateValid leaf6644Box leaf6644Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi329ValidityFacts
    leaf6644LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6644CoverageChecked :
    coverageCheck (innerAD leaf6644Box) leaf6644InnerLog = true := by
  rfl'

private theorem leaf6644InnerLogValid :
    leaf6644InnerLog.Valid 8 (innerAD leaf6644Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint93PositiveFacts.valid leaf6644CoverageChecked

private noncomputable def leaf6644InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629599/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6644InputLogOnePlusV_eq :
    leaf6644InputLogOnePlusV = outerEnclosure 24
      (leaf6644Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6644RoundedFacts : LeafRoundedFacts 8
    leaf6644Certificate.logOnePlusV leaf6644InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6644InputLogOnePlusV_eq }

private noncomputable def leaf6644Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi329InputQChi innerPair352Input
    leaf6644InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6644LowerChecked :
    lowerCheck 24 leaf6644Box leaf6644Inputs = true := by
  rfl'

private theorem leaf6644CoversExact : CoversExact 8
    leaf6644Box leaf6644Certificate leaf6644InnerLog leaf6644Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi329RoundedFacts
    innerPair352RoundedFacts leaf6644RoundedFacts (by rfl)

private theorem leaf6644FlatSound : Sound leaf6644Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6644CertificateValid
    leaf6644InnerLogValid leaf6644CoversExact leaf6644LowerChecked

private noncomputable def leaf6645Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (65/128), chiHi := (33/64) }

private noncomputable def leaf6645Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435805/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712110080) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (728436981/536870912) }, upper := { exponent := 1, mantissa := (5645/4096) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi330LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137428506621/137424220160) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf6645InnerLog : WideLogData :=
  innerPair353Data

set_option maxRecDepth 1000000 in
private theorem leaf6645LocalValidity :
    LeafFacts leaf6645Box leaf6645Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6645Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712110080) }) = true
      norm_num [leaf6645Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6645CertificateValid :
    WideCertificateValid leaf6645Box leaf6645Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi330ValidityFacts
    leaf6645LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6645CoverageChecked :
    coverageCheck (innerAD leaf6645Box) leaf6645InnerLog = true := by
  rfl'

private theorem leaf6645InnerLogValid :
    leaf6645InnerLog.Valid 8 (innerAD leaf6645Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint96PositiveFacts.valid leaf6645CoverageChecked

private noncomputable def leaf6645InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907401/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6645InputLogOnePlusV_eq :
    leaf6645InputLogOnePlusV = outerEnclosure 24
      (leaf6645Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6645RoundedFacts : LeafRoundedFacts 8
    leaf6645Certificate.logOnePlusV leaf6645InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6645InputLogOnePlusV_eq }

private noncomputable def leaf6645Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi330InputQChi innerPair353Input
    leaf6645InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6645LowerChecked :
    lowerCheck 24 leaf6645Box leaf6645Inputs = true := by
  rfl'

private theorem leaf6645CoversExact : CoversExact 8
    leaf6645Box leaf6645Certificate leaf6645InnerLog leaf6645Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi330RoundedFacts
    innerPair353RoundedFacts leaf6645RoundedFacts (by rfl)

private theorem leaf6645FlatSound : Sound leaf6645Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6645CertificateValid
    leaf6645InnerLogValid leaf6645CoversExact leaf6645LowerChecked

private noncomputable def leaf6646Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (65/128), chiHi := (33/64) }

private noncomputable def leaf6646Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435807/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712042496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (732696559/536870912) }, upper := { exponent := 1, mantissa := (2839/2048) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi330LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137428439037/137424084992) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf6646InnerLog : WideLogData :=
  innerPair353Data

set_option maxRecDepth 1000000 in
private theorem leaf6646LocalValidity :
    LeafFacts leaf6646Box leaf6646Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6646Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712042496) }) = true
      norm_num [leaf6646Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6646CertificateValid :
    WideCertificateValid leaf6646Box leaf6646Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi330ValidityFacts
    leaf6646LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6646CoverageChecked :
    coverageCheck (innerAD leaf6646Box) leaf6646InnerLog = true := by
  rfl'

private theorem leaf6646InnerLogValid :
    leaf6646InnerLog.Valid 8 (innerAD leaf6646Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint96PositiveFacts.valid leaf6646CoverageChecked

private noncomputable def leaf6646InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907403/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6646InputLogOnePlusV_eq :
    leaf6646InputLogOnePlusV = outerEnclosure 24
      (leaf6646Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6646RoundedFacts : LeafRoundedFacts 8
    leaf6646Certificate.logOnePlusV leaf6646InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6646InputLogOnePlusV_eq }

private noncomputable def leaf6646Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi330InputQChi innerPair353Input
    leaf6646InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6646LowerChecked :
    lowerCheck 24 leaf6646Box leaf6646Inputs = true := by
  rfl'

private theorem leaf6646CoversExact : CoversExact 8
    leaf6646Box leaf6646Certificate leaf6646InnerLog leaf6646Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi330RoundedFacts
    innerPair353RoundedFacts leaf6646RoundedFacts (by rfl)

private theorem leaf6646FlatSound : Sound leaf6646Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6646CertificateValid
    leaf6646InnerLogValid leaf6646CoversExact leaf6646LowerChecked

private noncomputable def leaf6647Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (1/2), chiHi := (65/128) }

private noncomputable def leaf6647Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435807/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712088576) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (729747619/536870912) }, upper := { exponent := 1, mantissa := (11311/8192) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi329LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137428485117/137424177152) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf6647InnerLog : WideLogData :=
  innerPair353Data

set_option maxRecDepth 1000000 in
private theorem leaf6647LocalValidity :
    LeafFacts leaf6647Box leaf6647Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6647Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712088576) }) = true
      norm_num [leaf6647Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6647CertificateValid :
    WideCertificateValid leaf6647Box leaf6647Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi329ValidityFacts
    leaf6647LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6647CoverageChecked :
    coverageCheck (innerAD leaf6647Box) leaf6647InnerLog = true := by
  rfl'

private theorem leaf6647InnerLogValid :
    leaf6647InnerLog.Valid 8 (innerAD leaf6647Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint96PositiveFacts.valid leaf6647CoverageChecked

private noncomputable def leaf6647InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629607/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6647InputLogOnePlusV_eq :
    leaf6647InputLogOnePlusV = outerEnclosure 24
      (leaf6647Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6647RoundedFacts : LeafRoundedFacts 8
    leaf6647Certificate.logOnePlusV leaf6647InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6647InputLogOnePlusV_eq }

private noncomputable def leaf6647Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi329InputQChi innerPair353Input
    leaf6647InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6647LowerChecked :
    lowerCheck 24 leaf6647Box leaf6647Inputs = true := by
  rfl'

private theorem leaf6647CoversExact : CoversExact 8
    leaf6647Box leaf6647Certificate leaf6647InnerLog leaf6647Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi329RoundedFacts
    innerPair353RoundedFacts leaf6647RoundedFacts (by rfl)

private theorem leaf6647FlatSound : Sound leaf6647Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6647CertificateValid
    leaf6647InnerLogValid leaf6647CoversExact leaf6647LowerChecked

private noncomputable def leaf6648Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (1/2), chiHi := (65/128) }

private noncomputable def leaf6648Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435809/268435456) }, vSqrt := { lower := (8191/8192), upper := (4042140973/4041883648) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (733941665/536870912) }, upper := { exponent := 1, mantissa := (711/512) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi329LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (8084024621/8083767296) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf6648InnerLog : WideLogData :=
  innerPair353Data

set_option maxRecDepth 1000000 in
private theorem leaf6648LocalValidity :
    LeafFacts leaf6648Box leaf6648Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6648Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4042140973/4041883648) }) = true
      norm_num [leaf6648Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6648CertificateValid :
    WideCertificateValid leaf6648Box leaf6648Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi329ValidityFacts
    leaf6648LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6648CoverageChecked :
    coverageCheck (innerAD leaf6648Box) leaf6648InnerLog = true := by
  rfl'

private theorem leaf6648InnerLogValid :
    leaf6648InnerLog.Valid 8 (innerAD leaf6648Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint96PositiveFacts.valid leaf6648CoverageChecked

private noncomputable def leaf6648InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629615/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6648InputLogOnePlusV_eq :
    leaf6648InputLogOnePlusV = outerEnclosure 24
      (leaf6648Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6648RoundedFacts : LeafRoundedFacts 8
    leaf6648Certificate.logOnePlusV leaf6648InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6648InputLogOnePlusV_eq }

private noncomputable def leaf6648Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi329InputQChi innerPair353Input
    leaf6648InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6648LowerChecked :
    lowerCheck 24 leaf6648Box leaf6648Inputs = true := by
  rfl'

private theorem leaf6648CoversExact : CoversExact 8
    leaf6648Box leaf6648Certificate leaf6648InnerLog leaf6648Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi329RoundedFacts
    innerPair353RoundedFacts leaf6648RoundedFacts (by rfl)

private theorem leaf6648FlatSound : Sound leaf6648Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6648CertificateValid
    leaf6648InnerLogValid leaf6648CoversExact leaf6648LowerChecked

private noncomputable def leaf6649Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (65/128), chiHi := (33/64) }

private noncomputable def leaf6649Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435809/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68711974912) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (736956137/536870912) }, upper := { exponent := 1, mantissa := (5711/4096) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi330LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137428371453/137423949824) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf6649InnerLog : WideLogData :=
  innerPair353Data

set_option maxRecDepth 1000000 in
private theorem leaf6649LocalValidity :
    LeafFacts leaf6649Box leaf6649Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6649Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68711974912) }) = true
      norm_num [leaf6649Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6649CertificateValid :
    WideCertificateValid leaf6649Box leaf6649Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi330ValidityFacts
    leaf6649LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6649CoverageChecked :
    coverageCheck (innerAD leaf6649Box) leaf6649InnerLog = true := by
  rfl'

private theorem leaf6649InnerLogValid :
    leaf6649InnerLog.Valid 8 (innerAD leaf6649Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint96PositiveFacts.valid leaf6649CoverageChecked

private noncomputable def leaf6649InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629621/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6649InputLogOnePlusV_eq :
    leaf6649InputLogOnePlusV = outerEnclosure 24
      (leaf6649Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6649RoundedFacts : LeafRoundedFacts 8
    leaf6649Certificate.logOnePlusV leaf6649InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6649InputLogOnePlusV_eq }

private noncomputable def leaf6649Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi330InputQChi innerPair353Input
    leaf6649InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6649LowerChecked :
    lowerCheck 24 leaf6649Box leaf6649Inputs = true := by
  rfl'

private theorem leaf6649CoversExact : CoversExact 8
    leaf6649Box leaf6649Certificate leaf6649InnerLog leaf6649Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi330RoundedFacts
    innerPair353RoundedFacts leaf6649RoundedFacts (by rfl)

private theorem leaf6649FlatSound : Sound leaf6649Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6649CertificateValid
    leaf6649InnerLogValid leaf6649CoversExact leaf6649LowerChecked

private noncomputable def leaf6650Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (65/128), chiHi := (33/64) }

private noncomputable def leaf6650Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435811/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711907328) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (741215715/536870912) }, upper := { exponent := 1, mantissa := (359/256) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi330LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428303869/137423814656) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf6650InnerLog : WideLogData :=
  innerPair356Data

set_option maxRecDepth 1000000 in
private theorem leaf6650LocalValidity :
    LeafFacts leaf6650Box leaf6650Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6650Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711907328) }) = true
      norm_num [leaf6650Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6650CertificateValid :
    WideCertificateValid leaf6650Box leaf6650Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi330ValidityFacts
    leaf6650LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6650CoverageChecked :
    coverageCheck (innerAD leaf6650Box) leaf6650InnerLog = true := by
  rfl'

private theorem leaf6650InnerLogValid :
    leaf6650InnerLog.Valid 8 (innerAD leaf6650Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint96PositiveFacts.valid leaf6650CoverageChecked

private noncomputable def leaf6650InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629629/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6650InputLogOnePlusV_eq :
    leaf6650InputLogOnePlusV = outerEnclosure 24
      (leaf6650Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6650RoundedFacts : LeafRoundedFacts 8
    leaf6650Certificate.logOnePlusV leaf6650InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6650InputLogOnePlusV_eq }

private noncomputable def leaf6650Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi330InputQChi innerPair356Input
    leaf6650InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6650LowerChecked :
    lowerCheck 24 leaf6650Box leaf6650Inputs = true := by
  rfl'

private theorem leaf6650CoversExact : CoversExact 8
    leaf6650Box leaf6650Certificate leaf6650InnerLog leaf6650Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi330RoundedFacts
    innerPair356RoundedFacts leaf6650RoundedFacts (by rfl)

private theorem leaf6650FlatSound : Sound leaf6650Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6650CertificateValid
    leaf6650InnerLogValid leaf6650CoversExact leaf6650LowerChecked

private noncomputable def leaf6651Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (33/64), chiHi := (67/128) }

private noncomputable def leaf6651Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435807/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68711998464) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (735514435/536870912) }, upper := { exponent := 1, mantissa := (11399/8192) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi331LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137428395005/137423996928) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf6651InnerLog : WideLogData :=
  innerPair353Data

set_option maxRecDepth 1000000 in
private theorem leaf6651LocalValidity :
    LeafFacts leaf6651Box leaf6651Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6651Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68711998464) }) = true
      norm_num [leaf6651Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6651CertificateValid :
    WideCertificateValid leaf6651Box leaf6651Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi331ValidityFacts
    leaf6651LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6651CoverageChecked :
    coverageCheck (innerAD leaf6651Box) leaf6651InnerLog = true := by
  rfl'

private theorem leaf6651InnerLogValid :
    leaf6651InnerLog.Valid 8 (innerAD leaf6651Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint96PositiveFacts.valid leaf6651CoverageChecked

private noncomputable def leaf6651InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814809/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6651InputLogOnePlusV_eq :
    leaf6651InputLogOnePlusV = outerEnclosure 24
      (leaf6651Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6651RoundedFacts : LeafRoundedFacts 8
    leaf6651Certificate.logOnePlusV leaf6651InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6651InputLogOnePlusV_eq }

private noncomputable def leaf6651Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi331InputQChi innerPair353Input
    leaf6651InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6651LowerChecked :
    lowerCheck 24 leaf6651Box leaf6651Inputs = true := by
  rfl'

private theorem leaf6651CoversExact : CoversExact 8
    leaf6651Box leaf6651Certificate leaf6651InnerLog leaf6651Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi331RoundedFacts
    innerPair353RoundedFacts leaf6651RoundedFacts (by rfl)

private theorem leaf6651FlatSound : Sound leaf6651Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6651CertificateValid
    leaf6651InnerLogValid leaf6651CoversExact leaf6651LowerChecked

private noncomputable def leaf6652Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (33/64), chiHi := (67/128) }

private noncomputable def leaf6652Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435809/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68711929856) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (739839545/536870912) }, upper := { exponent := 1, mantissa := (5733/4096) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi331LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137428326397/137423859712) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf6652InnerLog : WideLogData :=
  innerPair356Data

set_option maxRecDepth 1000000 in
private theorem leaf6652LocalValidity :
    LeafFacts leaf6652Box leaf6652Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6652Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68711929856) }) = true
      norm_num [leaf6652Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6652CertificateValid :
    WideCertificateValid leaf6652Box leaf6652Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi331ValidityFacts
    leaf6652LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6652CoverageChecked :
    coverageCheck (innerAD leaf6652Box) leaf6652InnerLog = true := by
  rfl'

private theorem leaf6652InnerLogValid :
    leaf6652InnerLog.Valid 8 (innerAD leaf6652Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint96PositiveFacts.valid leaf6652CoverageChecked

private noncomputable def leaf6652InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814813/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6652InputLogOnePlusV_eq :
    leaf6652InputLogOnePlusV = outerEnclosure 24
      (leaf6652Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6652RoundedFacts : LeafRoundedFacts 8
    leaf6652Certificate.logOnePlusV leaf6652InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6652InputLogOnePlusV_eq }

private noncomputable def leaf6652Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi331InputQChi innerPair356Input
    leaf6652InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6652LowerChecked :
    lowerCheck 24 leaf6652Box leaf6652Inputs = true := by
  rfl'

private theorem leaf6652CoversExact : CoversExact 8
    leaf6652Box leaf6652Certificate leaf6652InnerLog leaf6652Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi331RoundedFacts
    innerPair356RoundedFacts leaf6652RoundedFacts (by rfl)

private theorem leaf6652FlatSound : Sound leaf6652Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6652CertificateValid
    leaf6652InnerLogValid leaf6652CoversExact leaf6652LowerChecked

private noncomputable def leaf6653Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (67/128), chiHi := (17/32) }

private noncomputable def leaf6653Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435809/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68711886848) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (742591889/536870912) }, upper := { exponent := 1, mantissa := (2877/2048) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi332LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137428283389/137423773696) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf6653InnerLog : WideLogData :=
  innerPair356Data

set_option maxRecDepth 1000000 in
private theorem leaf6653LocalValidity :
    LeafFacts leaf6653Box leaf6653Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6653Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68711886848) }) = true
      norm_num [leaf6653Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6653CertificateValid :
    WideCertificateValid leaf6653Box leaf6653Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi332ValidityFacts
    leaf6653LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6653CoverageChecked :
    coverageCheck (innerAD leaf6653Box) leaf6653InnerLog = true := by
  rfl'

private theorem leaf6653InnerLogValid :
    leaf6653InnerLog.Valid 8 (innerAD leaf6653Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint96PositiveFacts.valid leaf6653CoverageChecked

private noncomputable def leaf6653InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629631/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6653InputLogOnePlusV_eq :
    leaf6653InputLogOnePlusV = outerEnclosure 24
      (leaf6653Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6653RoundedFacts : LeafRoundedFacts 8
    leaf6653Certificate.logOnePlusV leaf6653InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6653InputLogOnePlusV_eq }

private noncomputable def leaf6653Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi332InputQChi innerPair356Input
    leaf6653InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6653LowerChecked :
    lowerCheck 24 leaf6653Box leaf6653Inputs = true := by
  rfl'

private theorem leaf6653CoversExact : CoversExact 8
    leaf6653Box leaf6653Certificate leaf6653InnerLog leaf6653Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi332RoundedFacts
    innerPair356RoundedFacts leaf6653RoundedFacts (by rfl)

private theorem leaf6653FlatSound : Sound leaf6653Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6653CertificateValid
    leaf6653InnerLogValid leaf6653CoversExact leaf6653LowerChecked

private noncomputable def leaf6654Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (67/128), chiHi := (17/32) }

private noncomputable def leaf6654Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435811/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68711817216) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (746982531/536870912) }, upper := { exponent := 1, mantissa := (1447/1024) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi332LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137428213757/137423634432) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf6654InnerLog : WideLogData :=
  innerPair357Data

set_option maxRecDepth 1000000 in
private theorem leaf6654LocalValidity :
    LeafFacts leaf6654Box leaf6654Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6654Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68711817216) }) = true
      norm_num [leaf6654Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6654CertificateValid :
    WideCertificateValid leaf6654Box leaf6654Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi332ValidityFacts
    leaf6654LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6654CoverageChecked :
    coverageCheck (innerAD leaf6654Box) leaf6654InnerLog = true := by
  rfl'

private theorem leaf6654InnerLogValid :
    leaf6654InnerLog.Valid 8 (innerAD leaf6654Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint97PositiveFacts.valid leaf6654CoverageChecked

private noncomputable def leaf6654InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453705/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf6654InputLogOnePlusV_eq :
    leaf6654InputLogOnePlusV = outerEnclosure 24
      (leaf6654Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6654RoundedFacts : LeafRoundedFacts 8
    leaf6654Certificate.logOnePlusV leaf6654InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6654InputLogOnePlusV_eq }

private noncomputable def leaf6654Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi332InputQChi innerPair357Input
    leaf6654InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6654LowerChecked :
    lowerCheck 24 leaf6654Box leaf6654Inputs = true := by
  rfl'

private theorem leaf6654CoversExact : CoversExact 8
    leaf6654Box leaf6654Certificate leaf6654InnerLog leaf6654Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi332RoundedFacts
    innerPair357RoundedFacts leaf6654RoundedFacts (by rfl)

private theorem leaf6654FlatSound : Sound leaf6654Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6654CertificateValid
    leaf6654InnerLogValid leaf6654CoversExact leaf6654LowerChecked

private noncomputable def leaf6655Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (33/64), chiHi := (67/128) }

private noncomputable def leaf6655Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435811/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68711861248) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (744164655/536870912) }, upper := { exponent := 1, mantissa := (11533/8192) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi331LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137428257789/137423722496) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf6655InnerLog : WideLogData :=
  innerPair357Data

set_option maxRecDepth 1000000 in
private theorem leaf6655LocalValidity :
    LeafFacts leaf6655Box leaf6655Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6655Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68711861248) }) = true
      norm_num [leaf6655Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6655CertificateValid :
    WideCertificateValid leaf6655Box leaf6655Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi331ValidityFacts
    leaf6655LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6655CoverageChecked :
    coverageCheck (innerAD leaf6655Box) leaf6655InnerLog = true := by
  rfl'

private theorem leaf6655InnerLogValid :
    leaf6655InnerLog.Valid 8 (innerAD leaf6655Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint97PositiveFacts.valid leaf6655CoverageChecked

private noncomputable def leaf6655InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814817/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6655InputLogOnePlusV_eq :
    leaf6655InputLogOnePlusV = outerEnclosure 24
      (leaf6655Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6655RoundedFacts : LeafRoundedFacts 8
    leaf6655Certificate.logOnePlusV leaf6655InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6655InputLogOnePlusV_eq }

private noncomputable def leaf6655Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi331InputQChi innerPair357Input
    leaf6655InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6655LowerChecked :
    lowerCheck 24 leaf6655Box leaf6655Inputs = true := by
  rfl'

private theorem leaf6655CoversExact : CoversExact 8
    leaf6655Box leaf6655Certificate leaf6655InnerLog leaf6655Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi331RoundedFacts
    innerPair357RoundedFacts leaf6655RoundedFacts (by rfl)

private theorem leaf6655FlatSound : Sound leaf6655Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6655CertificateValid
    leaf6655InnerLogValid leaf6655CoversExact leaf6655LowerChecked

private noncomputable def leaf6656Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (33/64), chiHi := (67/128) }

private noncomputable def leaf6656Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435813/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711792640) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (748489765/536870912) }, upper := { exponent := 1, mantissa := (725/512) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi331LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428189181/137423585280) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf6656InnerLog : WideLogData :=
  innerPair357Data

set_option maxRecDepth 1000000 in
private theorem leaf6656LocalValidity :
    LeafFacts leaf6656Box leaf6656Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6656Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711792640) }) = true
      norm_num [leaf6656Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6656CertificateValid :
    WideCertificateValid leaf6656Box leaf6656Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi331ValidityFacts
    leaf6656LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6656CoverageChecked :
    coverageCheck (innerAD leaf6656Box) leaf6656InnerLog = true := by
  rfl'

private theorem leaf6656InnerLogValid :
    leaf6656InnerLog.Valid 8 (innerAD leaf6656Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint97PositiveFacts.valid leaf6656CoverageChecked

private noncomputable def leaf6656InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629643/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6656InputLogOnePlusV_eq :
    leaf6656InputLogOnePlusV = outerEnclosure 24
      (leaf6656Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6656RoundedFacts : LeafRoundedFacts 8
    leaf6656Certificate.logOnePlusV leaf6656InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6656InputLogOnePlusV_eq }

private noncomputable def leaf6656Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi331InputQChi innerPair357Input
    leaf6656InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6656LowerChecked :
    lowerCheck 24 leaf6656Box leaf6656Inputs = true := by
  rfl'

private theorem leaf6656CoversExact : CoversExact 8
    leaf6656Box leaf6656Certificate leaf6656InnerLog leaf6656Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi331RoundedFacts
    innerPair357RoundedFacts leaf6656RoundedFacts (by rfl)

private theorem leaf6656FlatSound : Sound leaf6656Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6656CertificateValid
    leaf6656InnerLogValid leaf6656CoversExact leaf6656LowerChecked

private noncomputable def leaf6657Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (67/128), chiHi := (17/32) }

private noncomputable def leaf6657Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435813/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68711747584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (751373173/536870912) }, upper := { exponent := 1, mantissa := (2911/2048) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi332LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137428144125/137423495168) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf6657InnerLog : WideLogData :=
  innerPair357Data

set_option maxRecDepth 1000000 in
private theorem leaf6657LocalValidity :
    LeafFacts leaf6657Box leaf6657Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6657Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68711747584) }) = true
      norm_num [leaf6657Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6657CertificateValid :
    WideCertificateValid leaf6657Box leaf6657Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi332ValidityFacts
    leaf6657LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6657CoverageChecked :
    coverageCheck (innerAD leaf6657Box) leaf6657InnerLog = true := by
  rfl'

private theorem leaf6657InnerLogValid :
    leaf6657InnerLog.Valid 8 (innerAD leaf6657Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint97PositiveFacts.valid leaf6657CoverageChecked

private noncomputable def leaf6657InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (726853/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf6657InputLogOnePlusV_eq :
    leaf6657InputLogOnePlusV = outerEnclosure 24
      (leaf6657Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6657RoundedFacts : LeafRoundedFacts 8
    leaf6657Certificate.logOnePlusV leaf6657InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6657InputLogOnePlusV_eq }

private noncomputable def leaf6657Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi332InputQChi innerPair357Input
    leaf6657InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6657LowerChecked :
    lowerCheck 24 leaf6657Box leaf6657Inputs = true := by
  rfl'

private theorem leaf6657CoversExact : CoversExact 8
    leaf6657Box leaf6657Certificate leaf6657InnerLog leaf6657Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi332RoundedFacts
    innerPair357RoundedFacts leaf6657RoundedFacts (by rfl)

private theorem leaf6657FlatSound : Sound leaf6657Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6657CertificateValid
    leaf6657InnerLogValid leaf6657CoversExact leaf6657LowerChecked

private noncomputable def leaf6658Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (67/128), chiHi := (17/32) }

private noncomputable def leaf6658Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435815/268435456) }, vSqrt := { lower := (8191/8192), upper := (967836571/967770112) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (755763815/536870912) }, upper := { exponent := 1, mantissa := (183/128) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi332LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (1935606683/1935540224) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf6658InnerLog : WideLogData :=
  innerPair367Data

set_option maxRecDepth 1000000 in
private theorem leaf6658LocalValidity :
    LeafFacts leaf6658Box leaf6658Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6658Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (967836571/967770112) }) = true
      norm_num [leaf6658Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6658CertificateValid :
    WideCertificateValid leaf6658Box leaf6658Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi332ValidityFacts
    leaf6658LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6658CoverageChecked :
    coverageCheck (innerAD leaf6658Box) leaf6658InnerLog = true := by
  rfl'

private theorem leaf6658InnerLogValid :
    leaf6658InnerLog.Valid 8 (innerAD leaf6658Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint97PositiveFacts.valid leaf6658CoverageChecked

private noncomputable def leaf6658InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629657/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6658InputLogOnePlusV_eq :
    leaf6658InputLogOnePlusV = outerEnclosure 24
      (leaf6658Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6658RoundedFacts : LeafRoundedFacts 8
    leaf6658Certificate.logOnePlusV leaf6658InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6658InputLogOnePlusV_eq }

private noncomputable def leaf6658Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi332InputQChi innerPair367Input
    leaf6658InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6658LowerChecked :
    lowerCheck 24 leaf6658Box leaf6658Inputs = true := by
  rfl'

private theorem leaf6658CoversExact : CoversExact 8
    leaf6658Box leaf6658Certificate leaf6658InnerLog leaf6658Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi332RoundedFacts
    innerPair367RoundedFacts leaf6658RoundedFacts (by rfl)

private theorem leaf6658FlatSound : Sound leaf6658Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6658CertificateValid
    leaf6658InnerLogValid leaf6658CoversExact leaf6658LowerChecked

private noncomputable def leaf6659Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (17/32), chiHi := (69/128) }

private noncomputable def leaf6659Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435811/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68711775232) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (749669343/536870912) }, upper := { exponent := 1, mantissa := (11617/8192) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi327LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137428171773/137423550464) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf6659InnerLog : WideLogData :=
  innerPair357Data

set_option maxRecDepth 1000000 in
private theorem leaf6659LocalValidity :
    LeafFacts leaf6659Box leaf6659Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6659Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68711775232) }) = true
      norm_num [leaf6659Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6659CertificateValid :
    WideCertificateValid leaf6659Box leaf6659Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi327ValidityFacts
    leaf6659LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6659CoverageChecked :
    coverageCheck (innerAD leaf6659Box) leaf6659InnerLog = true := by
  rfl'

private theorem leaf6659InnerLogValid :
    leaf6659InnerLog.Valid 8 (innerAD leaf6659Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint97PositiveFacts.valid leaf6659CoverageChecked

private noncomputable def leaf6659InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629645/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6659InputLogOnePlusV_eq :
    leaf6659InputLogOnePlusV = outerEnclosure 24
      (leaf6659Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6659RoundedFacts : LeafRoundedFacts 8
    leaf6659Certificate.logOnePlusV leaf6659InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6659InputLogOnePlusV_eq }

private noncomputable def leaf6659Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi327InputQChi innerPair357Input
    leaf6659InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6659LowerChecked :
    lowerCheck 24 leaf6659Box leaf6659Inputs = true := by
  rfl'

private theorem leaf6659CoversExact : CoversExact 8
    leaf6659Box leaf6659Certificate leaf6659InnerLog leaf6659Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi327RoundedFacts
    innerPair357RoundedFacts leaf6659RoundedFacts (by rfl)

private theorem leaf6659FlatSound : Sound leaf6659Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6659CertificateValid
    leaf6659InnerLogValid leaf6659CoversExact leaf6659LowerChecked

private noncomputable def leaf6660Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (17/32), chiHi := (69/128) }

private noncomputable def leaf6660Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435813/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68711704576) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (754125517/536870912) }, upper := { exponent := 1, mantissa := (5843/4096) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi327LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137428101117/137423409152) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf6660InnerLog : WideLogData :=
  innerPair357Data

set_option maxRecDepth 1000000 in
private theorem leaf6660LocalValidity :
    LeafFacts leaf6660Box leaf6660Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6660Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68711704576) }) = true
      norm_num [leaf6660Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6660CertificateValid :
    WideCertificateValid leaf6660Box leaf6660Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi327ValidityFacts
    leaf6660LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6660CoverageChecked :
    coverageCheck (innerAD leaf6660Box) leaf6660InnerLog = true := by
  rfl'

private theorem leaf6660InnerLogValid :
    leaf6660InnerLog.Valid 8 (innerAD leaf6660Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint97PositiveFacts.valid leaf6660CoverageChecked

private noncomputable def leaf6660InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814827/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6660InputLogOnePlusV_eq :
    leaf6660InputLogOnePlusV = outerEnclosure 24
      (leaf6660Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6660RoundedFacts : LeafRoundedFacts 8
    leaf6660Certificate.logOnePlusV leaf6660InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6660InputLogOnePlusV_eq }

private noncomputable def leaf6660Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi327InputQChi innerPair357Input
    leaf6660InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6660LowerChecked :
    lowerCheck 24 leaf6660Box leaf6660Inputs = true := by
  rfl'

private theorem leaf6660CoversExact : CoversExact 8
    leaf6660Box leaf6660Certificate leaf6660InnerLog leaf6660Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi327RoundedFacts
    innerPair357RoundedFacts leaf6660RoundedFacts (by rfl)

private theorem leaf6660FlatSound : Sound leaf6660Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6660CertificateValid
    leaf6660InnerLogValid leaf6660CoversExact leaf6660LowerChecked

private noncomputable def leaf6661Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (69/128), chiHi := (35/64) }

private noncomputable def leaf6661Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217977/134217728) }, vSqrt := { lower := (65529/65536), upper := (2642940849/2642753536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (378356945/268435456) }, upper := { exponent := 1, mantissa := (2949/2048) } }, logOuter := sk129LogOuterCertificate, logK := sk129LogKCertificate, logChi := chi328LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (5285694385/5285507072) } }, logDArg := sk129LogDArgCertificate }

private noncomputable def leaf6661InnerLog : WideLogData :=
  innerPair827Data

set_option maxRecDepth 1000000 in
private theorem leaf6661LocalValidity :
    LeafFacts leaf6661Box leaf6661Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6661Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (2642940849/2642753536) }) = true
      norm_num [leaf6661Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6661CertificateValid :
    WideCertificateValid leaf6661Box leaf6661Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk129ValidityFacts chi328ValidityFacts
    leaf6661LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6661CoverageChecked :
    coverageCheck (innerAD leaf6661Box) leaf6661InnerLog = true := by
  rfl'

private theorem leaf6661InnerLogValid :
    leaf6661InnerLog.Valid 8 (innerAD leaf6661Box) :=
  wideLogDataValid_of_cachedCheck endpoint521PositiveFacts
    endpoint522PositiveFacts.valid leaf6661CoverageChecked

private noncomputable def leaf6661InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629675/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6661InputLogOnePlusV_eq :
    leaf6661InputLogOnePlusV = outerEnclosure 24
      (leaf6661Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6661RoundedFacts : LeafRoundedFacts 8
    leaf6661Certificate.logOnePlusV leaf6661InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6661InputLogOnePlusV_eq }

private noncomputable def leaf6661Inputs : Inputs :=
  inputsOfCaches globalInput sk129RoundedInputs
    chi328InputQChi innerPair827Input
    leaf6661InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6661LowerChecked :
    lowerCheck 24 leaf6661Box leaf6661Inputs = true := by
  rfl'

private theorem leaf6661CoversExact : CoversExact 8
    leaf6661Box leaf6661Certificate leaf6661InnerLog leaf6661Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk129RoundedFacts chi328RoundedFacts
    innerPair827RoundedFacts leaf6661RoundedFacts (by rfl)

private theorem leaf6661FlatSound : Sound leaf6661Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6661CertificateValid
    leaf6661InnerLogValid leaf6661CoversExact leaf6661LowerChecked

private noncomputable def leaf6662Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (17/32), chiHi := (69/128) }

private noncomputable def leaf6662Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435815/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68711633920) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (758581691/536870912) }, upper := { exponent := 1, mantissa := (11755/8192) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi327LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137428030461/137423267840) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf6662InnerLog : WideLogData :=
  innerPair367Data

set_option maxRecDepth 1000000 in
private theorem leaf6662LocalValidity :
    LeafFacts leaf6662Box leaf6662Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6662Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68711633920) }) = true
      norm_num [leaf6662Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6662CertificateValid :
    WideCertificateValid leaf6662Box leaf6662Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi327ValidityFacts
    leaf6662LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6662CoverageChecked :
    coverageCheck (innerAD leaf6662Box) leaf6662InnerLog = true := by
  rfl'

private theorem leaf6662InnerLogValid :
    leaf6662InnerLog.Valid 8 (innerAD leaf6662Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint97PositiveFacts.valid leaf6662CoverageChecked

private noncomputable def leaf6662InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814831/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6662InputLogOnePlusV_eq :
    leaf6662InputLogOnePlusV = outerEnclosure 24
      (leaf6662Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6662RoundedFacts : LeafRoundedFacts 8
    leaf6662Certificate.logOnePlusV leaf6662InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6662InputLogOnePlusV_eq }

private noncomputable def leaf6662Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi327InputQChi innerPair367Input
    leaf6662InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6662LowerChecked :
    lowerCheck 24 leaf6662Box leaf6662Inputs = true := by
  rfl'

private theorem leaf6662CoversExact : CoversExact 8
    leaf6662Box leaf6662Certificate leaf6662InnerLog leaf6662Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi327RoundedFacts
    innerPair367RoundedFacts leaf6662RoundedFacts (by rfl)

private theorem leaf6662FlatSound : Sound leaf6662Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6662CertificateValid
    leaf6662InnerLogValid leaf6662CoversExact leaf6662LowerChecked

private noncomputable def leaf6663Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (17/32), chiHi := (69/128) }

private noncomputable def leaf6663Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435817/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711563264) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (763037865/536870912) }, upper := { exponent := 1, mantissa := (739/512) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi327LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137427959805/137423126528) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf6663InnerLog : WideLogData :=
  innerPair368Data

set_option maxRecDepth 1000000 in
private theorem leaf6663LocalValidity :
    LeafFacts leaf6663Box leaf6663Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6663Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711563264) }) = true
      norm_num [leaf6663Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6663CertificateValid :
    WideCertificateValid leaf6663Box leaf6663Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi327ValidityFacts
    leaf6663LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6663CoverageChecked :
    coverageCheck (innerAD leaf6663Box) leaf6663InnerLog = true := by
  rfl'

private theorem leaf6663InnerLogValid :
    leaf6663InnerLog.Valid 8 (innerAD leaf6663Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint98PositiveFacts.valid leaf6663CoverageChecked

private noncomputable def leaf6663InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629671/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6663InputLogOnePlusV_eq :
    leaf6663InputLogOnePlusV = outerEnclosure 24
      (leaf6663Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6663RoundedFacts : LeafRoundedFacts 8
    leaf6663Certificate.logOnePlusV leaf6663InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6663InputLogOnePlusV_eq }

private noncomputable def leaf6663Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi327InputQChi innerPair368Input
    leaf6663InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6663LowerChecked :
    lowerCheck 24 leaf6663Box leaf6663Inputs = true := by
  rfl'

private theorem leaf6663CoversExact : CoversExact 8
    leaf6663Box leaf6663Certificate leaf6663InnerLog leaf6663Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi327RoundedFacts
    innerPair368RoundedFacts leaf6663RoundedFacts (by rfl)

private theorem leaf6663FlatSound : Sound leaf6663Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6663CertificateValid
    leaf6663InnerLogValid leaf6663CoversExact leaf6663LowerChecked

private noncomputable def leaf6664Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (69/128), chiHi := (35/64) }

private noncomputable def leaf6664Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435817/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68711520256) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (765790209/536870912) }, upper := { exponent := 1, mantissa := (5933/4096) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi328LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137427916797/137423040512) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf6664InnerLog : WideLogData :=
  innerPair368Data

set_option maxRecDepth 1000000 in
private theorem leaf6664LocalValidity :
    LeafFacts leaf6664Box leaf6664Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6664Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68711520256) }) = true
      norm_num [leaf6664Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6664CertificateValid :
    WideCertificateValid leaf6664Box leaf6664Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi328ValidityFacts
    leaf6664LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6664CoverageChecked :
    coverageCheck (innerAD leaf6664Box) leaf6664InnerLog = true := by
  rfl'

private theorem leaf6664InnerLogValid :
    leaf6664InnerLog.Valid 8 (innerAD leaf6664Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint98PositiveFacts.valid leaf6664CoverageChecked

private noncomputable def leaf6664InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907419/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6664InputLogOnePlusV_eq :
    leaf6664InputLogOnePlusV = outerEnclosure 24
      (leaf6664Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6664RoundedFacts : LeafRoundedFacts 8
    leaf6664Certificate.logOnePlusV leaf6664InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6664InputLogOnePlusV_eq }

private noncomputable def leaf6664Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi328InputQChi innerPair368Input
    leaf6664InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6664LowerChecked :
    lowerCheck 24 leaf6664Box leaf6664Inputs = true := by
  rfl'

private theorem leaf6664CoversExact : CoversExact 8
    leaf6664Box leaf6664Certificate leaf6664InnerLog leaf6664Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi328RoundedFacts
    innerPair368RoundedFacts leaf6664RoundedFacts (by rfl)

private theorem leaf6664FlatSound : Sound leaf6664Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6664CertificateValid
    leaf6664InnerLogValid leaf6664CoversExact leaf6664LowerChecked

private noncomputable def leaf6665Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (69/128), chiHi := (35/64) }

private noncomputable def leaf6665Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435819/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711448576) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (770311915/536870912) }, upper := { exponent := 1, mantissa := (373/256) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi328LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137427845117/137422897152) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf6665InnerLog : WideLogData :=
  innerPair368Data

set_option maxRecDepth 1000000 in
private theorem leaf6665LocalValidity :
    LeafFacts leaf6665Box leaf6665Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6665Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711448576) }) = true
      norm_num [leaf6665Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6665CertificateValid :
    WideCertificateValid leaf6665Box leaf6665Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi328ValidityFacts
    leaf6665LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6665CoverageChecked :
    coverageCheck (innerAD leaf6665Box) leaf6665InnerLog = true := by
  rfl'

private theorem leaf6665InnerLogValid :
    leaf6665InnerLog.Valid 8 (innerAD leaf6665Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint98PositiveFacts.valid leaf6665CoverageChecked

private noncomputable def leaf6665InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629685/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6665InputLogOnePlusV_eq :
    leaf6665InputLogOnePlusV = outerEnclosure 24
      (leaf6665Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6665RoundedFacts : LeafRoundedFacts 8
    leaf6665Certificate.logOnePlusV leaf6665InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6665InputLogOnePlusV_eq }

private noncomputable def leaf6665Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi328InputQChi innerPair368Input
    leaf6665InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6665LowerChecked :
    lowerCheck 24 leaf6665Box leaf6665Inputs = true := by
  rfl'

private theorem leaf6665CoversExact : CoversExact 8
    leaf6665Box leaf6665Certificate leaf6665InnerLog leaf6665Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi328RoundedFacts
    innerPair368RoundedFacts leaf6665RoundedFacts (by rfl)

private theorem leaf6665FlatSound : Sound leaf6665Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6665CertificateValid
    leaf6665InnerLogValid leaf6665CoversExact leaf6665LowerChecked

private noncomputable def leaf6666Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (35/64), chiHi := (71/128) }

private noncomputable def leaf6666Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217979/134217728) }, vSqrt := { lower := (65529/65536), upper := (11452743679/11451913216) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (381895671/268435456) }, upper := { exponent := 1, mantissa := (5953/4096) } }, logOuter := sk129LogOuterCertificate, logK := sk129LogKCertificate, logChi := chi333LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (22904656895/22903826432) } }, logDArg := sk129LogDArgCertificate }

private noncomputable def leaf6666InnerLog : WideLogData :=
  innerPair732Data

set_option maxRecDepth 1000000 in
private theorem leaf6666LocalValidity :
    LeafFacts leaf6666Box leaf6666Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6666Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (11452743679/11451913216) }) = true
      norm_num [leaf6666Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6666CertificateValid :
    WideCertificateValid leaf6666Box leaf6666Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk129ValidityFacts chi333ValidityFacts
    leaf6666LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6666CoverageChecked :
    coverageCheck (innerAD leaf6666Box) leaf6666InnerLog = true := by
  rfl'

private theorem leaf6666InnerLogValid :
    leaf6666InnerLog.Valid 8 (innerAD leaf6666Box) :=
  wideLogDataValid_of_cachedCheck endpoint469PositiveFacts
    endpoint523PositiveFacts.valid leaf6666CoverageChecked

private noncomputable def leaf6666InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629689/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6666InputLogOnePlusV_eq :
    leaf6666InputLogOnePlusV = outerEnclosure 24
      (leaf6666Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6666RoundedFacts : LeafRoundedFacts 8
    leaf6666Certificate.logOnePlusV leaf6666InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6666InputLogOnePlusV_eq }

private noncomputable def leaf6666Inputs : Inputs :=
  inputsOfCaches globalInput sk129RoundedInputs
    chi333InputQChi innerPair732Input
    leaf6666InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6666LowerChecked :
    lowerCheck 24 leaf6666Box leaf6666Inputs = true := by
  rfl'

private theorem leaf6666CoversExact : CoversExact 8
    leaf6666Box leaf6666Certificate leaf6666InnerLog leaf6666Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk129RoundedFacts chi333RoundedFacts
    innerPair732RoundedFacts leaf6666RoundedFacts (by rfl)

private theorem leaf6666FlatSound : Sound leaf6666Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6666CertificateValid
    leaf6666InnerLogValid leaf6666CoversExact leaf6666LowerChecked

private noncomputable def leaf6667Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (71/128), chiHi := (9/16) }

private noncomputable def leaf6667Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217981/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34355683328) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (385434397/268435456) }, upper := { exponent := 1, mantissa := (751/512) } }, logOuter := sk129LogOuterCertificate, logK := sk129LogKCertificate, logChi := chi334LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68713914365/68711366656) } }, logDArg := sk129LogDArgCertificate }

private noncomputable def leaf6667InnerLog : WideLogData :=
  innerPair368Data

set_option maxRecDepth 1000000 in
private theorem leaf6667LocalValidity :
    LeafFacts leaf6667Box leaf6667Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6667Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34355683328) }) = true
      norm_num [leaf6667Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6667CertificateValid :
    WideCertificateValid leaf6667Box leaf6667Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk129ValidityFacts chi334ValidityFacts
    leaf6667LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6667CoverageChecked :
    coverageCheck (innerAD leaf6667Box) leaf6667InnerLog = true := by
  rfl'

private theorem leaf6667InnerLogValid :
    leaf6667InnerLog.Valid 8 (innerAD leaf6667Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint98PositiveFacts.valid leaf6667CoverageChecked

private noncomputable def leaf6667InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629703/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6667InputLogOnePlusV_eq :
    leaf6667InputLogOnePlusV = outerEnclosure 24
      (leaf6667Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6667RoundedFacts : LeafRoundedFacts 8
    leaf6667Certificate.logOnePlusV leaf6667InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6667InputLogOnePlusV_eq }

private noncomputable def leaf6667Inputs : Inputs :=
  inputsOfCaches globalInput sk129RoundedInputs
    chi334InputQChi innerPair368Input
    leaf6667InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6667LowerChecked :
    lowerCheck 24 leaf6667Box leaf6667Inputs = true := by
  rfl'

private theorem leaf6667CoversExact : CoversExact 8
    leaf6667Box leaf6667Certificate leaf6667InnerLog leaf6667Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk129RoundedFacts chi334RoundedFacts
    innerPair368RoundedFacts leaf6667RoundedFacts (by rfl)

private theorem leaf6667FlatSound : Sound leaf6667Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6667CertificateValid
    leaf6667InnerLogValid leaf6667CoversExact leaf6667LowerChecked

private noncomputable def leaf6668Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (35/64), chiHi := (71/128) }

private noncomputable def leaf6668Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217981/134217728) }, vSqrt := { lower := (8191/8192), upper := (34358231037/34355666944) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (386482909/268435456) }, upper := { exponent := 1, mantissa := (753/512) } }, logOuter := sk130LogOuterCertificate, logK := sk130LogKCertificate, logChi := chi333LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68713897981/68711333888) } }, logDArg := sk130LogDArgCertificate }

private noncomputable def leaf6668InnerLog : WideLogData :=
  innerPair829Data

set_option maxRecDepth 1000000 in
private theorem leaf6668LocalValidity :
    LeafFacts leaf6668Box leaf6668Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6668Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358231037/34355666944) }) = true
      norm_num [leaf6668Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6668CertificateValid :
    WideCertificateValid leaf6668Box leaf6668Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk130ValidityFacts chi333ValidityFacts
    leaf6668LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6668CoverageChecked :
    coverageCheck (innerAD leaf6668Box) leaf6668InnerLog = true := by
  rfl'

private theorem leaf6668InnerLogValid :
    leaf6668InnerLog.Valid 8 (innerAD leaf6668Box) :=
  wideLogDataValid_of_cachedCheck endpoint524PositiveFacts
    endpoint525PositiveFacts.valid leaf6668CoverageChecked

private noncomputable def leaf6668InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629707/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6668InputLogOnePlusV_eq :
    leaf6668InputLogOnePlusV = outerEnclosure 24
      (leaf6668Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6668RoundedFacts : LeafRoundedFacts 8
    leaf6668Certificate.logOnePlusV leaf6668InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6668InputLogOnePlusV_eq }

private noncomputable def leaf6668Inputs : Inputs :=
  inputsOfCaches globalInput sk130RoundedInputs
    chi333InputQChi innerPair829Input
    leaf6668InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6668LowerChecked :
    lowerCheck 24 leaf6668Box leaf6668Inputs = true := by
  rfl'

private theorem leaf6668CoversExact : CoversExact 8
    leaf6668Box leaf6668Certificate leaf6668InnerLog leaf6668Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk130RoundedFacts chi333RoundedFacts
    innerPair829RoundedFacts leaf6668RoundedFacts (by rfl)

private theorem leaf6668FlatSound : Sound leaf6668Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6668CertificateValid
    leaf6668InnerLogValid leaf6668CoversExact leaf6668LowerChecked

private noncomputable def leaf6669Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (71/128), chiHi := (9/16) }

private noncomputable def leaf6669Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217983/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588902400) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (390087167/268435456) }, upper := { exponent := 1, mantissa := (95/64) } }, logOuter := sk130LogOuterCertificate, logK := sk130LogKCertificate, logChi := chi334LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178329087/17177804800) } }, logDArg := sk130LogDArgCertificate }

private noncomputable def leaf6669InnerLog : WideLogData :=
  innerPair735Data

set_option maxRecDepth 1000000 in
private theorem leaf6669LocalValidity :
    LeafFacts leaf6669Box leaf6669Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6669Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588902400) }) = true
      norm_num [leaf6669Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6669CertificateValid :
    WideCertificateValid leaf6669Box leaf6669Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk130ValidityFacts chi334ValidityFacts
    leaf6669LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6669CoverageChecked :
    coverageCheck (innerAD leaf6669Box) leaf6669InnerLog = true := by
  rfl'

private theorem leaf6669InnerLogValid :
    leaf6669InnerLog.Valid 8 (innerAD leaf6669Box) :=
  wideLogDataValid_of_cachedCheck endpoint471PositiveFacts
    endpoint481PositiveFacts.valid leaf6669CoverageChecked

private noncomputable def leaf6669InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629593/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6669InputLogOnePlusV_eq :
    leaf6669InputLogOnePlusV = outerEnclosure 24
      (leaf6669Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6669RoundedFacts : LeafRoundedFacts 8
    leaf6669Certificate.logOnePlusV leaf6669InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6669InputLogOnePlusV_eq }

private noncomputable def leaf6669Inputs : Inputs :=
  inputsOfCaches globalInput sk130RoundedInputs
    chi334InputQChi innerPair735Input
    leaf6669InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6669LowerChecked :
    lowerCheck 24 leaf6669Box leaf6669Inputs = true := by
  rfl'

private theorem leaf6669CoversExact : CoversExact 8
    leaf6669Box leaf6669Certificate leaf6669InnerLog leaf6669Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk130RoundedFacts chi334RoundedFacts
    innerPair735RoundedFacts leaf6669RoundedFacts (by rfl)

private theorem leaf6669FlatSound : Sound leaf6669Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6669CertificateValid
    leaf6669InnerLogValid leaf6669CoversExact leaf6669LowerChecked

private noncomputable def component134Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (1/2), chiHi := (65/128) }

set_option maxRecDepth 1000000 in
private theorem component134Node0_sound : Sound component134Node0Box :=
  sound_of_literal_split component134Node0Box leaf6618Box leaf6619Box
    .k (105/32) (by rfl) (by rfl)
    leaf6618FlatSound leaf6619FlatSound

private noncomputable def component134Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (65/128), chiHi := (33/64) }

set_option maxRecDepth 1000000 in
private theorem component134Node1_sound : Sound component134Node1Box :=
  sound_of_literal_split component134Node1Box leaf6620Box leaf6621Box
    .k (105/32) (by rfl) (by rfl)
    leaf6620FlatSound leaf6621FlatSound

private noncomputable def component134Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (1/2), chiHi := (33/64) }

set_option maxRecDepth 1000000 in
private theorem component134Node2_sound : Sound component134Node2Box :=
  sound_of_literal_split component134Node2Box component134Node0Box component134Node1Box
    .chi (65/128) (by rfl) (by rfl)
    component134Node0_sound component134Node1_sound

private noncomputable def component134Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (1/2), chiHi := (65/128) }

set_option maxRecDepth 1000000 in
private theorem component134Node3_sound : Sound component134Node3Box :=
  sound_of_literal_split component134Node3Box leaf6622Box leaf6623Box
    .k (107/32) (by rfl) (by rfl)
    leaf6622FlatSound leaf6623FlatSound

private noncomputable def component134Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (65/128), chiHi := (33/64) }

set_option maxRecDepth 1000000 in
private theorem component134Node4_sound : Sound component134Node4Box :=
  sound_of_literal_split component134Node4Box leaf6624Box leaf6625Box
    .k (107/32) (by rfl) (by rfl)
    leaf6624FlatSound leaf6625FlatSound

private noncomputable def component134Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (1/2), chiHi := (33/64) }

set_option maxRecDepth 1000000 in
private theorem component134Node5_sound : Sound component134Node5Box :=
  sound_of_literal_split component134Node5Box component134Node3Box component134Node4Box
    .chi (65/128) (by rfl) (by rfl)
    component134Node3_sound component134Node4_sound

private noncomputable def component134Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (1/2), chiHi := (33/64) }

set_option maxRecDepth 1000000 in
private theorem component134Node6_sound : Sound component134Node6Box :=
  sound_of_literal_split component134Node6Box component134Node2Box component134Node5Box
    .k (53/16) (by rfl) (by rfl)
    component134Node2_sound component134Node5_sound

private noncomputable def component134Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (33/64), chiHi := (67/128) }

set_option maxRecDepth 1000000 in
private theorem component134Node7_sound : Sound component134Node7Box :=
  sound_of_literal_split component134Node7Box leaf6626Box leaf6627Box
    .k (105/32) (by rfl) (by rfl)
    leaf6626FlatSound leaf6627FlatSound

private noncomputable def component134Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (67/128), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component134Node8_sound : Sound component134Node8Box :=
  sound_of_literal_split component134Node8Box leaf6628Box leaf6629Box
    .k (105/32) (by rfl) (by rfl)
    leaf6628FlatSound leaf6629FlatSound

private noncomputable def component134Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (33/64), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component134Node9_sound : Sound component134Node9Box :=
  sound_of_literal_split component134Node9Box component134Node7Box component134Node8Box
    .chi (67/128) (by rfl) (by rfl)
    component134Node7_sound component134Node8_sound

private noncomputable def component134Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (33/64), chiHi := (67/128) }

set_option maxRecDepth 1000000 in
private theorem component134Node10_sound : Sound component134Node10Box :=
  sound_of_literal_split component134Node10Box leaf6630Box leaf6631Box
    .k (107/32) (by rfl) (by rfl)
    leaf6630FlatSound leaf6631FlatSound

private noncomputable def component134Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (67/128), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component134Node11_sound : Sound component134Node11Box :=
  sound_of_literal_split component134Node11Box leaf6632Box leaf6633Box
    .k (107/32) (by rfl) (by rfl)
    leaf6632FlatSound leaf6633FlatSound

private noncomputable def component134Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (33/64), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component134Node12_sound : Sound component134Node12Box :=
  sound_of_literal_split component134Node12Box component134Node10Box component134Node11Box
    .chi (67/128) (by rfl) (by rfl)
    component134Node10_sound component134Node11_sound

private noncomputable def component134Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (33/64), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component134Node13_sound : Sound component134Node13Box :=
  sound_of_literal_split component134Node13Box component134Node9Box component134Node12Box
    .k (53/16) (by rfl) (by rfl)
    component134Node9_sound component134Node12_sound

private noncomputable def component134Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (1/2), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component134Node14_sound : Sound component134Node14Box :=
  sound_of_literal_split component134Node14Box component134Node6Box component134Node13Box
    .chi (33/64) (by rfl) (by rfl)
    component134Node6_sound component134Node13_sound

private noncomputable def component134Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (17/32), chiHi := (35/64) }

set_option maxRecDepth 1000000 in
private theorem component134Node15_sound : Sound component134Node15Box :=
  sound_of_literal_split component134Node15Box leaf6634Box leaf6635Box
    .chi (69/128) (by rfl) (by rfl)
    leaf6634FlatSound leaf6635FlatSound

private noncomputable def component134Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (17/32), chiHi := (69/128) }

set_option maxRecDepth 1000000 in
private theorem component134Node16_sound : Sound component134Node16Box :=
  sound_of_literal_split component134Node16Box leaf6636Box leaf6637Box
    .k (107/32) (by rfl) (by rfl)
    leaf6636FlatSound leaf6637FlatSound

private noncomputable def component134Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (17/32), chiHi := (35/64) }

set_option maxRecDepth 1000000 in
private theorem component134Node17_sound : Sound component134Node17Box :=
  sound_of_literal_split component134Node17Box component134Node16Box leaf6638Box
    .chi (69/128) (by rfl) (by rfl)
    component134Node16_sound leaf6638FlatSound

private noncomputable def component134Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (17/32), chiHi := (35/64) }

set_option maxRecDepth 1000000 in
private theorem component134Node18_sound : Sound component134Node18Box :=
  sound_of_literal_split component134Node18Box component134Node15Box component134Node17Box
    .k (53/16) (by rfl) (by rfl)
    component134Node15_sound component134Node17_sound

private noncomputable def component134Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (35/64), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component134Node19_sound : Sound component134Node19Box :=
  sound_of_literal_split component134Node19Box leaf6639Box leaf6640Box
    .chi (71/128) (by rfl) (by rfl)
    leaf6639FlatSound leaf6640FlatSound

private noncomputable def component134Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (35/64), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component134Node20_sound : Sound component134Node20Box :=
  sound_of_literal_split component134Node20Box leaf6641Box leaf6642Box
    .chi (71/128) (by rfl) (by rfl)
    leaf6641FlatSound leaf6642FlatSound

private noncomputable def component134Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (35/64), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component134Node21_sound : Sound component134Node21Box :=
  sound_of_literal_split component134Node21Box component134Node19Box component134Node20Box
    .k (53/16) (by rfl) (by rfl)
    component134Node19_sound component134Node20_sound

private noncomputable def component134Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (17/32), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component134Node22_sound : Sound component134Node22Box :=
  sound_of_literal_split component134Node22Box component134Node18Box component134Node21Box
    .chi (35/64) (by rfl) (by rfl)
    component134Node18_sound component134Node21_sound

private noncomputable def component134Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (1/2), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component134Node23_sound : Sound component134Node23Box :=
  sound_of_literal_split component134Node23Box component134Node14Box component134Node22Box
    .chi (17/32) (by rfl) (by rfl)
    component134Node14_sound component134Node22_sound

private noncomputable def component134Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (1/2), chiHi := (65/128) }

set_option maxRecDepth 1000000 in
private theorem component134Node24_sound : Sound component134Node24Box :=
  sound_of_literal_split component134Node24Box leaf6643Box leaf6644Box
    .k (109/32) (by rfl) (by rfl)
    leaf6643FlatSound leaf6644FlatSound

private noncomputable def component134Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (65/128), chiHi := (33/64) }

set_option maxRecDepth 1000000 in
private theorem component134Node25_sound : Sound component134Node25Box :=
  sound_of_literal_split component134Node25Box leaf6645Box leaf6646Box
    .k (109/32) (by rfl) (by rfl)
    leaf6645FlatSound leaf6646FlatSound

private noncomputable def component134Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (1/2), chiHi := (33/64) }

set_option maxRecDepth 1000000 in
private theorem component134Node26_sound : Sound component134Node26Box :=
  sound_of_literal_split component134Node26Box component134Node24Box component134Node25Box
    .chi (65/128) (by rfl) (by rfl)
    component134Node24_sound component134Node25_sound

private noncomputable def component134Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (1/2), chiHi := (65/128) }

set_option maxRecDepth 1000000 in
private theorem component134Node27_sound : Sound component134Node27Box :=
  sound_of_literal_split component134Node27Box leaf6647Box leaf6648Box
    .k (111/32) (by rfl) (by rfl)
    leaf6647FlatSound leaf6648FlatSound

private noncomputable def component134Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (65/128), chiHi := (33/64) }

set_option maxRecDepth 1000000 in
private theorem component134Node28_sound : Sound component134Node28Box :=
  sound_of_literal_split component134Node28Box leaf6649Box leaf6650Box
    .k (111/32) (by rfl) (by rfl)
    leaf6649FlatSound leaf6650FlatSound

private noncomputable def component134Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (1/2), chiHi := (33/64) }

set_option maxRecDepth 1000000 in
private theorem component134Node29_sound : Sound component134Node29Box :=
  sound_of_literal_split component134Node29Box component134Node27Box component134Node28Box
    .chi (65/128) (by rfl) (by rfl)
    component134Node27_sound component134Node28_sound

private noncomputable def component134Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (1/2), chiHi := (33/64) }

set_option maxRecDepth 1000000 in
private theorem component134Node30_sound : Sound component134Node30Box :=
  sound_of_literal_split component134Node30Box component134Node26Box component134Node29Box
    .k (55/16) (by rfl) (by rfl)
    component134Node26_sound component134Node29_sound

private noncomputable def component134Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (33/64), chiHi := (67/128) }

set_option maxRecDepth 1000000 in
private theorem component134Node31_sound : Sound component134Node31Box :=
  sound_of_literal_split component134Node31Box leaf6651Box leaf6652Box
    .k (109/32) (by rfl) (by rfl)
    leaf6651FlatSound leaf6652FlatSound

private noncomputable def component134Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (67/128), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component134Node32_sound : Sound component134Node32Box :=
  sound_of_literal_split component134Node32Box leaf6653Box leaf6654Box
    .k (109/32) (by rfl) (by rfl)
    leaf6653FlatSound leaf6654FlatSound

private noncomputable def component134Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (33/64), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component134Node33_sound : Sound component134Node33Box :=
  sound_of_literal_split component134Node33Box component134Node31Box component134Node32Box
    .chi (67/128) (by rfl) (by rfl)
    component134Node31_sound component134Node32_sound

private noncomputable def component134Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (33/64), chiHi := (67/128) }

set_option maxRecDepth 1000000 in
private theorem component134Node34_sound : Sound component134Node34Box :=
  sound_of_literal_split component134Node34Box leaf6655Box leaf6656Box
    .k (111/32) (by rfl) (by rfl)
    leaf6655FlatSound leaf6656FlatSound

private noncomputable def component134Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (67/128), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component134Node35_sound : Sound component134Node35Box :=
  sound_of_literal_split component134Node35Box leaf6657Box leaf6658Box
    .k (111/32) (by rfl) (by rfl)
    leaf6657FlatSound leaf6658FlatSound

private noncomputable def component134Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (33/64), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component134Node36_sound : Sound component134Node36Box :=
  sound_of_literal_split component134Node36Box component134Node34Box component134Node35Box
    .chi (67/128) (by rfl) (by rfl)
    component134Node34_sound component134Node35_sound

private noncomputable def component134Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (33/64), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component134Node37_sound : Sound component134Node37Box :=
  sound_of_literal_split component134Node37Box component134Node33Box component134Node36Box
    .k (55/16) (by rfl) (by rfl)
    component134Node33_sound component134Node36_sound

private noncomputable def component134Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (1/2), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component134Node38_sound : Sound component134Node38Box :=
  sound_of_literal_split component134Node38Box component134Node30Box component134Node37Box
    .chi (33/64) (by rfl) (by rfl)
    component134Node30_sound component134Node37_sound

private noncomputable def component134Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (17/32), chiHi := (69/128) }

set_option maxRecDepth 1000000 in
private theorem component134Node39_sound : Sound component134Node39Box :=
  sound_of_literal_split component134Node39Box leaf6659Box leaf6660Box
    .k (109/32) (by rfl) (by rfl)
    leaf6659FlatSound leaf6660FlatSound

private noncomputable def component134Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (17/32), chiHi := (35/64) }

set_option maxRecDepth 1000000 in
private theorem component134Node40_sound : Sound component134Node40Box :=
  sound_of_literal_split component134Node40Box component134Node39Box leaf6661Box
    .chi (69/128) (by rfl) (by rfl)
    component134Node39_sound leaf6661FlatSound

private noncomputable def component134Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (17/32), chiHi := (69/128) }

set_option maxRecDepth 1000000 in
private theorem component134Node41_sound : Sound component134Node41Box :=
  sound_of_literal_split component134Node41Box leaf6662Box leaf6663Box
    .k (111/32) (by rfl) (by rfl)
    leaf6662FlatSound leaf6663FlatSound

private noncomputable def component134Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (69/128), chiHi := (35/64) }

set_option maxRecDepth 1000000 in
private theorem component134Node42_sound : Sound component134Node42Box :=
  sound_of_literal_split component134Node42Box leaf6664Box leaf6665Box
    .k (111/32) (by rfl) (by rfl)
    leaf6664FlatSound leaf6665FlatSound

private noncomputable def component134Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (17/32), chiHi := (35/64) }

set_option maxRecDepth 1000000 in
private theorem component134Node43_sound : Sound component134Node43Box :=
  sound_of_literal_split component134Node43Box component134Node41Box component134Node42Box
    .chi (69/128) (by rfl) (by rfl)
    component134Node41_sound component134Node42_sound

private noncomputable def component134Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (17/32), chiHi := (35/64) }

set_option maxRecDepth 1000000 in
private theorem component134Node44_sound : Sound component134Node44Box :=
  sound_of_literal_split component134Node44Box component134Node40Box component134Node43Box
    .k (55/16) (by rfl) (by rfl)
    component134Node40_sound component134Node43_sound

private noncomputable def component134Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (35/64), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component134Node45_sound : Sound component134Node45Box :=
  sound_of_literal_split component134Node45Box leaf6666Box leaf6667Box
    .chi (71/128) (by rfl) (by rfl)
    leaf6666FlatSound leaf6667FlatSound

private noncomputable def component134Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (35/64), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component134Node46_sound : Sound component134Node46Box :=
  sound_of_literal_split component134Node46Box leaf6668Box leaf6669Box
    .chi (71/128) (by rfl) (by rfl)
    leaf6668FlatSound leaf6669FlatSound

private noncomputable def component134Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (35/64), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component134Node47_sound : Sound component134Node47Box :=
  sound_of_literal_split component134Node47Box component134Node45Box component134Node46Box
    .k (55/16) (by rfl) (by rfl)
    component134Node45_sound component134Node46_sound

private noncomputable def component134Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (17/32), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component134Node48_sound : Sound component134Node48Box :=
  sound_of_literal_split component134Node48Box component134Node44Box component134Node47Box
    .chi (35/64) (by rfl) (by rfl)
    component134Node44_sound component134Node47_sound

private noncomputable def component134Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (1/2), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component134Node49_sound : Sound component134Node49Box :=
  sound_of_literal_split component134Node49Box component134Node38Box component134Node48Box
    .chi (17/32) (by rfl) (by rfl)
    component134Node38_sound component134Node48_sound

noncomputable def component134Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (7/2), chiLo := (1/2), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
theorem component134_sound : Sound component134Box :=
  sound_of_literal_split component134Box component134Node23Box component134Node49Box
    .k (27/8) (by rfl) (by rfl)
    component134Node23_sound component134Node49_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
