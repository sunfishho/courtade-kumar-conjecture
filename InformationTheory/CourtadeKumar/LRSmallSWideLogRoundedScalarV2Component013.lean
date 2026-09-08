import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch4
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

private noncomputable def leaf543Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (17/16), chiLo := (3/4), chiHi := (13/16) }

private noncomputable def leaf543Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (16777275/16777216) }, vSqrt := { lower := (65533/65536), upper := (34359279615/34357927936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (29326535/16777216) }, upper := { exponent := 0, mantissa := (477/256) } }, logOuter := sk18LogOuterCertificate, logK := sk18LogKCertificate, logChi := chi76LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (68717207551/68715855872) } }, logDArg := sk18LogDArgCertificate }

private noncomputable def leaf543InnerLog : WideLogData :=
  innerPair67Data

set_option maxRecDepth 1000000 in
private theorem leaf543LocalValidity :
    LeafFacts leaf543Box leaf543Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf543Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (34359279615/34357927936) }) = true
      norm_num [leaf543Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf543CertificateValid :
    WideCertificateValid leaf543Box leaf543Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk18ValidityFacts chi76ValidityFacts
    leaf543LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf543CoverageChecked :
    coverageCheck (innerAD leaf543Box) leaf543InnerLog = true := by
  rfl'

private theorem leaf543InnerLogValid :
    leaf543InnerLog.Valid 8 (innerAD leaf543Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint22PositiveFacts.valid leaf543CoverageChecked

private noncomputable def leaf543InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629411/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf543InputLogOnePlusV_eq :
    leaf543InputLogOnePlusV = outerEnclosure 24
      (leaf543Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf543RoundedFacts : LeafRoundedFacts 8
    leaf543Certificate.logOnePlusV leaf543InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf543InputLogOnePlusV_eq }

private noncomputable def leaf543Inputs : Inputs :=
  inputsOfCaches globalInput sk18RoundedInputs
    chi76InputQChi innerPair67Input
    leaf543InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf543LowerChecked :
    lowerCheck 24 leaf543Box leaf543Inputs = true := by
  rfl'

private theorem leaf543CoversExact : CoversExact 8
    leaf543Box leaf543Certificate leaf543InnerLog leaf543Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk18RoundedFacts chi76RoundedFacts
    innerPair67RoundedFacts leaf543RoundedFacts (by rfl)

private theorem leaf543FlatSound : Sound leaf543Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf543CertificateValid
    leaf543InnerLogValid leaf543CoversExact leaf543LowerChecked

private noncomputable def leaf544Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/16), kHi := (9/8), chiLo := (3/4), chiHi := (13/16) }

private noncomputable def leaf544Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (16777277/16777216) }, vSqrt := { lower := (65533/65536), upper := (404226819/404209664) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (30112917/16777216) }, upper := { exponent := 0, mantissa := (245/128) } }, logOuter := sk19LogOuterCertificate, logK := sk19LogKCertificate, logChi := chi76LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (808436483/808419328) } }, logDArg := sk19LogDArgCertificate }

private noncomputable def leaf544InnerLog : WideLogData :=
  innerPair73Data

set_option maxRecDepth 1000000 in
private theorem leaf544LocalValidity :
    LeafFacts leaf544Box leaf544Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf544Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (404226819/404209664) }) = true
      norm_num [leaf544Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf544CertificateValid :
    WideCertificateValid leaf544Box leaf544Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk19ValidityFacts chi76ValidityFacts
    leaf544LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf544CoverageChecked :
    coverageCheck (innerAD leaf544Box) leaf544InnerLog = true := by
  rfl'

private theorem leaf544InnerLogValid :
    leaf544InnerLog.Valid 8 (innerAD leaf544Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint23PositiveFacts.valid leaf544CoverageChecked

private noncomputable def leaf544InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629437/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf544InputLogOnePlusV_eq :
    leaf544InputLogOnePlusV = outerEnclosure 24
      (leaf544Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf544RoundedFacts : LeafRoundedFacts 8
    leaf544Certificate.logOnePlusV leaf544InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf544InputLogOnePlusV_eq }

private noncomputable def leaf544Inputs : Inputs :=
  inputsOfCaches globalInput sk19RoundedInputs
    chi76InputQChi innerPair73Input
    leaf544InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf544LowerChecked :
    lowerCheck 24 leaf544Box leaf544Inputs = true := by
  rfl'

private theorem leaf544CoversExact : CoversExact 8
    leaf544Box leaf544Certificate leaf544InnerLog leaf544Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk19RoundedFacts chi76RoundedFacts
    innerPair73RoundedFacts leaf544RoundedFacts (by rfl)

private theorem leaf544FlatSound : Sound leaf544Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf544CertificateValid
    leaf544InnerLogValid leaf544CoversExact leaf544LowerChecked

private noncomputable def leaf545Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (17/16), chiLo := (13/16), chiHi := (7/8) }

private noncomputable def leaf545Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (16777277/16777216) }, vSqrt := { lower := (65533/65536), upper := (11453093205/11452596224) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (30375045/16777216) }, upper := { exponent := 0, mantissa := (247/128) } }, logOuter := sk18LogOuterCertificate, logK := sk18LogKCertificate, logChi := chi77LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (22905689429/22905192448) } }, logDArg := sk18LogDArgCertificate }

private noncomputable def leaf545InnerLog : WideLogData :=
  innerPair73Data

set_option maxRecDepth 1000000 in
private theorem leaf545LocalValidity :
    LeafFacts leaf545Box leaf545Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf545Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (11453093205/11452596224) }) = true
      norm_num [leaf545Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf545CertificateValid :
    WideCertificateValid leaf545Box leaf545Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk18ValidityFacts chi77ValidityFacts
    leaf545LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf545CoverageChecked :
    coverageCheck (innerAD leaf545Box) leaf545InnerLog = true := by
  rfl'

private theorem leaf545InnerLogValid :
    leaf545InnerLog.Valid 8 (innerAD leaf545Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint23PositiveFacts.valid leaf545CoverageChecked

private noncomputable def leaf545InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629445/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf545InputLogOnePlusV_eq :
    leaf545InputLogOnePlusV = outerEnclosure 24
      (leaf545Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf545RoundedFacts : LeafRoundedFacts 8
    leaf545Certificate.logOnePlusV leaf545InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf545InputLogOnePlusV_eq }

private noncomputable def leaf545Inputs : Inputs :=
  inputsOfCaches globalInput sk18RoundedInputs
    chi77InputQChi innerPair73Input
    leaf545InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf545LowerChecked :
    lowerCheck 24 leaf545Box leaf545Inputs = true := by
  rfl'

private theorem leaf545CoversExact : CoversExact 8
    leaf545Box leaf545Certificate leaf545InnerLog leaf545Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk18RoundedFacts chi77RoundedFacts
    innerPair73RoundedFacts leaf545RoundedFacts (by rfl)

private theorem leaf545FlatSound : Sound leaf545Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf545CertificateValid
    leaf545InnerLogValid leaf545CoversExact leaf545LowerChecked

private noncomputable def leaf546Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/16), kHi := (9/8), chiLo := (13/16), chiHi := (7/8) }

private noncomputable def leaf546Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (16777279/16777216) }, vSqrt := { lower := (65533/65536), upper := (554173473/554156032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (31226959/16777216) }, upper := { exponent := 0, mantissa := (127/64) } }, logOuter := sk19LogOuterCertificate, logK := sk19LogKCertificate, logChi := chi77LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (1108329505/1108312064) } }, logDArg := sk19LogDArgCertificate }

private noncomputable def leaf546InnerLog : WideLogData :=
  innerPair93Data

set_option maxRecDepth 1000000 in
private theorem leaf546LocalValidity :
    LeafFacts leaf546Box leaf546Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf546Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (554173473/554156032) }) = true
      norm_num [leaf546Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf546CertificateValid :
    WideCertificateValid leaf546Box leaf546Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk19ValidityFacts chi77ValidityFacts
    leaf546LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf546CoverageChecked :
    coverageCheck (innerAD leaf546Box) leaf546InnerLog = true := by
  rfl'

private theorem leaf546InnerLogValid :
    leaf546InnerLog.Valid 8 (innerAD leaf546Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint24PositiveFacts.valid leaf546CoverageChecked

private noncomputable def leaf546InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629345/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf546InputLogOnePlusV_eq :
    leaf546InputLogOnePlusV = outerEnclosure 24
      (leaf546Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf546RoundedFacts : LeafRoundedFacts 8
    leaf546Certificate.logOnePlusV leaf546InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf546InputLogOnePlusV_eq }

private noncomputable def leaf546Inputs : Inputs :=
  inputsOfCaches globalInput sk19RoundedInputs
    chi77InputQChi innerPair93Input
    leaf546InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf546LowerChecked :
    lowerCheck 24 leaf546Box leaf546Inputs = true := by
  rfl'

private theorem leaf546CoversExact : CoversExact 8
    leaf546Box leaf546Certificate leaf546InnerLog leaf546Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk19RoundedFacts chi77RoundedFacts
    innerPair93RoundedFacts leaf546RoundedFacts (by rfl)

private theorem leaf546FlatSound : Sound leaf546Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf546CertificateValid
    leaf546InnerLogValid leaf546CoversExact leaf546LowerChecked

private noncomputable def leaf547Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (17/16), chiLo := (7/8), chiHi := (15/16) }

private noncomputable def leaf547Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (16777279/16777216) }, vSqrt := { lower := (65533/65536), upper := (17179377663/17178824704) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (31423555/16777216) }, upper := { exponent := 0, mantissa := (511/256) } }, logOuter := sk18LogOuterCertificate, logK := sk18LogKCertificate, logChi := chi78LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (34358202367/34357649408) } }, logDArg := sk18LogDArgCertificate }

private noncomputable def leaf547InnerLog : WideLogData :=
  innerPair93Data

set_option maxRecDepth 1000000 in
private theorem leaf547LocalValidity :
    LeafFacts leaf547Box leaf547Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf547Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (17179377663/17178824704) }) = true
      norm_num [leaf547Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf547CertificateValid :
    WideCertificateValid leaf547Box leaf547Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk18ValidityFacts chi78ValidityFacts
    leaf547LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf547CoverageChecked :
    coverageCheck (innerAD leaf547Box) leaf547InnerLog = true := by
  rfl'

private theorem leaf547InnerLogValid :
    leaf547InnerLog.Valid 8 (innerAD leaf547Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint24PositiveFacts.valid leaf547CoverageChecked

private noncomputable def leaf547InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629351/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf547InputLogOnePlusV_eq :
    leaf547InputLogOnePlusV = outerEnclosure 24
      (leaf547Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf547RoundedFacts : LeafRoundedFacts 8
    leaf547Certificate.logOnePlusV leaf547InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf547InputLogOnePlusV_eq }

private noncomputable def leaf547Inputs : Inputs :=
  inputsOfCaches globalInput sk18RoundedInputs
    chi78InputQChi innerPair93Input
    leaf547InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf547LowerChecked :
    lowerCheck 24 leaf547Box leaf547Inputs = true := by
  rfl'

private theorem leaf547CoversExact : CoversExact 8
    leaf547Box leaf547Certificate leaf547InnerLog leaf547Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk18RoundedFacts chi78RoundedFacts
    innerPair93RoundedFacts leaf547RoundedFacts (by rfl)

private theorem leaf547FlatSound : Sound leaf547Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf547CertificateValid
    leaf547InnerLogValid leaf547CoversExact leaf547LowerChecked

private noncomputable def leaf548Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/16), kHi := (9/8), chiLo := (7/8), chiHi := (15/16) }

private noncomputable def leaf548Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (16777281/16777216) }, vSqrt := { lower := (65533/65536), upper := (17179377663/17178763264) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (32341001/16777216) }, upper := { exponent := 1, mantissa := (263/256) } }, logOuter := sk19LogOuterCertificate, logK := sk19LogKCertificate, logChi := chi78LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (34358140927/34357526528) } }, logDArg := sk19LogDArgCertificate }

private noncomputable def leaf548InnerLog : WideLogData :=
  innerPair104Data

set_option maxRecDepth 1000000 in
private theorem leaf548LocalValidity :
    LeafFacts leaf548Box leaf548Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf548Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (17179377663/17178763264) }) = true
      norm_num [leaf548Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf548CertificateValid :
    WideCertificateValid leaf548Box leaf548Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk19ValidityFacts chi78ValidityFacts
    leaf548LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf548CoverageChecked :
    coverageCheck (innerAD leaf548Box) leaf548InnerLog = true := by
  rfl'

private theorem leaf548InnerLogValid :
    leaf548InnerLog.Valid 8 (innerAD leaf548Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint72PositiveFacts.valid leaf548CoverageChecked

private noncomputable def leaf548InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629381/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf548InputLogOnePlusV_eq :
    leaf548InputLogOnePlusV = outerEnclosure 24
      (leaf548Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf548RoundedFacts : LeafRoundedFacts 8
    leaf548Certificate.logOnePlusV leaf548InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf548InputLogOnePlusV_eq }

private noncomputable def leaf548Inputs : Inputs :=
  inputsOfCaches globalInput sk19RoundedInputs
    chi78InputQChi innerPair104Input
    leaf548InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf548LowerChecked :
    lowerCheck 24 leaf548Box leaf548Inputs = true := by
  rfl'

private theorem leaf548CoversExact : CoversExact 8
    leaf548Box leaf548Certificate leaf548InnerLog leaf548Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk19RoundedFacts chi78RoundedFacts
    innerPair104RoundedFacts leaf548RoundedFacts (by rfl)

private theorem leaf548FlatSound : Sound leaf548Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf548CertificateValid
    leaf548InnerLogValid leaf548CoversExact leaf548LowerChecked

private noncomputable def leaf549Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (17/16), chiLo := (15/16), chiHi := (1) }

private noncomputable def leaf549Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (16777281/16777216) }, vSqrt := { lower := (65533/65536), upper := (17179377663/17178755072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (32472065/16777216) }, upper := { exponent := 1, mantissa := (33/32) } }, logOuter := sk18LogOuterCertificate, logK := sk18LogKCertificate, logChi := chi79LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (34358132735/34357510144) } }, logDArg := sk18LogDArgCertificate }

private noncomputable def leaf549InnerLog : WideLogData :=
  innerPair104Data

set_option maxRecDepth 1000000 in
private theorem leaf549LocalValidity :
    LeafFacts leaf549Box leaf549Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf549Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (17179377663/17178755072) }) = true
      norm_num [leaf549Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf549CertificateValid :
    WideCertificateValid leaf549Box leaf549Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk18ValidityFacts chi79ValidityFacts
    leaf549LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf549CoverageChecked :
    coverageCheck (innerAD leaf549Box) leaf549InnerLog = true := by
  rfl'

private theorem leaf549InnerLogValid :
    leaf549InnerLog.Valid 8 (innerAD leaf549Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint72PositiveFacts.valid leaf549CoverageChecked

private noncomputable def leaf549InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629385/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf549InputLogOnePlusV_eq :
    leaf549InputLogOnePlusV = outerEnclosure 24
      (leaf549Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf549RoundedFacts : LeafRoundedFacts 8
    leaf549Certificate.logOnePlusV leaf549InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf549InputLogOnePlusV_eq }

private noncomputable def leaf549Inputs : Inputs :=
  inputsOfCaches globalInput sk18RoundedInputs
    chi79InputQChi innerPair104Input
    leaf549InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf549LowerChecked :
    lowerCheck 24 leaf549Box leaf549Inputs = true := by
  rfl'

private theorem leaf549CoversExact : CoversExact 8
    leaf549Box leaf549Certificate leaf549InnerLog leaf549Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk18RoundedFacts chi79RoundedFacts
    innerPair104RoundedFacts leaf549RoundedFacts (by rfl)

private theorem leaf549FlatSound : Sound leaf549Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf549CertificateValid
    leaf549InnerLogValid leaf549CoversExact leaf549LowerChecked

private noncomputable def leaf550Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/16), kHi := (9/8), chiLo := (15/16), chiHi := (1) }

private noncomputable def leaf550Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (16777283/16777216) }, vSqrt := { lower := (65533/65536), upper := (17179377663/17178689536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (33455043/16777216) }, upper := { exponent := 1, mantissa := (17/16) } }, logOuter := sk19LogOuterCertificate, logK := sk19LogKCertificate, logChi := chi79LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (34358067199/34357379072) } }, logDArg := sk19LogDArgCertificate }

private noncomputable def leaf550InnerLog : WideLogData :=
  innerPair111Data

set_option maxRecDepth 1000000 in
private theorem leaf550LocalValidity :
    LeafFacts leaf550Box leaf550Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf550Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (17179377663/17178689536) }) = true
      norm_num [leaf550Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf550CertificateValid :
    WideCertificateValid leaf550Box leaf550Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk19ValidityFacts chi79ValidityFacts
    leaf550LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf550CoverageChecked :
    coverageCheck (innerAD leaf550Box) leaf550InnerLog = true := by
  rfl'

private theorem leaf550InnerLogValid :
    leaf550InnerLog.Valid 8 (innerAD leaf550Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint73PositiveFacts.valid leaf550CoverageChecked

private noncomputable def leaf550InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629417/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf550InputLogOnePlusV_eq :
    leaf550InputLogOnePlusV = outerEnclosure 24
      (leaf550Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf550RoundedFacts : LeafRoundedFacts 8
    leaf550Certificate.logOnePlusV leaf550InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf550InputLogOnePlusV_eq }

private noncomputable def leaf550Inputs : Inputs :=
  inputsOfCaches globalInput sk19RoundedInputs
    chi79InputQChi innerPair111Input
    leaf550InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf550LowerChecked :
    lowerCheck 24 leaf550Box leaf550Inputs = true := by
  rfl'

private theorem leaf550CoversExact : CoversExact 8
    leaf550Box leaf550Certificate leaf550InnerLog leaf550Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk19RoundedFacts chi79RoundedFacts
    innerPair111RoundedFacts leaf550RoundedFacts (by rfl)

private theorem leaf550FlatSound : Sound leaf550Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf550CertificateValid
    leaf550InnerLogValid leaf550CoversExact leaf550LowerChecked

private noncomputable def leaf551Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (19/16), chiLo := (3/4), chiHi := (13/16) }

private noncomputable def leaf551Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (16777279/16777216) }, vSqrt := { lower := (65533/65536), upper := (11453093205/11452571648) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (30899299/16777216) }, upper := { exponent := 0, mantissa := (503/256) } }, logOuter := sk21LogOuterCertificate, logK := sk21LogKCertificate, logChi := chi76LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (22905664853/22905143296) } }, logDArg := sk21LogDArgCertificate }

private noncomputable def leaf551InnerLog : WideLogData :=
  innerPair93Data

set_option maxRecDepth 1000000 in
private theorem leaf551LocalValidity :
    LeafFacts leaf551Box leaf551Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf551Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (11453093205/11452571648) }) = true
      norm_num [leaf551Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf551CertificateValid :
    WideCertificateValid leaf551Box leaf551Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk21ValidityFacts chi76ValidityFacts
    leaf551LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf551CoverageChecked :
    coverageCheck (innerAD leaf551Box) leaf551InnerLog = true := by
  rfl'

private theorem leaf551InnerLogValid :
    leaf551InnerLog.Valid 8 (innerAD leaf551Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint24PositiveFacts.valid leaf551CoverageChecked

private noncomputable def leaf551InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629463/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf551InputLogOnePlusV_eq :
    leaf551InputLogOnePlusV = outerEnclosure 24
      (leaf551Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf551RoundedFacts : LeafRoundedFacts 8
    leaf551Certificate.logOnePlusV leaf551InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf551InputLogOnePlusV_eq }

private noncomputable def leaf551Inputs : Inputs :=
  inputsOfCaches globalInput sk21RoundedInputs
    chi76InputQChi innerPair93Input
    leaf551InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf551LowerChecked :
    lowerCheck 24 leaf551Box leaf551Inputs = true := by
  rfl'

private theorem leaf551CoversExact : CoversExact 8
    leaf551Box leaf551Certificate leaf551InnerLog leaf551Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk21RoundedFacts chi76RoundedFacts
    innerPair93RoundedFacts leaf551RoundedFacts (by rfl)

private theorem leaf551FlatSound : Sound leaf551Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf551CertificateValid
    leaf551InnerLogValid leaf551CoversExact leaf551LowerChecked

private noncomputable def leaf552Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/16), kHi := (5/4), chiLo := (3/4), chiHi := (13/16) }

private noncomputable def leaf552Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (16777281/16777216) }, vSqrt := { lower := (65533/65536), upper := (17179377663/17178804224) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (31685681/16777216) }, upper := { exponent := 1, mantissa := (129/128) } }, logOuter := sk22LogOuterCertificate, logK := sk22LogKCertificate, logChi := chi76LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (34358181887/34357608448) } }, logDArg := sk22LogDArgCertificate }

private noncomputable def leaf552InnerLog : WideLogData :=
  innerPair104Data

set_option maxRecDepth 1000000 in
private theorem leaf552LocalValidity :
    LeafFacts leaf552Box leaf552Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf552Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (17179377663/17178804224) }) = true
      norm_num [leaf552Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf552CertificateValid :
    WideCertificateValid leaf552Box leaf552Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk22ValidityFacts chi76ValidityFacts
    leaf552LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf552CoverageChecked :
    coverageCheck (innerAD leaf552Box) leaf552InnerLog = true := by
  rfl'

private theorem leaf552InnerLogValid :
    leaf552InnerLog.Valid 8 (innerAD leaf552Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint72PositiveFacts.valid leaf552CoverageChecked

private noncomputable def leaf552InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629361/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf552InputLogOnePlusV_eq :
    leaf552InputLogOnePlusV = outerEnclosure 24
      (leaf552Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf552RoundedFacts : LeafRoundedFacts 8
    leaf552Certificate.logOnePlusV leaf552InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf552InputLogOnePlusV_eq }

private noncomputable def leaf552Inputs : Inputs :=
  inputsOfCaches globalInput sk22RoundedInputs
    chi76InputQChi innerPair104Input
    leaf552InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf552LowerChecked :
    lowerCheck 24 leaf552Box leaf552Inputs = true := by
  rfl'

private theorem leaf552CoversExact : CoversExact 8
    leaf552Box leaf552Certificate leaf552InnerLog leaf552Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk22RoundedFacts chi76RoundedFacts
    innerPair104RoundedFacts leaf552RoundedFacts (by rfl)

private theorem leaf552FlatSound : Sound leaf552Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf552CertificateValid
    leaf552InnerLogValid leaf552CoversExact leaf552LowerChecked

private noncomputable def leaf553Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (19/16), chiLo := (13/16), chiHi := (7/8) }

private noncomputable def leaf553Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (16777281/16777216) }, vSqrt := { lower := (65533/65536), upper := (17179377663/17178779648) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (32078873/16777216) }, upper := { exponent := 1, mantissa := (261/256) } }, logOuter := sk21LogOuterCertificate, logK := sk21LogKCertificate, logChi := chi77LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (34358157311/34357559296) } }, logDArg := sk21LogDArgCertificate }

private noncomputable def leaf553InnerLog : WideLogData :=
  innerPair104Data

set_option maxRecDepth 1000000 in
private theorem leaf553LocalValidity :
    LeafFacts leaf553Box leaf553Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf553Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (17179377663/17178779648) }) = true
      norm_num [leaf553Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf553CertificateValid :
    WideCertificateValid leaf553Box leaf553Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk21ValidityFacts chi77ValidityFacts
    leaf553LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf553CoverageChecked :
    coverageCheck (innerAD leaf553Box) leaf553InnerLog = true := by
  rfl'

private theorem leaf553InnerLogValid :
    leaf553InnerLog.Valid 8 (innerAD leaf553Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint72PositiveFacts.valid leaf553CoverageChecked

private noncomputable def leaf553InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629373/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf553InputLogOnePlusV_eq :
    leaf553InputLogOnePlusV = outerEnclosure 24
      (leaf553Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf553RoundedFacts : LeafRoundedFacts 8
    leaf553Certificate.logOnePlusV leaf553InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf553InputLogOnePlusV_eq }

private noncomputable def leaf553Inputs : Inputs :=
  inputsOfCaches globalInput sk21RoundedInputs
    chi77InputQChi innerPair104Input
    leaf553InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf553LowerChecked :
    lowerCheck 24 leaf553Box leaf553Inputs = true := by
  rfl'

private theorem leaf553CoversExact : CoversExact 8
    leaf553Box leaf553Certificate leaf553InnerLog leaf553Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk21RoundedFacts chi77RoundedFacts
    innerPair104RoundedFacts leaf553RoundedFacts (by rfl)

private theorem leaf553FlatSound : Sound leaf553Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf553CertificateValid
    leaf553InnerLogValid leaf553CoversExact leaf553LowerChecked

private noncomputable def leaf554Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/16), kHi := (5/4), chiLo := (13/16), chiHi := (7/8) }

private noncomputable def leaf554Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (16777283/16777216) }, vSqrt := { lower := (65533/65536), upper := (5726459221/5726240768) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (32930787/16777216) }, upper := { exponent := 1, mantissa := (67/64) } }, logOuter := sk22LogOuterCertificate, logK := sk22LogKCertificate, logChi := chi77LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (11452699989/11452481536) } }, logDArg := sk22LogDArgCertificate }

private noncomputable def leaf554InnerLog : WideLogData :=
  innerPair111Data

set_option maxRecDepth 1000000 in
private theorem leaf554LocalValidity :
    LeafFacts leaf554Box leaf554Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf554Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (5726459221/5726240768) }) = true
      norm_num [leaf554Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf554CertificateValid :
    WideCertificateValid leaf554Box leaf554Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk22ValidityFacts chi77ValidityFacts
    leaf554LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf554CoverageChecked :
    coverageCheck (innerAD leaf554Box) leaf554InnerLog = true := by
  rfl'

private theorem leaf554InnerLogValid :
    leaf554InnerLog.Valid 8 (innerAD leaf554Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint73PositiveFacts.valid leaf554CoverageChecked

private noncomputable def leaf554InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629401/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf554InputLogOnePlusV_eq :
    leaf554InputLogOnePlusV = outerEnclosure 24
      (leaf554Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf554RoundedFacts : LeafRoundedFacts 8
    leaf554Certificate.logOnePlusV leaf554InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf554InputLogOnePlusV_eq }

private noncomputable def leaf554Inputs : Inputs :=
  inputsOfCaches globalInput sk22RoundedInputs
    chi77InputQChi innerPair111Input
    leaf554InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf554LowerChecked :
    lowerCheck 24 leaf554Box leaf554Inputs = true := by
  rfl'

private theorem leaf554CoversExact : CoversExact 8
    leaf554Box leaf554Certificate leaf554InnerLog leaf554Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk22RoundedFacts chi77RoundedFacts
    innerPair111RoundedFacts leaf554RoundedFacts (by rfl)

private theorem leaf554FlatSound : Sound leaf554Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf554CertificateValid
    leaf554InnerLogValid leaf554CoversExact leaf554LowerChecked

private noncomputable def leaf555Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (19/16), chiLo := (7/8), chiHi := (15/16) }

private noncomputable def leaf555Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (16777283/16777216) }, vSqrt := { lower := (65533/65536), upper := (17179377663/17178701824) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (33258447/16777216) }, upper := { exponent := 1, mantissa := (541/512) } }, logOuter := sk21LogOuterCertificate, logK := sk21LogKCertificate, logChi := chi78LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (34358079487/34357403648) } }, logDArg := sk21LogDArgCertificate }

private noncomputable def leaf555InnerLog : WideLogData :=
  innerPair111Data

set_option maxRecDepth 1000000 in
private theorem leaf555LocalValidity :
    LeafFacts leaf555Box leaf555Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf555Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (17179377663/17178701824) }) = true
      norm_num [leaf555Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf555CertificateValid :
    WideCertificateValid leaf555Box leaf555Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk21ValidityFacts chi78ValidityFacts
    leaf555LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf555CoverageChecked :
    coverageCheck (innerAD leaf555Box) leaf555InnerLog = true := by
  rfl'

private theorem leaf555InnerLogValid :
    leaf555InnerLog.Valid 8 (innerAD leaf555Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint73PositiveFacts.valid leaf555CoverageChecked

private noncomputable def leaf555InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629411/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf555InputLogOnePlusV_eq :
    leaf555InputLogOnePlusV = outerEnclosure 24
      (leaf555Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf555RoundedFacts : LeafRoundedFacts 8
    leaf555Certificate.logOnePlusV leaf555InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf555InputLogOnePlusV_eq }

private noncomputable def leaf555Inputs : Inputs :=
  inputsOfCaches globalInput sk21RoundedInputs
    chi78InputQChi innerPair111Input
    leaf555InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf555LowerChecked :
    lowerCheck 24 leaf555Box leaf555Inputs = true := by
  rfl'

private theorem leaf555CoversExact : CoversExact 8
    leaf555Box leaf555Certificate leaf555InnerLog leaf555Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk21RoundedFacts chi78RoundedFacts
    innerPair111RoundedFacts leaf555RoundedFacts (by rfl)

private theorem leaf555FlatSound : Sound leaf555Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf555CertificateValid
    leaf555InnerLogValid leaf555CoversExact leaf555LowerChecked

private noncomputable def leaf556Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/16), kHi := (5/4), chiLo := (7/8), chiHi := (15/16) }

private noncomputable def leaf556Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (16777285/16777216) }, vSqrt := { lower := (65533/65536), upper := (17179377663/17178640384) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (34175893/33554432) }, upper := { exponent := 1, mantissa := (139/128) } }, logOuter := sk22LogOuterCertificate, logK := sk22LogKCertificate, logChi := chi78LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (34358018047/34357280768) } }, logDArg := sk22LogDArgCertificate }

private noncomputable def leaf556InnerLog : WideLogData :=
  innerPair118Data

set_option maxRecDepth 1000000 in
private theorem leaf556LocalValidity :
    LeafFacts leaf556Box leaf556Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf556Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (17179377663/17178640384) }) = true
      norm_num [leaf556Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf556CertificateValid :
    WideCertificateValid leaf556Box leaf556Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk22ValidityFacts chi78ValidityFacts
    leaf556LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf556CoverageChecked :
    coverageCheck (innerAD leaf556Box) leaf556InnerLog = true := by
  rfl'

private theorem leaf556InnerLogValid :
    leaf556InnerLog.Valid 8 (innerAD leaf556Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint74PositiveFacts.valid leaf556CoverageChecked

private noncomputable def leaf556InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629441/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf556InputLogOnePlusV_eq :
    leaf556InputLogOnePlusV = outerEnclosure 24
      (leaf556Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf556RoundedFacts : LeafRoundedFacts 8
    leaf556Certificate.logOnePlusV leaf556InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf556InputLogOnePlusV_eq }

private noncomputable def leaf556Inputs : Inputs :=
  inputsOfCaches globalInput sk22RoundedInputs
    chi78InputQChi innerPair118Input
    leaf556InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf556LowerChecked :
    lowerCheck 24 leaf556Box leaf556Inputs = true := by
  rfl'

private theorem leaf556CoversExact : CoversExact 8
    leaf556Box leaf556Certificate leaf556InnerLog leaf556Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk22RoundedFacts chi78RoundedFacts
    innerPair118RoundedFacts leaf556RoundedFacts (by rfl)

private theorem leaf556FlatSound : Sound leaf556Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf556CertificateValid
    leaf556InnerLogValid leaf556CoversExact leaf556LowerChecked

private noncomputable def leaf557Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (19/16), chiLo := (15/16), chiHi := (1) }

private noncomputable def leaf557Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (16777285/16777216) }, vSqrt := { lower := (65533/65536), upper := (5726459221/5726208000) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (34438021/33554432) }, upper := { exponent := 1, mantissa := (35/32) } }, logOuter := sk21LogOuterCertificate, logK := sk21LogKCertificate, logChi := chi79LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (11452667221/11452416000) } }, logDArg := sk21LogDArgCertificate }

private noncomputable def leaf557InnerLog : WideLogData :=
  innerPair118Data

set_option maxRecDepth 1000000 in
private theorem leaf557LocalValidity :
    LeafFacts leaf557Box leaf557Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf557Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (5726459221/5726208000) }) = true
      norm_num [leaf557Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf557CertificateValid :
    WideCertificateValid leaf557Box leaf557Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk21ValidityFacts chi79ValidityFacts
    leaf557LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf557CoverageChecked :
    coverageCheck (innerAD leaf557Box) leaf557InnerLog = true := by
  rfl'

private theorem leaf557InnerLogValid :
    leaf557InnerLog.Valid 8 (innerAD leaf557Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint74PositiveFacts.valid leaf557CoverageChecked

private noncomputable def leaf557InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629449/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf557InputLogOnePlusV_eq :
    leaf557InputLogOnePlusV = outerEnclosure 24
      (leaf557Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf557RoundedFacts : LeafRoundedFacts 8
    leaf557Certificate.logOnePlusV leaf557InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf557InputLogOnePlusV_eq }

private noncomputable def leaf557Inputs : Inputs :=
  inputsOfCaches globalInput sk21RoundedInputs
    chi79InputQChi innerPair118Input
    leaf557InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf557LowerChecked :
    lowerCheck 24 leaf557Box leaf557Inputs = true := by
  rfl'

private theorem leaf557CoversExact : CoversExact 8
    leaf557Box leaf557Certificate leaf557InnerLog leaf557Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk21RoundedFacts chi79RoundedFacts
    innerPair118RoundedFacts leaf557RoundedFacts (by rfl)

private theorem leaf557FlatSound : Sound leaf557Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf557CertificateValid
    leaf557InnerLogValid leaf557CoversExact leaf557LowerChecked

private noncomputable def leaf558Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/16), kHi := (5/4), chiLo := (15/16), chiHi := (1) }

private noncomputable def leaf558Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (16777287/16777216) }, vSqrt := { lower := (65533/65536), upper := (17179377663/17178558464) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (35420999/33554432) }, upper := { exponent := 1, mantissa := (9/8) } }, logOuter := sk22LogOuterCertificate, logK := sk22LogKCertificate, logChi := chi79LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (34357936127/34357116928) } }, logDArg := sk22LogDArgCertificate }

private noncomputable def leaf558InnerLog : WideLogData :=
  innerPair244Data

set_option maxRecDepth 1000000 in
private theorem leaf558LocalValidity :
    LeafFacts leaf558Box leaf558Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf558Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (17179377663/17178558464) }) = true
      norm_num [leaf558Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf558CertificateValid :
    WideCertificateValid leaf558Box leaf558Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk22ValidityFacts chi79ValidityFacts
    leaf558LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf558CoverageChecked :
    coverageCheck (innerAD leaf558Box) leaf558InnerLog = true := by
  rfl'

private theorem leaf558InnerLogValid :
    leaf558InnerLog.Valid 8 (innerAD leaf558Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint75PositiveFacts.valid leaf558CoverageChecked

private noncomputable def leaf558InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629481/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf558InputLogOnePlusV_eq :
    leaf558InputLogOnePlusV = outerEnclosure 24
      (leaf558Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf558RoundedFacts : LeafRoundedFacts 8
    leaf558Certificate.logOnePlusV leaf558InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf558InputLogOnePlusV_eq }

private noncomputable def leaf558Inputs : Inputs :=
  inputsOfCaches globalInput sk22RoundedInputs
    chi79InputQChi innerPair244Input
    leaf558InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf558LowerChecked :
    lowerCheck 24 leaf558Box leaf558Inputs = true := by
  rfl'

private theorem leaf558CoversExact : CoversExact 8
    leaf558Box leaf558Certificate leaf558InnerLog leaf558Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk22RoundedFacts chi79RoundedFacts
    innerPair244RoundedFacts leaf558RoundedFacts (by rfl)

private theorem leaf558FlatSound : Sound leaf558Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf558CertificateValid
    leaf558InnerLogValid leaf558CoversExact leaf558LowerChecked

private noncomputable def leaf559Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (21/16), chiLo := (3/4), chiHi := (13/16) }

private noncomputable def leaf559Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (16777283/16777216) }, vSqrt := { lower := (65533/65536), upper := (17179377663/17178750976) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (32472063/16777216) }, upper := { exponent := 1, mantissa := (529/512) } }, logOuter := sk25LogOuterCertificate, logK := sk25LogKCertificate, logChi := chi76LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (34358128639/34357501952) } }, logDArg := sk25LogDArgCertificate }

private noncomputable def leaf559InnerLog : WideLogData :=
  innerPair105Data

set_option maxRecDepth 1000000 in
private theorem leaf559LocalValidity :
    LeafFacts leaf559Box leaf559Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf559Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (17179377663/17178750976) }) = true
      norm_num [leaf559Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf559CertificateValid :
    WideCertificateValid leaf559Box leaf559Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk25ValidityFacts chi76ValidityFacts
    leaf559LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf559CoverageChecked :
    coverageCheck (innerAD leaf559Box) leaf559InnerLog = true := by
  rfl'

private theorem leaf559InnerLogValid :
    leaf559InnerLog.Valid 8 (innerAD leaf559Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint73PositiveFacts.valid leaf559CoverageChecked

private noncomputable def leaf559InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629387/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf559InputLogOnePlusV_eq :
    leaf559InputLogOnePlusV = outerEnclosure 24
      (leaf559Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf559RoundedFacts : LeafRoundedFacts 8
    leaf559Certificate.logOnePlusV leaf559InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf559InputLogOnePlusV_eq }

private noncomputable def leaf559Inputs : Inputs :=
  inputsOfCaches globalInput sk25RoundedInputs
    chi76InputQChi innerPair105Input
    leaf559InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf559LowerChecked :
    lowerCheck 24 leaf559Box leaf559Inputs = true := by
  rfl'

private theorem leaf559CoversExact : CoversExact 8
    leaf559Box leaf559Certificate leaf559InnerLog leaf559Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk25RoundedFacts chi76RoundedFacts
    innerPair105RoundedFacts leaf559RoundedFacts (by rfl)

private theorem leaf559FlatSound : Sound leaf559Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf559CertificateValid
    leaf559InnerLogValid leaf559CoversExact leaf559LowerChecked

private noncomputable def leaf560Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/16), kHi := (11/8), chiLo := (3/4), chiHi := (13/16) }

private noncomputable def leaf560Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (16777285/16777216) }, vSqrt := { lower := (65533/65536), upper := (5726459221/5726232576) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (33258445/16777216) }, upper := { exponent := 1, mantissa := (271/256) } }, logOuter := sk26LogOuterCertificate, logK := sk26LogKCertificate, logChi := chi76LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (11452691797/11452465152) } }, logDArg := sk26LogDArgCertificate }

private noncomputable def leaf560InnerLog : WideLogData :=
  innerPair111Data

set_option maxRecDepth 1000000 in
private theorem leaf560LocalValidity :
    LeafFacts leaf560Box leaf560Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf560Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (5726459221/5726232576) }) = true
      norm_num [leaf560Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf560CertificateValid :
    WideCertificateValid leaf560Box leaf560Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk26ValidityFacts chi76ValidityFacts
    leaf560LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf560CoverageChecked :
    coverageCheck (innerAD leaf560Box) leaf560InnerLog = true := by
  rfl'

private theorem leaf560InnerLogValid :
    leaf560InnerLog.Valid 8 (innerAD leaf560Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint73PositiveFacts.valid leaf560CoverageChecked

private noncomputable def leaf560InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629413/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf560InputLogOnePlusV_eq :
    leaf560InputLogOnePlusV = outerEnclosure 24
      (leaf560Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf560RoundedFacts : LeafRoundedFacts 8
    leaf560Certificate.logOnePlusV leaf560InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf560InputLogOnePlusV_eq }

private noncomputable def leaf560Inputs : Inputs :=
  inputsOfCaches globalInput sk26RoundedInputs
    chi76InputQChi innerPair111Input
    leaf560InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf560LowerChecked :
    lowerCheck 24 leaf560Box leaf560Inputs = true := by
  rfl'

private theorem leaf560CoversExact : CoversExact 8
    leaf560Box leaf560Certificate leaf560InnerLog leaf560Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk26RoundedFacts chi76RoundedFacts
    innerPair111RoundedFacts leaf560RoundedFacts (by rfl)

private theorem leaf560FlatSound : Sound leaf560Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf560CertificateValid
    leaf560InnerLogValid leaf560CoversExact leaf560LowerChecked

private noncomputable def leaf561Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (21/16), chiLo := (13/16), chiHi := (7/8) }

private noncomputable def leaf561Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (16777285/16777216) }, vSqrt := { lower := (65533/65536), upper := (17179377663/17178664960) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (33782701/33554432) }, upper := { exponent := 1, mantissa := (275/256) } }, logOuter := sk25LogOuterCertificate, logK := sk25LogKCertificate, logChi := chi77LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (34358042623/34357329920) } }, logDArg := sk25LogDArgCertificate }

private noncomputable def leaf561InnerLog : WideLogData :=
  innerPair118Data

set_option maxRecDepth 1000000 in
private theorem leaf561LocalValidity :
    LeafFacts leaf561Box leaf561Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf561Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (17179377663/17178664960) }) = true
      norm_num [leaf561Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf561CertificateValid :
    WideCertificateValid leaf561Box leaf561Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk25ValidityFacts chi77ValidityFacts
    leaf561LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf561CoverageChecked :
    coverageCheck (innerAD leaf561Box) leaf561InnerLog = true := by
  rfl'

private theorem leaf561InnerLogValid :
    leaf561InnerLog.Valid 8 (innerAD leaf561Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint74PositiveFacts.valid leaf561CoverageChecked

private noncomputable def leaf561InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629429/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf561InputLogOnePlusV_eq :
    leaf561InputLogOnePlusV = outerEnclosure 24
      (leaf561Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf561RoundedFacts : LeafRoundedFacts 8
    leaf561Certificate.logOnePlusV leaf561InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf561InputLogOnePlusV_eq }

private noncomputable def leaf561Inputs : Inputs :=
  inputsOfCaches globalInput sk25RoundedInputs
    chi77InputQChi innerPair118Input
    leaf561InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf561LowerChecked :
    lowerCheck 24 leaf561Box leaf561Inputs = true := by
  rfl'

private theorem leaf561CoversExact : CoversExact 8
    leaf561Box leaf561Certificate leaf561InnerLog leaf561Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk25RoundedFacts chi77RoundedFacts
    innerPair118RoundedFacts leaf561RoundedFacts (by rfl)

private theorem leaf561FlatSound : Sound leaf561Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf561CertificateValid
    leaf561InnerLogValid leaf561CoversExact leaf561LowerChecked

private noncomputable def leaf562Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/16), kHi := (11/8), chiLo := (13/16), chiHi := (7/8) }

private noncomputable def leaf562Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (16777287/16777216) }, vSqrt := { lower := (65533/65536), upper := (17179377663/17178607616) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (34634615/33554432) }, upper := { exponent := 1, mantissa := (141/128) } }, logOuter := sk26LogOuterCertificate, logK := sk26LogKCertificate, logChi := chi77LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (34357985279/34357215232) } }, logDArg := sk26LogDArgCertificate }

private noncomputable def leaf562InnerLog : WideLogData :=
  innerPair244Data

set_option maxRecDepth 1000000 in
private theorem leaf562LocalValidity :
    LeafFacts leaf562Box leaf562Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf562Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (17179377663/17178607616) }) = true
      norm_num [leaf562Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf562CertificateValid :
    WideCertificateValid leaf562Box leaf562Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk26ValidityFacts chi77ValidityFacts
    leaf562LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf562CoverageChecked :
    coverageCheck (innerAD leaf562Box) leaf562InnerLog = true := by
  rfl'

private theorem leaf562InnerLogValid :
    leaf562InnerLog.Valid 8 (innerAD leaf562Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint75PositiveFacts.valid leaf562CoverageChecked

private noncomputable def leaf562InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629457/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf562InputLogOnePlusV_eq :
    leaf562InputLogOnePlusV = outerEnclosure 24
      (leaf562Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf562RoundedFacts : LeafRoundedFacts 8
    leaf562Certificate.logOnePlusV leaf562InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf562InputLogOnePlusV_eq }

private noncomputable def leaf562Inputs : Inputs :=
  inputsOfCaches globalInput sk26RoundedInputs
    chi77InputQChi innerPair244Input
    leaf562InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf562LowerChecked :
    lowerCheck 24 leaf562Box leaf562Inputs = true := by
  rfl'

private theorem leaf562CoversExact : CoversExact 8
    leaf562Box leaf562Certificate leaf562InnerLog leaf562Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk26RoundedFacts chi77RoundedFacts
    innerPair244RoundedFacts leaf562RoundedFacts (by rfl)

private theorem leaf562FlatSound : Sound leaf562Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf562CertificateValid
    leaf562InnerLogValid leaf562CoversExact leaf562LowerChecked

private noncomputable def leaf563Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (23/16), chiLo := (3/4), chiHi := (13/16) }

private noncomputable def leaf563Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (16777287/16777216) }, vSqrt := { lower := (16383/16384), upper := (17179377663/17178644480) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (34044827/33554432) }, upper := { exponent := 1, mantissa := (555/512) } }, logOuter := sk27LogOuterCertificate, logK := sk27LogKCertificate, logChi := chi76LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (34358022143/34357288960) } }, logDArg := sk27LogDArgCertificate }

private noncomputable def leaf563InnerLog : WideLogData :=
  innerPair118Data

set_option maxRecDepth 1000000 in
private theorem leaf563LocalValidity :
    LeafFacts leaf563Box leaf563Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf563Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (17179377663/17178644480) }) = true
      norm_num [leaf563Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf563CertificateValid :
    WideCertificateValid leaf563Box leaf563Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk27ValidityFacts chi76ValidityFacts
    leaf563LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf563CoverageChecked :
    coverageCheck (innerAD leaf563Box) leaf563InnerLog = true := by
  rfl'

private theorem leaf563InnerLogValid :
    leaf563InnerLog.Valid 8 (innerAD leaf563Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint74PositiveFacts.valid leaf563CoverageChecked

private noncomputable def leaf563InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629439/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf563InputLogOnePlusV_eq :
    leaf563InputLogOnePlusV = outerEnclosure 24
      (leaf563Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf563RoundedFacts : LeafRoundedFacts 8
    leaf563Certificate.logOnePlusV leaf563InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf563InputLogOnePlusV_eq }

private noncomputable def leaf563Inputs : Inputs :=
  inputsOfCaches globalInput sk27RoundedInputs
    chi76InputQChi innerPair118Input
    leaf563InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf563LowerChecked :
    lowerCheck 24 leaf563Box leaf563Inputs = true := by
  rfl'

private theorem leaf563CoversExact : CoversExact 8
    leaf563Box leaf563Certificate leaf563InnerLog leaf563Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk27RoundedFacts chi76RoundedFacts
    innerPair118RoundedFacts leaf563RoundedFacts (by rfl)

private theorem leaf563FlatSound : Sound leaf563Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf563CertificateValid
    leaf563InnerLogValid leaf563CoversExact leaf563LowerChecked

private noncomputable def leaf564Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/16), kHi := (3/2), chiLo := (3/4), chiHi := (13/16) }

private noncomputable def leaf564Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (16777289/16777216) }, vSqrt := { lower := (16383/16384), upper := (17179377663/17178591232) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (34831209/33554432) }, upper := { exponent := 1, mantissa := (71/64) } }, logOuter := sk28LogOuterCertificate, logK := sk28LogKCertificate, logChi := chi76LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (34357968895/34357182464) } }, logDArg := sk28LogDArgCertificate }

private noncomputable def leaf564InnerLog : WideLogData :=
  innerPair244Data

set_option maxRecDepth 1000000 in
private theorem leaf564LocalValidity :
    LeafFacts leaf564Box leaf564Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf564Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (17179377663/17178591232) }) = true
      norm_num [leaf564Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf564CertificateValid :
    WideCertificateValid leaf564Box leaf564Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk28ValidityFacts chi76ValidityFacts
    leaf564LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf564CoverageChecked :
    coverageCheck (innerAD leaf564Box) leaf564InnerLog = true := by
  rfl'

private theorem leaf564InnerLogValid :
    leaf564InnerLog.Valid 8 (innerAD leaf564Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint75PositiveFacts.valid leaf564CoverageChecked

private noncomputable def leaf564InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629465/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf564InputLogOnePlusV_eq :
    leaf564InputLogOnePlusV = outerEnclosure 24
      (leaf564Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf564RoundedFacts : LeafRoundedFacts 8
    leaf564Certificate.logOnePlusV leaf564InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf564InputLogOnePlusV_eq }

private noncomputable def leaf564Inputs : Inputs :=
  inputsOfCaches globalInput sk28RoundedInputs
    chi76InputQChi innerPair244Input
    leaf564InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf564LowerChecked :
    lowerCheck 24 leaf564Box leaf564Inputs = true := by
  rfl'

private theorem leaf564CoversExact : CoversExact 8
    leaf564Box leaf564Certificate leaf564InnerLog leaf564Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk28RoundedFacts chi76RoundedFacts
    innerPair244RoundedFacts leaf564RoundedFacts (by rfl)

private theorem leaf564FlatSound : Sound leaf564Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf564CertificateValid
    leaf564InnerLogValid leaf564CoversExact leaf564LowerChecked

private noncomputable def leaf565Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (23/16), chiLo := (13/16), chiHi := (7/8) }

private noncomputable def leaf565Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (16777289/16777216) }, vSqrt := { lower := (16383/16384), upper := (5726459221/5726183424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (35486529/33554432) }, upper := { exponent := 1, mantissa := (289/256) } }, logOuter := sk27LogOuterCertificate, logK := sk27LogKCertificate, logChi := chi77LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (11452642645/11452366848) } }, logDArg := sk27LogDArgCertificate }

private noncomputable def leaf565InnerLog : WideLogData :=
  innerPair245Data

set_option maxRecDepth 1000000 in
private theorem leaf565LocalValidity :
    LeafFacts leaf565Box leaf565Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf565Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (5726459221/5726183424) }) = true
      norm_num [leaf565Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf565CertificateValid :
    WideCertificateValid leaf565Box leaf565Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk27ValidityFacts chi77ValidityFacts
    leaf565LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf565CoverageChecked :
    coverageCheck (innerAD leaf565Box) leaf565InnerLog = true := by
  rfl'

private theorem leaf565InnerLogValid :
    leaf565InnerLog.Valid 8 (innerAD leaf565Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint76PositiveFacts.valid leaf565CoverageChecked

private noncomputable def leaf565InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629485/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf565InputLogOnePlusV_eq :
    leaf565InputLogOnePlusV = outerEnclosure 24
      (leaf565Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf565RoundedFacts : LeafRoundedFacts 8
    leaf565Certificate.logOnePlusV leaf565InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf565InputLogOnePlusV_eq }

private noncomputable def leaf565Inputs : Inputs :=
  inputsOfCaches globalInput sk27RoundedInputs
    chi77InputQChi innerPair245Input
    leaf565InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf565LowerChecked :
    lowerCheck 24 leaf565Box leaf565Inputs = true := by
  rfl'

private theorem leaf565CoversExact : CoversExact 8
    leaf565Box leaf565Certificate leaf565InnerLog leaf565Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk27RoundedFacts chi77RoundedFacts
    innerPair245RoundedFacts leaf565RoundedFacts (by rfl)

private theorem leaf565FlatSound : Sound leaf565Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf565CertificateValid
    leaf565InnerLogValid leaf565CoversExact leaf565LowerChecked

private noncomputable def leaf566Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/16), kHi := (3/2), chiLo := (13/16), chiHi := (7/8) }

private noncomputable def leaf566Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (16777291/16777216) }, vSqrt := { lower := (16383/16384), upper := (17179377663/17178492928) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (36338443/33554432) }, upper := { exponent := 1, mantissa := (37/32) } }, logOuter := sk28LogOuterCertificate, logK := sk28LogKCertificate, logChi := chi77LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (34357870591/34356985856) } }, logDArg := sk28LogDArgCertificate }

private noncomputable def leaf566InnerLog : WideLogData :=
  innerPair251Data

set_option maxRecDepth 1000000 in
private theorem leaf566LocalValidity :
    LeafFacts leaf566Box leaf566Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf566Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (17179377663/17178492928) }) = true
      norm_num [leaf566Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf566CertificateValid :
    WideCertificateValid leaf566Box leaf566Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk28ValidityFacts chi77ValidityFacts
    leaf566LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf566CoverageChecked :
    coverageCheck (innerAD leaf566Box) leaf566InnerLog = true := by
  rfl'

private theorem leaf566InnerLogValid :
    leaf566InnerLog.Valid 8 (innerAD leaf566Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint76PositiveFacts.valid leaf566CoverageChecked

private noncomputable def leaf566InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629513/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf566InputLogOnePlusV_eq :
    leaf566InputLogOnePlusV = outerEnclosure 24
      (leaf566Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf566RoundedFacts : LeafRoundedFacts 8
    leaf566Certificate.logOnePlusV leaf566InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf566InputLogOnePlusV_eq }

private noncomputable def leaf566Inputs : Inputs :=
  inputsOfCaches globalInput sk28RoundedInputs
    chi77InputQChi innerPair251Input
    leaf566InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf566LowerChecked :
    lowerCheck 24 leaf566Box leaf566Inputs = true := by
  rfl'

private theorem leaf566CoversExact : CoversExact 8
    leaf566Box leaf566Certificate leaf566InnerLog leaf566Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk28RoundedFacts chi77RoundedFacts
    innerPair251RoundedFacts leaf566RoundedFacts (by rfl)

private theorem leaf566FlatSound : Sound leaf566Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf566CertificateValid
    leaf566InnerLogValid leaf566CoversExact leaf566LowerChecked

private noncomputable def leaf567Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (21/16), chiLo := (7/8), chiHi := (15/16) }

private noncomputable def leaf567Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (16777287/16777216) }, vSqrt := { lower := (65533/65536), upper := (17179377663/17178578944) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (35093339/33554432) }, upper := { exponent := 1, mantissa := (571/512) } }, logOuter := sk25LogOuterCertificate, logK := sk25LogKCertificate, logChi := chi78LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (34357956607/34357157888) } }, logDArg := sk25LogDArgCertificate }

private noncomputable def leaf567InnerLog : WideLogData :=
  innerPair244Data

set_option maxRecDepth 1000000 in
private theorem leaf567LocalValidity :
    LeafFacts leaf567Box leaf567Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf567Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (17179377663/17178578944) }) = true
      norm_num [leaf567Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf567CertificateValid :
    WideCertificateValid leaf567Box leaf567Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk25ValidityFacts chi78ValidityFacts
    leaf567LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf567CoverageChecked :
    coverageCheck (innerAD leaf567Box) leaf567InnerLog = true := by
  rfl'

private theorem leaf567InnerLogValid :
    leaf567InnerLog.Valid 8 (innerAD leaf567Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint75PositiveFacts.valid leaf567CoverageChecked

private noncomputable def leaf567InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629471/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf567InputLogOnePlusV_eq :
    leaf567InputLogOnePlusV = outerEnclosure 24
      (leaf567Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf567RoundedFacts : LeafRoundedFacts 8
    leaf567Certificate.logOnePlusV leaf567InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf567InputLogOnePlusV_eq }

private noncomputable def leaf567Inputs : Inputs :=
  inputsOfCaches globalInput sk25RoundedInputs
    chi78InputQChi innerPair244Input
    leaf567InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf567LowerChecked :
    lowerCheck 24 leaf567Box leaf567Inputs = true := by
  rfl'

private theorem leaf567CoversExact : CoversExact 8
    leaf567Box leaf567Certificate leaf567InnerLog leaf567Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk25RoundedFacts chi78RoundedFacts
    innerPair244RoundedFacts leaf567RoundedFacts (by rfl)

private theorem leaf567FlatSound : Sound leaf567Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf567CertificateValid
    leaf567InnerLogValid leaf567CoversExact leaf567LowerChecked

private noncomputable def leaf568Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/16), kHi := (11/8), chiLo := (7/8), chiHi := (15/16) }

private noncomputable def leaf568Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (16777289/16777216) }, vSqrt := { lower := (65533/65536), upper := (17179377663/17178517504) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (36010785/33554432) }, upper := { exponent := 1, mantissa := (293/256) } }, logOuter := sk26LogOuterCertificate, logK := sk26LogKCertificate, logChi := chi78LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (34357895167/34357035008) } }, logDArg := sk26LogDArgCertificate }

private noncomputable def leaf568InnerLog : WideLogData :=
  innerPair251Data

set_option maxRecDepth 1000000 in
private theorem leaf568LocalValidity :
    LeafFacts leaf568Box leaf568Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf568Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (17179377663/17178517504) }) = true
      norm_num [leaf568Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf568CertificateValid :
    WideCertificateValid leaf568Box leaf568Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk26ValidityFacts chi78ValidityFacts
    leaf568LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf568CoverageChecked :
    coverageCheck (innerAD leaf568Box) leaf568InnerLog = true := by
  rfl'

private theorem leaf568InnerLogValid :
    leaf568InnerLog.Valid 8 (innerAD leaf568Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint76PositiveFacts.valid leaf568CoverageChecked

private noncomputable def leaf568InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629501/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf568InputLogOnePlusV_eq :
    leaf568InputLogOnePlusV = outerEnclosure 24
      (leaf568Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf568RoundedFacts : LeafRoundedFacts 8
    leaf568Certificate.logOnePlusV leaf568InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf568InputLogOnePlusV_eq }

private noncomputable def leaf568Inputs : Inputs :=
  inputsOfCaches globalInput sk26RoundedInputs
    chi78InputQChi innerPair251Input
    leaf568InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf568LowerChecked :
    lowerCheck 24 leaf568Box leaf568Inputs = true := by
  rfl'

private theorem leaf568CoversExact : CoversExact 8
    leaf568Box leaf568Certificate leaf568InnerLog leaf568Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk26RoundedFacts chi78RoundedFacts
    innerPair251RoundedFacts leaf568RoundedFacts (by rfl)

private theorem leaf568FlatSound : Sound leaf568Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf568CertificateValid
    leaf568InnerLogValid leaf568CoversExact leaf568LowerChecked

private noncomputable def leaf569Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (21/16), chiLo := (15/16), chiHi := (1) }

private noncomputable def leaf569Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (16777289/16777216) }, vSqrt := { lower := (65533/65536), upper := (17179377663/17178492928) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (36403977/33554432) }, upper := { exponent := 1, mantissa := (37/32) } }, logOuter := sk25LogOuterCertificate, logK := sk25LogKCertificate, logChi := chi79LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (34357870591/34356985856) } }, logDArg := sk25LogDArgCertificate }

private noncomputable def leaf569InnerLog : WideLogData :=
  innerPair251Data

set_option maxRecDepth 1000000 in
private theorem leaf569LocalValidity :
    LeafFacts leaf569Box leaf569Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf569Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (17179377663/17178492928) }) = true
      norm_num [leaf569Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf569CertificateValid :
    WideCertificateValid leaf569Box leaf569Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk25ValidityFacts chi79ValidityFacts
    leaf569LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf569CoverageChecked :
    coverageCheck (innerAD leaf569Box) leaf569InnerLog = true := by
  rfl'

private theorem leaf569InnerLogValid :
    leaf569InnerLog.Valid 8 (innerAD leaf569Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint76PositiveFacts.valid leaf569CoverageChecked

private noncomputable def leaf569InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629513/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf569InputLogOnePlusV_eq :
    leaf569InputLogOnePlusV = outerEnclosure 24
      (leaf569Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf569RoundedFacts : LeafRoundedFacts 8
    leaf569Certificate.logOnePlusV leaf569InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf569InputLogOnePlusV_eq }

private noncomputable def leaf569Inputs : Inputs :=
  inputsOfCaches globalInput sk25RoundedInputs
    chi79InputQChi innerPair251Input
    leaf569InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf569LowerChecked :
    lowerCheck 24 leaf569Box leaf569Inputs = true := by
  rfl'

private theorem leaf569CoversExact : CoversExact 8
    leaf569Box leaf569Certificate leaf569InnerLog leaf569Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk25RoundedFacts chi79RoundedFacts
    innerPair251RoundedFacts leaf569RoundedFacts (by rfl)

private theorem leaf569FlatSound : Sound leaf569Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf569CertificateValid
    leaf569InnerLogValid leaf569CoversExact leaf569LowerChecked

private noncomputable def leaf570Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/16), kHi := (11/8), chiLo := (15/16), chiHi := (1) }

private noncomputable def leaf570Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (16777291/16777216) }, vSqrt := { lower := (65533/65536), upper := (818065603/818020352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (37386955/33554432) }, upper := { exponent := 1, mantissa := (19/16) } }, logOuter := sk26LogOuterCertificate, logK := sk26LogKCertificate, logChi := chi79LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (1636085955/1636040704) } }, logDArg := sk26LogDArgCertificate }

private noncomputable def leaf570InnerLog : WideLogData :=
  innerPair258Data

set_option maxRecDepth 1000000 in
private theorem leaf570LocalValidity :
    LeafFacts leaf570Box leaf570Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf570Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (818065603/818020352) }) = true
      norm_num [leaf570Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf570CertificateValid :
    WideCertificateValid leaf570Box leaf570Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk26ValidityFacts chi79ValidityFacts
    leaf570LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf570CoverageChecked :
    coverageCheck (innerAD leaf570Box) leaf570InnerLog = true := by
  rfl'

private theorem leaf570InnerLogValid :
    leaf570InnerLog.Valid 8 (innerAD leaf570Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint77PositiveFacts.valid leaf570CoverageChecked

private noncomputable def leaf570InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629545/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf570InputLogOnePlusV_eq :
    leaf570InputLogOnePlusV = outerEnclosure 24
      (leaf570Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf570RoundedFacts : LeafRoundedFacts 8
    leaf570Certificate.logOnePlusV leaf570InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf570InputLogOnePlusV_eq }

private noncomputable def leaf570Inputs : Inputs :=
  inputsOfCaches globalInput sk26RoundedInputs
    chi79InputQChi innerPair258Input
    leaf570InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf570LowerChecked :
    lowerCheck 24 leaf570Box leaf570Inputs = true := by
  rfl'

private theorem leaf570CoversExact : CoversExact 8
    leaf570Box leaf570Certificate leaf570InnerLog leaf570Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk26RoundedFacts chi79RoundedFacts
    innerPair258RoundedFacts leaf570RoundedFacts (by rfl)

private theorem leaf570FlatSound : Sound leaf570Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf570CertificateValid
    leaf570InnerLogValid leaf570CoversExact leaf570LowerChecked

private noncomputable def leaf571Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (23/16), chiLo := (7/8), chiHi := (15/16) }

private noncomputable def leaf571Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (16777291/16777216) }, vSqrt := { lower := (16383/16384), upper := (79167639/79163392) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (36928231/33554432) }, upper := { exponent := 1, mantissa := (601/512) } }, logOuter := sk27LogOuterCertificate, logK := sk27LogKCertificate, logChi := chi78LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (158331031/158326784) } }, logDArg := sk27LogDArgCertificate }

private noncomputable def leaf571InnerLog : WideLogData :=
  innerPair258Data

set_option maxRecDepth 1000000 in
private theorem leaf571LocalValidity :
    LeafFacts leaf571Box leaf571Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf571Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (79167639/79163392) }) = true
      norm_num [leaf571Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf571CertificateValid :
    WideCertificateValid leaf571Box leaf571Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk27ValidityFacts chi78ValidityFacts
    leaf571LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf571CoverageChecked :
    coverageCheck (innerAD leaf571Box) leaf571InnerLog = true := by
  rfl'

private theorem leaf571InnerLogValid :
    leaf571InnerLog.Valid 8 (innerAD leaf571Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint77PositiveFacts.valid leaf571CoverageChecked

private noncomputable def leaf571InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629531/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf571InputLogOnePlusV_eq :
    leaf571InputLogOnePlusV = outerEnclosure 24
      (leaf571Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf571RoundedFacts : LeafRoundedFacts 8
    leaf571Certificate.logOnePlusV leaf571InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf571InputLogOnePlusV_eq }

private noncomputable def leaf571Inputs : Inputs :=
  inputsOfCaches globalInput sk27RoundedInputs
    chi78InputQChi innerPair258Input
    leaf571InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf571LowerChecked :
    lowerCheck 24 leaf571Box leaf571Inputs = true := by
  rfl'

private theorem leaf571CoversExact : CoversExact 8
    leaf571Box leaf571Certificate leaf571InnerLog leaf571Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk27RoundedFacts chi78RoundedFacts
    innerPair258RoundedFacts leaf571RoundedFacts (by rfl)

private theorem leaf571FlatSound : Sound leaf571Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf571CertificateValid
    leaf571InnerLogValid leaf571CoversExact leaf571LowerChecked

private noncomputable def leaf572Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/16), kHi := (3/2), chiLo := (7/8), chiHi := (15/16) }

private noncomputable def leaf572Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (16777293/16777216) }, vSqrt := { lower := (16383/16384), upper := (17179377663/17178394624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (37845677/33554432) }, upper := { exponent := 1, mantissa := (77/64) } }, logOuter := sk28LogOuterCertificate, logK := sk28LogKCertificate, logChi := chi78LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (34357772287/34356789248) } }, logDArg := sk28LogDArgCertificate }

private noncomputable def leaf572InnerLog : WideLogData :=
  innerPair266Data

set_option maxRecDepth 1000000 in
private theorem leaf572LocalValidity :
    LeafFacts leaf572Box leaf572Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf572Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (17179377663/17178394624) }) = true
      norm_num [leaf572Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf572CertificateValid :
    WideCertificateValid leaf572Box leaf572Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk28ValidityFacts chi78ValidityFacts
    leaf572LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf572CoverageChecked :
    coverageCheck (innerAD leaf572Box) leaf572InnerLog = true := by
  rfl'

private theorem leaf572InnerLogValid :
    leaf572InnerLog.Valid 8 (innerAD leaf572Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint78PositiveFacts.valid leaf572CoverageChecked

private noncomputable def leaf572InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629561/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf572InputLogOnePlusV_eq :
    leaf572InputLogOnePlusV = outerEnclosure 24
      (leaf572Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf572RoundedFacts : LeafRoundedFacts 8
    leaf572Certificate.logOnePlusV leaf572InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf572InputLogOnePlusV_eq }

private noncomputable def leaf572Inputs : Inputs :=
  inputsOfCaches globalInput sk28RoundedInputs
    chi78InputQChi innerPair266Input
    leaf572InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf572LowerChecked :
    lowerCheck 24 leaf572Box leaf572Inputs = true := by
  rfl'

private theorem leaf572CoversExact : CoversExact 8
    leaf572Box leaf572Certificate leaf572InnerLog leaf572Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk28RoundedFacts chi78RoundedFacts
    innerPair266RoundedFacts leaf572RoundedFacts (by rfl)

private theorem leaf572FlatSound : Sound leaf572Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf572CertificateValid
    leaf572InnerLogValid leaf572CoversExact leaf572LowerChecked

private noncomputable def leaf573Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (23/16), chiLo := (15/16), chiHi := (1) }

private noncomputable def leaf573Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (16777293/16777216) }, vSqrt := { lower := (16383/16384), upper := (17179377663/17178361856) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (38369933/33554432) }, upper := { exponent := 1, mantissa := (39/32) } }, logOuter := sk27LogOuterCertificate, logK := sk27LogKCertificate, logChi := chi79LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (34357739519/34356723712) } }, logDArg := sk27LogDArgCertificate }

private noncomputable def leaf573InnerLog : WideLogData :=
  innerPair266Data

set_option maxRecDepth 1000000 in
private theorem leaf573LocalValidity :
    LeafFacts leaf573Box leaf573Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf573Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (17179377663/17178361856) }) = true
      norm_num [leaf573Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf573CertificateValid :
    WideCertificateValid leaf573Box leaf573Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk27ValidityFacts chi79ValidityFacts
    leaf573LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf573CoverageChecked :
    coverageCheck (innerAD leaf573Box) leaf573InnerLog = true := by
  rfl'

private theorem leaf573InnerLogValid :
    leaf573InnerLog.Valid 8 (innerAD leaf573Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint78PositiveFacts.valid leaf573CoverageChecked

private noncomputable def leaf573InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629577/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf573InputLogOnePlusV_eq :
    leaf573InputLogOnePlusV = outerEnclosure 24
      (leaf573Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf573RoundedFacts : LeafRoundedFacts 8
    leaf573Certificate.logOnePlusV leaf573InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf573InputLogOnePlusV_eq }

private noncomputable def leaf573Inputs : Inputs :=
  inputsOfCaches globalInput sk27RoundedInputs
    chi79InputQChi innerPair266Input
    leaf573InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf573LowerChecked :
    lowerCheck 24 leaf573Box leaf573Inputs = true := by
  rfl'

private theorem leaf573CoversExact : CoversExact 8
    leaf573Box leaf573Certificate leaf573InnerLog leaf573Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk27RoundedFacts chi79RoundedFacts
    innerPair266RoundedFacts leaf573RoundedFacts (by rfl)

private theorem leaf573FlatSound : Sound leaf573Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf573CertificateValid
    leaf573InnerLogValid leaf573CoversExact leaf573LowerChecked

private noncomputable def leaf574Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/16), kHi := (3/2), chiLo := (15/16), chiHi := (1) }

private noncomputable def leaf574Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (16777295/16777216) }, vSqrt := { lower := (16383/16384), upper := (34358231037/34356592640) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (39352911/33554432) }, upper := { exponent := 1, mantissa := (5/4) } }, logOuter := sk28LogOuterCertificate, logK := sk28LogKCertificate, logChi := chi79LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68714823677/68713185280) } }, logDArg := sk28LogDArgCertificate }

private noncomputable def leaf574InnerLog : WideLogData :=
  innerPair274Data

set_option maxRecDepth 1000000 in
private theorem leaf574LocalValidity :
    LeafFacts leaf574Box leaf574Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf574Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34358231037/34356592640) }) = true
      norm_num [leaf574Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf574CertificateValid :
    WideCertificateValid leaf574Box leaf574Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk28ValidityFacts chi79ValidityFacts
    leaf574LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf574CoverageChecked :
    coverageCheck (innerAD leaf574Box) leaf574InnerLog = true := by
  rfl'

private theorem leaf574InnerLogValid :
    leaf574InnerLog.Valid 8 (innerAD leaf574Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint79PositiveFacts.valid leaf574CoverageChecked

private noncomputable def leaf574InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629481/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf574InputLogOnePlusV_eq :
    leaf574InputLogOnePlusV = outerEnclosure 24
      (leaf574Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf574RoundedFacts : LeafRoundedFacts 8
    leaf574Certificate.logOnePlusV leaf574InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf574InputLogOnePlusV_eq }

private noncomputable def leaf574Inputs : Inputs :=
  inputsOfCaches globalInput sk28RoundedInputs
    chi79InputQChi innerPair274Input
    leaf574InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf574LowerChecked :
    lowerCheck 24 leaf574Box leaf574Inputs = true := by
  rfl'

private theorem leaf574CoversExact : CoversExact 8
    leaf574Box leaf574Certificate leaf574InnerLog leaf574Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk28RoundedFacts chi79RoundedFacts
    innerPair274RoundedFacts leaf574RoundedFacts (by rfl)

private theorem leaf574FlatSound : Sound leaf574Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf574CertificateValid
    leaf574InnerLogValid leaf574CoversExact leaf574LowerChecked

private noncomputable def component13Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (9/8), chiLo := (3/4), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component13Node0_sound : Sound component13Node0Box :=
  sound_of_literal_split component13Node0Box leaf543Box leaf544Box
    .k (17/16) (by rfl) (by rfl)
    leaf543FlatSound leaf544FlatSound

private noncomputable def component13Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (9/8), chiLo := (13/16), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component13Node1_sound : Sound component13Node1Box :=
  sound_of_literal_split component13Node1Box leaf545Box leaf546Box
    .k (17/16) (by rfl) (by rfl)
    leaf545FlatSound leaf546FlatSound

private noncomputable def component13Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (9/8), chiLo := (3/4), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component13Node2_sound : Sound component13Node2Box :=
  sound_of_literal_split component13Node2Box component13Node0Box component13Node1Box
    .chi (13/16) (by rfl) (by rfl)
    component13Node0_sound component13Node1_sound

private noncomputable def component13Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (9/8), chiLo := (7/8), chiHi := (15/16) }

set_option maxRecDepth 1000000 in
private theorem component13Node3_sound : Sound component13Node3Box :=
  sound_of_literal_split component13Node3Box leaf547Box leaf548Box
    .k (17/16) (by rfl) (by rfl)
    leaf547FlatSound leaf548FlatSound

private noncomputable def component13Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (9/8), chiLo := (15/16), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component13Node4_sound : Sound component13Node4Box :=
  sound_of_literal_split component13Node4Box leaf549Box leaf550Box
    .k (17/16) (by rfl) (by rfl)
    leaf549FlatSound leaf550FlatSound

private noncomputable def component13Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (9/8), chiLo := (7/8), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component13Node5_sound : Sound component13Node5Box :=
  sound_of_literal_split component13Node5Box component13Node3Box component13Node4Box
    .chi (15/16) (by rfl) (by rfl)
    component13Node3_sound component13Node4_sound

private noncomputable def component13Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (9/8), chiLo := (3/4), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component13Node6_sound : Sound component13Node6Box :=
  sound_of_literal_split component13Node6Box component13Node2Box component13Node5Box
    .chi (7/8) (by rfl) (by rfl)
    component13Node2_sound component13Node5_sound

private noncomputable def component13Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (5/4), chiLo := (3/4), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component13Node7_sound : Sound component13Node7Box :=
  sound_of_literal_split component13Node7Box leaf551Box leaf552Box
    .k (19/16) (by rfl) (by rfl)
    leaf551FlatSound leaf552FlatSound

private noncomputable def component13Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (5/4), chiLo := (13/16), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component13Node8_sound : Sound component13Node8Box :=
  sound_of_literal_split component13Node8Box leaf553Box leaf554Box
    .k (19/16) (by rfl) (by rfl)
    leaf553FlatSound leaf554FlatSound

private noncomputable def component13Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (5/4), chiLo := (3/4), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component13Node9_sound : Sound component13Node9Box :=
  sound_of_literal_split component13Node9Box component13Node7Box component13Node8Box
    .chi (13/16) (by rfl) (by rfl)
    component13Node7_sound component13Node8_sound

private noncomputable def component13Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (5/4), chiLo := (7/8), chiHi := (15/16) }

set_option maxRecDepth 1000000 in
private theorem component13Node10_sound : Sound component13Node10Box :=
  sound_of_literal_split component13Node10Box leaf555Box leaf556Box
    .k (19/16) (by rfl) (by rfl)
    leaf555FlatSound leaf556FlatSound

private noncomputable def component13Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (5/4), chiLo := (15/16), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component13Node11_sound : Sound component13Node11Box :=
  sound_of_literal_split component13Node11Box leaf557Box leaf558Box
    .k (19/16) (by rfl) (by rfl)
    leaf557FlatSound leaf558FlatSound

private noncomputable def component13Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (5/4), chiLo := (7/8), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component13Node12_sound : Sound component13Node12Box :=
  sound_of_literal_split component13Node12Box component13Node10Box component13Node11Box
    .chi (15/16) (by rfl) (by rfl)
    component13Node10_sound component13Node11_sound

private noncomputable def component13Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (5/4), chiLo := (3/4), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component13Node13_sound : Sound component13Node13Box :=
  sound_of_literal_split component13Node13Box component13Node9Box component13Node12Box
    .chi (7/8) (by rfl) (by rfl)
    component13Node9_sound component13Node12_sound

private noncomputable def component13Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (5/4), chiLo := (3/4), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component13Node14_sound : Sound component13Node14Box :=
  sound_of_literal_split component13Node14Box component13Node6Box component13Node13Box
    .k (9/8) (by rfl) (by rfl)
    component13Node6_sound component13Node13_sound

private noncomputable def component13Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (11/8), chiLo := (3/4), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component13Node15_sound : Sound component13Node15Box :=
  sound_of_literal_split component13Node15Box leaf559Box leaf560Box
    .k (21/16) (by rfl) (by rfl)
    leaf559FlatSound leaf560FlatSound

private noncomputable def component13Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (11/8), chiLo := (13/16), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component13Node16_sound : Sound component13Node16Box :=
  sound_of_literal_split component13Node16Box leaf561Box leaf562Box
    .k (21/16) (by rfl) (by rfl)
    leaf561FlatSound leaf562FlatSound

private noncomputable def component13Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (11/8), chiLo := (3/4), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component13Node17_sound : Sound component13Node17Box :=
  sound_of_literal_split component13Node17Box component13Node15Box component13Node16Box
    .chi (13/16) (by rfl) (by rfl)
    component13Node15_sound component13Node16_sound

private noncomputable def component13Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (3/2), chiLo := (3/4), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component13Node18_sound : Sound component13Node18Box :=
  sound_of_literal_split component13Node18Box leaf563Box leaf564Box
    .k (23/16) (by rfl) (by rfl)
    leaf563FlatSound leaf564FlatSound

private noncomputable def component13Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (3/2), chiLo := (13/16), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component13Node19_sound : Sound component13Node19Box :=
  sound_of_literal_split component13Node19Box leaf565Box leaf566Box
    .k (23/16) (by rfl) (by rfl)
    leaf565FlatSound leaf566FlatSound

private noncomputable def component13Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (3/2), chiLo := (3/4), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component13Node20_sound : Sound component13Node20Box :=
  sound_of_literal_split component13Node20Box component13Node18Box component13Node19Box
    .chi (13/16) (by rfl) (by rfl)
    component13Node18_sound component13Node19_sound

private noncomputable def component13Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (3/2), chiLo := (3/4), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component13Node21_sound : Sound component13Node21Box :=
  sound_of_literal_split component13Node21Box component13Node17Box component13Node20Box
    .k (11/8) (by rfl) (by rfl)
    component13Node17_sound component13Node20_sound

private noncomputable def component13Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (11/8), chiLo := (7/8), chiHi := (15/16) }

set_option maxRecDepth 1000000 in
private theorem component13Node22_sound : Sound component13Node22Box :=
  sound_of_literal_split component13Node22Box leaf567Box leaf568Box
    .k (21/16) (by rfl) (by rfl)
    leaf567FlatSound leaf568FlatSound

private noncomputable def component13Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (11/8), chiLo := (15/16), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component13Node23_sound : Sound component13Node23Box :=
  sound_of_literal_split component13Node23Box leaf569Box leaf570Box
    .k (21/16) (by rfl) (by rfl)
    leaf569FlatSound leaf570FlatSound

private noncomputable def component13Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (11/8), chiLo := (7/8), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component13Node24_sound : Sound component13Node24Box :=
  sound_of_literal_split component13Node24Box component13Node22Box component13Node23Box
    .chi (15/16) (by rfl) (by rfl)
    component13Node22_sound component13Node23_sound

private noncomputable def component13Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (3/2), chiLo := (7/8), chiHi := (15/16) }

set_option maxRecDepth 1000000 in
private theorem component13Node25_sound : Sound component13Node25Box :=
  sound_of_literal_split component13Node25Box leaf571Box leaf572Box
    .k (23/16) (by rfl) (by rfl)
    leaf571FlatSound leaf572FlatSound

private noncomputable def component13Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (3/2), chiLo := (15/16), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component13Node26_sound : Sound component13Node26Box :=
  sound_of_literal_split component13Node26Box leaf573Box leaf574Box
    .k (23/16) (by rfl) (by rfl)
    leaf573FlatSound leaf574FlatSound

private noncomputable def component13Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (3/2), chiLo := (7/8), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component13Node27_sound : Sound component13Node27Box :=
  sound_of_literal_split component13Node27Box component13Node25Box component13Node26Box
    .chi (15/16) (by rfl) (by rfl)
    component13Node25_sound component13Node26_sound

private noncomputable def component13Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (3/2), chiLo := (7/8), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component13Node28_sound : Sound component13Node28Box :=
  sound_of_literal_split component13Node28Box component13Node24Box component13Node27Box
    .k (11/8) (by rfl) (by rfl)
    component13Node24_sound component13Node27_sound

private noncomputable def component13Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (3/2), chiLo := (3/4), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component13Node29_sound : Sound component13Node29Box :=
  sound_of_literal_split component13Node29Box component13Node21Box component13Node28Box
    .chi (7/8) (by rfl) (by rfl)
    component13Node21_sound component13Node28_sound

noncomputable def component13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (3/2), chiLo := (3/4), chiHi := (1) }

set_option maxRecDepth 1000000 in
theorem component13_sound : Sound component13Box :=
  sound_of_literal_split component13Box component13Node14Box component13Node29Box
    .k (5/4) (by rfl) (by rfl)
    component13Node14_sound component13Node29_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
