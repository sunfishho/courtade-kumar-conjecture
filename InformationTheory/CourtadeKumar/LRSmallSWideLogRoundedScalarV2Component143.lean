import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch7
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch8
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch9
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch11
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch12
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch13
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

private noncomputable def leaf7022Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (5/8), chiHi := (81/128) }

private noncomputable def leaf7022Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218011/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588669696) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (448738279/268435456) }, upper := { exponent := 1, mantissa := (6989/4096) } }, logOuter := sk157LogOuterCertificate, logK := sk157LogKCertificate, logChi := chi349LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178096383/17177339392) } }, logDArg := sk157LogDArgCertificate }

private noncomputable def leaf7022InnerLog : WideLogData :=
  innerPair765Data

set_option maxRecDepth 1000000 in
private theorem leaf7022LocalValidity :
    LeafFacts leaf7022Box leaf7022Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7022Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588669696) }) = true
      norm_num [leaf7022Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7022CertificateValid :
    WideCertificateValid leaf7022Box leaf7022Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk157ValidityFacts chi349ValidityFacts
    leaf7022LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7022CoverageChecked :
    coverageCheck (innerAD leaf7022Box) leaf7022InnerLog = true := by
  rfl'

private theorem leaf7022InnerLogValid :
    leaf7022InnerLog.Valid 8 (innerAD leaf7022Box) :=
  wideLogDataValid_of_cachedCheck endpoint486PositiveFacts
    endpoint488PositiveFacts.valid leaf7022CoverageChecked

private noncomputable def leaf7022InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907455/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf7022InputLogOnePlusV_eq :
    leaf7022InputLogOnePlusV = outerEnclosure 24
      (leaf7022Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7022RoundedFacts : LeafRoundedFacts 8
    leaf7022Certificate.logOnePlusV leaf7022InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7022InputLogOnePlusV_eq }

private noncomputable def leaf7022Inputs : Inputs :=
  inputsOfCaches globalInput sk157RoundedInputs
    chi349InputQChi innerPair765Input
    leaf7022InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7022LowerChecked :
    lowerCheck 24 leaf7022Box leaf7022Inputs = true := by
  rfl'

private theorem leaf7022CoversExact : CoversExact 8
    leaf7022Box leaf7022Certificate leaf7022InnerLog leaf7022Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk157RoundedFacts chi349RoundedFacts
    innerPair765RoundedFacts leaf7022RoundedFacts (by rfl)

private theorem leaf7022FlatSound : Sound leaf7022Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7022CertificateValid
    leaf7022InnerLogValid leaf7022CoversExact leaf7022LowerChecked

private noncomputable def leaf7023Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (81/128), chiHi := (41/64) }

private noncomputable def leaf7023Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218013/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588654080) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (452670197/268435456) }, upper := { exponent := 1, mantissa := (3525/2048) } }, logOuter := sk157LogOuterCertificate, logK := sk157LogKCertificate, logChi := chi350LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178080767/17177308160) } }, logDArg := sk157LogDArgCertificate }

private noncomputable def leaf7023InnerLog : WideLogData :=
  innerPair847Data

set_option maxRecDepth 1000000 in
private theorem leaf7023LocalValidity :
    LeafFacts leaf7023Box leaf7023Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7023Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588654080) }) = true
      norm_num [leaf7023Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7023CertificateValid :
    WideCertificateValid leaf7023Box leaf7023Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk157ValidityFacts chi350ValidityFacts
    leaf7023LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7023CoverageChecked :
    coverageCheck (innerAD leaf7023Box) leaf7023InnerLog = true := by
  rfl'

private theorem leaf7023InnerLogValid :
    leaf7023InnerLog.Valid 8 (innerAD leaf7023Box) :=
  wideLogDataValid_of_cachedCheck endpoint541PositiveFacts
    endpoint559PositiveFacts.valid leaf7023CoverageChecked

private noncomputable def leaf7023InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629835/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7023InputLogOnePlusV_eq :
    leaf7023InputLogOnePlusV = outerEnclosure 24
      (leaf7023Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7023RoundedFacts : LeafRoundedFacts 8
    leaf7023Certificate.logOnePlusV leaf7023InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7023InputLogOnePlusV_eq }

private noncomputable def leaf7023Inputs : Inputs :=
  inputsOfCaches globalInput sk157RoundedInputs
    chi350InputQChi innerPair847Input
    leaf7023InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7023LowerChecked :
    lowerCheck 24 leaf7023Box leaf7023Inputs = true := by
  rfl'

private theorem leaf7023CoversExact : CoversExact 8
    leaf7023Box leaf7023Certificate leaf7023InnerLog leaf7023Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk157RoundedFacts chi350RoundedFacts
    innerPair847RoundedFacts leaf7023RoundedFacts (by rfl)

private theorem leaf7023FlatSound : Sound leaf7023Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7023CertificateValid
    leaf7023InnerLogValid leaf7023CoversExact leaf7023LowerChecked

private noncomputable def leaf7024Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (5/8), chiHi := (81/128) }

private noncomputable def leaf7024Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218013/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588648960) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (453980837/268435456) }, upper := { exponent := 1, mantissa := (3535/2048) } }, logOuter := sk158LogOuterCertificate, logK := sk158LogKCertificate, logChi := chi349LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178075647/17177297920) } }, logDArg := sk158LogDArgCertificate }

private noncomputable def leaf7024InnerLog : WideLogData :=
  innerPair774Data

set_option maxRecDepth 1000000 in
private theorem leaf7024LocalValidity :
    LeafFacts leaf7024Box leaf7024Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7024Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588648960) }) = true
      norm_num [leaf7024Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7024CertificateValid :
    WideCertificateValid leaf7024Box leaf7024Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk158ValidityFacts chi349ValidityFacts
    leaf7024LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7024CoverageChecked :
    coverageCheck (innerAD leaf7024Box) leaf7024InnerLog = true := by
  rfl'

private theorem leaf7024InnerLogValid :
    leaf7024InnerLog.Valid 8 (innerAD leaf7024Box) :=
  wideLogDataValid_of_cachedCheck endpoint487PositiveFacts
    endpoint559PositiveFacts.valid leaf7024CoverageChecked

private noncomputable def leaf7024InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726865/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf7024InputLogOnePlusV_eq :
    leaf7024InputLogOnePlusV = outerEnclosure 24
      (leaf7024Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7024RoundedFacts : LeafRoundedFacts 8
    leaf7024Certificate.logOnePlusV leaf7024InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7024InputLogOnePlusV_eq }

private noncomputable def leaf7024Inputs : Inputs :=
  inputsOfCaches globalInput sk158RoundedInputs
    chi349InputQChi innerPair774Input
    leaf7024InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7024LowerChecked :
    lowerCheck 24 leaf7024Box leaf7024Inputs = true := by
  rfl'

private theorem leaf7024CoversExact : CoversExact 8
    leaf7024Box leaf7024Certificate leaf7024InnerLog leaf7024Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk158RoundedFacts chi349RoundedFacts
    innerPair774RoundedFacts leaf7024RoundedFacts (by rfl)

private theorem leaf7024FlatSound : Sound leaf7024Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7024CertificateValid
    leaf7024InnerLogValid leaf7024CoversExact leaf7024LowerChecked

private noncomputable def leaf7025Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (81/128), chiHi := (41/64) }

private noncomputable def leaf7025Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218015/134217728) }, vSqrt := { lower := (8191/8192), upper := (11452394153/11451510784) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (457978287/268435456) }, upper := { exponent := 1, mantissa := (1783/1024) } }, logOuter := sk158LogOuterCertificate, logK := sk158LogKCertificate, logChi := chi350LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (22903904937/22903021568) } }, logDArg := sk158LogDArgCertificate }

private noncomputable def leaf7025InnerLog : WideLogData :=
  innerPair770Data

set_option maxRecDepth 1000000 in
private theorem leaf7025LocalValidity :
    LeafFacts leaf7025Box leaf7025Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7025Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (11452394153/11451510784) }) = true
      norm_num [leaf7025Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7025CertificateValid :
    WideCertificateValid leaf7025Box leaf7025Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk158ValidityFacts chi350ValidityFacts
    leaf7025LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7025CoverageChecked :
    coverageCheck (innerAD leaf7025Box) leaf7025InnerLog = true := by
  rfl'

private theorem leaf7025InnerLogValid :
    leaf7025InnerLog.Valid 8 (innerAD leaf7025Box) :=
  wideLogDataValid_of_cachedCheck endpoint487PositiveFacts
    endpoint489PositiveFacts.valid leaf7025CoverageChecked

private noncomputable def leaf7025InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (363429/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf7025InputLogOnePlusV_eq :
    leaf7025InputLogOnePlusV = outerEnclosure 24
      (leaf7025Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7025RoundedFacts : LeafRoundedFacts 8
    leaf7025Certificate.logOnePlusV leaf7025InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7025InputLogOnePlusV_eq }

private noncomputable def leaf7025Inputs : Inputs :=
  inputsOfCaches globalInput sk158RoundedInputs
    chi350InputQChi innerPair770Input
    leaf7025InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7025LowerChecked :
    lowerCheck 24 leaf7025Box leaf7025Inputs = true := by
  rfl'

private theorem leaf7025CoversExact : CoversExact 8
    leaf7025Box leaf7025Certificate leaf7025InnerLog leaf7025Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk158RoundedFacts chi350RoundedFacts
    innerPair770RoundedFacts leaf7025RoundedFacts (by rfl)

private theorem leaf7025FlatSound : Sound leaf7025Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7025CertificateValid
    leaf7025InnerLogValid leaf7025CoversExact leaf7025LowerChecked

private noncomputable def leaf7026Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (41/64), chiHi := (83/128) }

private noncomputable def leaf7026Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218015/134217728) }, vSqrt := { lower := (8191/8192), upper := (11452394153/11451517952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (456602115/268435456) }, upper := { exponent := 1, mantissa := (7111/4096) } }, logOuter := sk157LogOuterCertificate, logK := sk157LogKCertificate, logChi := chi351LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (22903912105/22903035904) } }, logDArg := sk157LogDArgCertificate }

private noncomputable def leaf7026InnerLog : WideLogData :=
  innerPair770Data

set_option maxRecDepth 1000000 in
private theorem leaf7026LocalValidity :
    LeafFacts leaf7026Box leaf7026Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7026Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (11452394153/11451517952) }) = true
      norm_num [leaf7026Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7026CertificateValid :
    WideCertificateValid leaf7026Box leaf7026Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk157ValidityFacts chi351ValidityFacts
    leaf7026LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7026CoverageChecked :
    coverageCheck (innerAD leaf7026Box) leaf7026InnerLog = true := by
  rfl'

private theorem leaf7026InnerLogValid :
    leaf7026InnerLog.Valid 8 (innerAD leaf7026Box) :=
  wideLogDataValid_of_cachedCheck endpoint487PositiveFacts
    endpoint489PositiveFacts.valid leaf7026CoverageChecked

private noncomputable def leaf7026InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629723/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7026InputLogOnePlusV_eq :
    leaf7026InputLogOnePlusV = outerEnclosure 24
      (leaf7026Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7026RoundedFacts : LeafRoundedFacts 8
    leaf7026Certificate.logOnePlusV leaf7026InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7026InputLogOnePlusV_eq }

private noncomputable def leaf7026Inputs : Inputs :=
  inputsOfCaches globalInput sk157RoundedInputs
    chi351InputQChi innerPair770Input
    leaf7026InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7026LowerChecked :
    lowerCheck 24 leaf7026Box leaf7026Inputs = true := by
  rfl'

private theorem leaf7026CoversExact : CoversExact 8
    leaf7026Box leaf7026Certificate leaf7026InnerLog leaf7026Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk157RoundedFacts chi351RoundedFacts
    innerPair770RoundedFacts leaf7026RoundedFacts (by rfl)

private theorem leaf7026FlatSound : Sound leaf7026Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7026CertificateValid
    leaf7026InnerLogValid leaf7026CoversExact leaf7026LowerChecked

private noncomputable def leaf7027Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (83/128), chiHi := (21/32) }

private noncomputable def leaf7027Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (134218017/134217728) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34354491392) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (460534033/268435456) }, upper := { exponent := 1, mantissa := (1793/1024) } }, logOuter := sk157LogOuterCertificate, logK := sk157LogKCertificate, logChi := chi352LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68711673851/68708982784) } }, logDArg := sk157LogDArgCertificate }

private noncomputable def leaf7027InnerLog : WideLogData :=
  innerPair771Data

set_option maxRecDepth 1000000 in
private theorem leaf7027LocalValidity :
    LeafFacts leaf7027Box leaf7027Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7027Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34354491392) }) = true
      norm_num [leaf7027Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7027CertificateValid :
    WideCertificateValid leaf7027Box leaf7027Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk157ValidityFacts chi352ValidityFacts
    leaf7027LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7027CoverageChecked :
    coverageCheck (innerAD leaf7027Box) leaf7027InnerLog = true := by
  rfl'

private theorem leaf7027InnerLogValid :
    leaf7027InnerLog.Valid 8 (innerAD leaf7027Box) :=
  wideLogDataValid_of_cachedCheck endpoint487PositiveFacts
    endpoint498PositiveFacts.valid leaf7027CoverageChecked

private noncomputable def leaf7027InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814869/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf7027InputLogOnePlusV_eq :
    leaf7027InputLogOnePlusV = outerEnclosure 24
      (leaf7027Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7027RoundedFacts : LeafRoundedFacts 8
    leaf7027Certificate.logOnePlusV leaf7027InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7027InputLogOnePlusV_eq }

private noncomputable def leaf7027Inputs : Inputs :=
  inputsOfCaches globalInput sk157RoundedInputs
    chi352InputQChi innerPair771Input
    leaf7027InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7027LowerChecked :
    lowerCheck 24 leaf7027Box leaf7027Inputs = true := by
  rfl'

private theorem leaf7027CoversExact : CoversExact 8
    leaf7027Box leaf7027Certificate leaf7027InnerLog leaf7027Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk157RoundedFacts chi352RoundedFacts
    innerPair771RoundedFacts leaf7027RoundedFacts (by rfl)

private theorem leaf7027FlatSound : Sound leaf7027Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7027CertificateValid
    leaf7027InnerLogValid leaf7027CoversExact leaf7027LowerChecked

private noncomputable def leaf7028Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (41/64), chiHi := (83/128) }

private noncomputable def leaf7028Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (134218017/134217728) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34354468864) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (461975737/268435456) }, upper := { exponent := 1, mantissa := (3597/2048) } }, logOuter := sk158LogOuterCertificate, logK := sk158LogKCertificate, logChi := chi351LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68711651323/68708937728) } }, logDArg := sk158LogDArgCertificate }

private noncomputable def leaf7028InnerLog : WideLogData :=
  innerPair775Data

set_option maxRecDepth 1000000 in
private theorem leaf7028LocalValidity :
    LeafFacts leaf7028Box leaf7028Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7028Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34354468864) }) = true
      norm_num [leaf7028Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7028CertificateValid :
    WideCertificateValid leaf7028Box leaf7028Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk158ValidityFacts chi351ValidityFacts
    leaf7028LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7028CoverageChecked :
    coverageCheck (innerAD leaf7028Box) leaf7028InnerLog = true := by
  rfl'

private theorem leaf7028InnerLogValid :
    leaf7028InnerLog.Valid 8 (innerAD leaf7028Box) :=
  wideLogDataValid_of_cachedCheck endpoint488PositiveFacts
    endpoint498PositiveFacts.valid leaf7028CoverageChecked

private noncomputable def leaf7028InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629743/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7028InputLogOnePlusV_eq :
    leaf7028InputLogOnePlusV = outerEnclosure 24
      (leaf7028Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7028RoundedFacts : LeafRoundedFacts 8
    leaf7028Certificate.logOnePlusV leaf7028InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7028InputLogOnePlusV_eq }

private noncomputable def leaf7028Inputs : Inputs :=
  inputsOfCaches globalInput sk158RoundedInputs
    chi351InputQChi innerPair775Input
    leaf7028InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7028LowerChecked :
    lowerCheck 24 leaf7028Box leaf7028Inputs = true := by
  rfl'

private theorem leaf7028CoversExact : CoversExact 8
    leaf7028Box leaf7028Certificate leaf7028InnerLog leaf7028Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk158RoundedFacts chi351RoundedFacts
    innerPair775RoundedFacts leaf7028RoundedFacts (by rfl)

private theorem leaf7028FlatSound : Sound leaf7028Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7028CertificateValid
    leaf7028InnerLogValid leaf7028CoversExact leaf7028LowerChecked

private noncomputable def leaf7029Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (83/128), chiHi := (21/32) }

private noncomputable def leaf7029Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (134218019/134217728) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34354405376) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (465973187/268435456) }, upper := { exponent := 1, mantissa := (907/512) } }, logOuter := sk158LogOuterCertificate, logK := sk158LogKCertificate, logChi := chi352LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68711587835/68708810752) } }, logDArg := sk158LogDArgCertificate }

private noncomputable def leaf7029InnerLog : WideLogData :=
  innerPair775Data

set_option maxRecDepth 1000000 in
private theorem leaf7029LocalValidity :
    LeafFacts leaf7029Box leaf7029Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7029Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34354405376) }) = true
      norm_num [leaf7029Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7029CertificateValid :
    WideCertificateValid leaf7029Box leaf7029Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk158ValidityFacts chi352ValidityFacts
    leaf7029LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7029CoverageChecked :
    coverageCheck (innerAD leaf7029Box) leaf7029InnerLog = true := by
  rfl'

private theorem leaf7029InnerLogValid :
    leaf7029InnerLog.Valid 8 (innerAD leaf7029Box) :=
  wideLogDataValid_of_cachedCheck endpoint488PositiveFacts
    endpoint498PositiveFacts.valid leaf7029CoverageChecked

private noncomputable def leaf7029InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629759/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7029InputLogOnePlusV_eq :
    leaf7029InputLogOnePlusV = outerEnclosure 24
      (leaf7029Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7029RoundedFacts : LeafRoundedFacts 8
    leaf7029Certificate.logOnePlusV leaf7029InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7029InputLogOnePlusV_eq }

private noncomputable def leaf7029Inputs : Inputs :=
  inputsOfCaches globalInput sk158RoundedInputs
    chi352InputQChi innerPair775Input
    leaf7029InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7029LowerChecked :
    lowerCheck 24 leaf7029Box leaf7029Inputs = true := by
  rfl'

private theorem leaf7029CoversExact : CoversExact 8
    leaf7029Box leaf7029Certificate leaf7029InnerLog leaf7029Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk158RoundedFacts chi352RoundedFacts
    innerPair775RoundedFacts leaf7029RoundedFacts (by rfl)

private theorem leaf7029FlatSound : Sound leaf7029Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7029CertificateValid
    leaf7029InnerLogValid leaf7029CoversExact leaf7029LowerChecked

private noncomputable def leaf7030Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (5/8), chiHi := (81/128) }

private noncomputable def leaf7030Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218015/134217728) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34354512896) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (459223395/268435456) }, upper := { exponent := 1, mantissa := (7151/4096) } }, logOuter := sk159LogOuterCertificate, logK := sk159LogKCertificate, logChi := chi349LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68711695355/68709025792) } }, logDArg := sk159LogDArgCertificate }

private noncomputable def leaf7030InnerLog : WideLogData :=
  innerPair770Data

set_option maxRecDepth 1000000 in
private theorem leaf7030LocalValidity :
    LeafFacts leaf7030Box leaf7030Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7030Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34354512896) }) = true
      norm_num [leaf7030Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7030CertificateValid :
    WideCertificateValid leaf7030Box leaf7030Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk159ValidityFacts chi349ValidityFacts
    leaf7030LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7030CoverageChecked :
    coverageCheck (innerAD leaf7030Box) leaf7030InnerLog = true := by
  rfl'

private theorem leaf7030InnerLogValid :
    leaf7030InnerLog.Valid 8 (innerAD leaf7030Box) :=
  wideLogDataValid_of_cachedCheck endpoint487PositiveFacts
    endpoint489PositiveFacts.valid leaf7030CoverageChecked

private noncomputable def leaf7030InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629733/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7030InputLogOnePlusV_eq :
    leaf7030InputLogOnePlusV = outerEnclosure 24
      (leaf7030Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7030RoundedFacts : LeafRoundedFacts 8
    leaf7030Certificate.logOnePlusV leaf7030InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7030InputLogOnePlusV_eq }

private noncomputable def leaf7030Inputs : Inputs :=
  inputsOfCaches globalInput sk159RoundedInputs
    chi349InputQChi innerPair770Input
    leaf7030InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7030LowerChecked :
    lowerCheck 24 leaf7030Box leaf7030Inputs = true := by
  rfl'

private theorem leaf7030CoversExact : CoversExact 8
    leaf7030Box leaf7030Certificate leaf7030InnerLog leaf7030Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk159RoundedFacts chi349RoundedFacts
    innerPair770RoundedFacts leaf7030RoundedFacts (by rfl)

private theorem leaf7030FlatSound : Sound leaf7030Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7030CertificateValid
    leaf7030InnerLogValid leaf7030CoversExact leaf7030LowerChecked

private noncomputable def leaf7031Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (81/128), chiHi := (41/64) }

private noncomputable def leaf7031Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (134218017/134217728) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34354448384) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (463286377/268435456) }, upper := { exponent := 1, mantissa := (3607/2048) } }, logOuter := sk159LogOuterCertificate, logK := sk159LogKCertificate, logChi := chi350LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68711630843/68708896768) } }, logDArg := sk159LogDArgCertificate }

private noncomputable def leaf7031InnerLog : WideLogData :=
  innerPair775Data

set_option maxRecDepth 1000000 in
private theorem leaf7031LocalValidity :
    LeafFacts leaf7031Box leaf7031Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7031Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34354448384) }) = true
      norm_num [leaf7031Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7031CertificateValid :
    WideCertificateValid leaf7031Box leaf7031Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk159ValidityFacts chi350ValidityFacts
    leaf7031LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7031CoverageChecked :
    coverageCheck (innerAD leaf7031Box) leaf7031InnerLog = true := by
  rfl'

private theorem leaf7031InnerLogValid :
    leaf7031InnerLog.Valid 8 (innerAD leaf7031Box) :=
  wideLogDataValid_of_cachedCheck endpoint488PositiveFacts
    endpoint498PositiveFacts.valid leaf7031CoverageChecked

private noncomputable def leaf7031InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907437/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf7031InputLogOnePlusV_eq :
    leaf7031InputLogOnePlusV = outerEnclosure 24
      (leaf7031Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7031RoundedFacts : LeafRoundedFacts 8
    leaf7031Certificate.logOnePlusV leaf7031InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7031InputLogOnePlusV_eq }

private noncomputable def leaf7031Inputs : Inputs :=
  inputsOfCaches globalInput sk159RoundedInputs
    chi350InputQChi innerPair775Input
    leaf7031InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7031LowerChecked :
    lowerCheck 24 leaf7031Box leaf7031Inputs = true := by
  rfl'

private theorem leaf7031CoversExact : CoversExact 8
    leaf7031Box leaf7031Certificate leaf7031InnerLog leaf7031Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk159RoundedFacts chi350RoundedFacts
    innerPair775RoundedFacts leaf7031RoundedFacts (by rfl)

private theorem leaf7031FlatSound : Sound leaf7031Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7031CertificateValid
    leaf7031InnerLogValid leaf7031CoversExact leaf7031LowerChecked

private noncomputable def leaf7032Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (5/8), chiHi := (81/128) }

private noncomputable def leaf7032Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (134218017/134217728) }, vSqrt := { lower := (65527/65536), upper := (34357182459/34354429952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (464465953/268435456) }, upper := { exponent := 1, mantissa := (113/64) } }, logOuter := sk160LogOuterCertificate, logK := sk160LogKCertificate, logChi := chi349LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (68711612411/68708859904) } }, logDArg := sk160LogDArgCertificate }

private noncomputable def leaf7032InnerLog : WideLogData :=
  innerPair775Data

set_option maxRecDepth 1000000 in
private theorem leaf7032LocalValidity :
    LeafFacts leaf7032Box leaf7032Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7032Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (34357182459/34354429952) }) = true
      norm_num [leaf7032Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7032CertificateValid :
    WideCertificateValid leaf7032Box leaf7032Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk160ValidityFacts chi349ValidityFacts
    leaf7032LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7032CoverageChecked :
    coverageCheck (innerAD leaf7032Box) leaf7032InnerLog = true := by
  rfl'

private theorem leaf7032InnerLogValid :
    leaf7032InnerLog.Valid 8 (innerAD leaf7032Box) :=
  wideLogDataValid_of_cachedCheck endpoint488PositiveFacts
    endpoint498PositiveFacts.valid leaf7032CoverageChecked

private noncomputable def leaf7032InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629753/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7032InputLogOnePlusV_eq :
    leaf7032InputLogOnePlusV = outerEnclosure 24
      (leaf7032Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7032RoundedFacts : LeafRoundedFacts 8
    leaf7032Certificate.logOnePlusV leaf7032InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7032InputLogOnePlusV_eq }

private noncomputable def leaf7032Inputs : Inputs :=
  inputsOfCaches globalInput sk160RoundedInputs
    chi349InputQChi innerPair775Input
    leaf7032InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7032LowerChecked :
    lowerCheck 24 leaf7032Box leaf7032Inputs = true := by
  rfl'

private theorem leaf7032CoversExact : CoversExact 8
    leaf7032Box leaf7032Certificate leaf7032InnerLog leaf7032Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk160RoundedFacts chi349RoundedFacts
    innerPair775RoundedFacts leaf7032RoundedFacts (by rfl)

private theorem leaf7032FlatSound : Sound leaf7032Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7032CertificateValid
    leaf7032InnerLogValid leaf7032CoversExact leaf7032LowerChecked

private noncomputable def leaf7033Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (81/128), chiHi := (41/64) }

private noncomputable def leaf7033Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (134218019/134217728) }, vSqrt := { lower := (65527/65536), upper := (34357182459/34354364416) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (468594467/268435456) }, upper := { exponent := 1, mantissa := (57/32) } }, logOuter := sk160LogOuterCertificate, logK := sk160LogKCertificate, logChi := chi350LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (68711546875/68708728832) } }, logDArg := sk160LogDArgCertificate }

private noncomputable def leaf7033InnerLog : WideLogData :=
  innerPair775Data

set_option maxRecDepth 1000000 in
private theorem leaf7033LocalValidity :
    LeafFacts leaf7033Box leaf7033Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7033Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (34357182459/34354364416) }) = true
      norm_num [leaf7033Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7033CertificateValid :
    WideCertificateValid leaf7033Box leaf7033Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk160ValidityFacts chi350ValidityFacts
    leaf7033LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7033CoverageChecked :
    coverageCheck (innerAD leaf7033Box) leaf7033InnerLog = true := by
  rfl'

private theorem leaf7033InnerLogValid :
    leaf7033InnerLog.Valid 8 (innerAD leaf7033Box) :=
  wideLogDataValid_of_cachedCheck endpoint488PositiveFacts
    endpoint498PositiveFacts.valid leaf7033CoverageChecked

private noncomputable def leaf7033InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629769/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7033InputLogOnePlusV_eq :
    leaf7033InputLogOnePlusV = outerEnclosure 24
      (leaf7033Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7033RoundedFacts : LeafRoundedFacts 8
    leaf7033Certificate.logOnePlusV leaf7033InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7033InputLogOnePlusV_eq }

private noncomputable def leaf7033Inputs : Inputs :=
  inputsOfCaches globalInput sk160RoundedInputs
    chi350InputQChi innerPair775Input
    leaf7033InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7033LowerChecked :
    lowerCheck 24 leaf7033Box leaf7033Inputs = true := by
  rfl'

private theorem leaf7033CoversExact : CoversExact 8
    leaf7033Box leaf7033Certificate leaf7033InnerLog leaf7033Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk160RoundedFacts chi350RoundedFacts
    innerPair775RoundedFacts leaf7033RoundedFacts (by rfl)

private theorem leaf7033FlatSound : Sound leaf7033Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7033CertificateValid
    leaf7033InnerLogValid leaf7033CoversExact leaf7033LowerChecked

private noncomputable def leaf7034Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (41/64), chiHi := (83/128) }

private noncomputable def leaf7034Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (134218019/134217728) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34354383872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (467349359/268435456) }, upper := { exponent := 1, mantissa := (7277/4096) } }, logOuter := sk159LogOuterCertificate, logK := sk159LogKCertificate, logChi := chi351LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68711566331/68708767744) } }, logDArg := sk159LogDArgCertificate }

private noncomputable def leaf7034InnerLog : WideLogData :=
  innerPair775Data

set_option maxRecDepth 1000000 in
private theorem leaf7034LocalValidity :
    LeafFacts leaf7034Box leaf7034Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7034Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34354383872) }) = true
      norm_num [leaf7034Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7034CertificateValid :
    WideCertificateValid leaf7034Box leaf7034Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk159ValidityFacts chi351ValidityFacts
    leaf7034LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7034CoverageChecked :
    coverageCheck (innerAD leaf7034Box) leaf7034InnerLog = true := by
  rfl'

private theorem leaf7034InnerLogValid :
    leaf7034InnerLog.Valid 8 (innerAD leaf7034Box) :=
  wideLogDataValid_of_cachedCheck endpoint488PositiveFacts
    endpoint498PositiveFacts.valid leaf7034CoverageChecked

private noncomputable def leaf7034InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907441/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf7034InputLogOnePlusV_eq :
    leaf7034InputLogOnePlusV = outerEnclosure 24
      (leaf7034Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7034RoundedFacts : LeafRoundedFacts 8
    leaf7034Certificate.logOnePlusV leaf7034InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7034InputLogOnePlusV_eq }

private noncomputable def leaf7034Inputs : Inputs :=
  inputsOfCaches globalInput sk159RoundedInputs
    chi351InputQChi innerPair775Input
    leaf7034InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7034LowerChecked :
    lowerCheck 24 leaf7034Box leaf7034Inputs = true := by
  rfl'

private theorem leaf7034CoversExact : CoversExact 8
    leaf7034Box leaf7034Certificate leaf7034InnerLog leaf7034Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk159RoundedFacts chi351RoundedFacts
    innerPair775RoundedFacts leaf7034RoundedFacts (by rfl)

private theorem leaf7034FlatSound : Sound leaf7034Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7034CertificateValid
    leaf7034InnerLogValid leaf7034CoversExact leaf7034LowerChecked

private noncomputable def leaf7035Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (83/128), chiHi := (21/32) }

private noncomputable def leaf7035Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (134218021/134217728) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34354319360) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (471412341/268435456) }, upper := { exponent := 1, mantissa := (1835/1024) } }, logOuter := sk159LogOuterCertificate, logK := sk159LogKCertificate, logChi := chi352LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68711501819/68708638720) } }, logDArg := sk159LogDArgCertificate }

private noncomputable def leaf7035InnerLog : WideLogData :=
  innerPair778Data

set_option maxRecDepth 1000000 in
private theorem leaf7035LocalValidity :
    LeafFacts leaf7035Box leaf7035Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7035Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34354319360) }) = true
      norm_num [leaf7035Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7035CertificateValid :
    WideCertificateValid leaf7035Box leaf7035Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk159ValidityFacts chi352ValidityFacts
    leaf7035LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7035CoverageChecked :
    coverageCheck (innerAD leaf7035Box) leaf7035InnerLog = true := by
  rfl'

private theorem leaf7035InnerLogValid :
    leaf7035InnerLog.Valid 8 (innerAD leaf7035Box) :=
  wideLogDataValid_of_cachedCheck endpoint489PositiveFacts
    endpoint500PositiveFacts.valid leaf7035CoverageChecked

private noncomputable def leaf7035InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907445/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf7035InputLogOnePlusV_eq :
    leaf7035InputLogOnePlusV = outerEnclosure 24
      (leaf7035Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7035RoundedFacts : LeafRoundedFacts 8
    leaf7035Certificate.logOnePlusV leaf7035InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7035InputLogOnePlusV_eq }

private noncomputable def leaf7035Inputs : Inputs :=
  inputsOfCaches globalInput sk159RoundedInputs
    chi352InputQChi innerPair778Input
    leaf7035InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7035LowerChecked :
    lowerCheck 24 leaf7035Box leaf7035Inputs = true := by
  rfl'

private theorem leaf7035CoversExact : CoversExact 8
    leaf7035Box leaf7035Certificate leaf7035InnerLog leaf7035Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk159RoundedFacts chi352RoundedFacts
    innerPair778RoundedFacts leaf7035RoundedFacts (by rfl)

private theorem leaf7035FlatSound : Sound leaf7035Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7035CertificateValid
    leaf7035InnerLogValid leaf7035CoversExact leaf7035LowerChecked

private noncomputable def leaf7036Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (41/64), chiHi := (83/128) }

private noncomputable def leaf7036Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (134218021/134217728) }, vSqrt := { lower := (65527/65536), upper := (11452394153/11451432960) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (472722981/268435456) }, upper := { exponent := 1, mantissa := (115/64) } }, logOuter := sk160LogOuterCertificate, logK := sk160LogKCertificate, logChi := chi351LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (22903827113/22902865920) } }, logDArg := sk160LogDArgCertificate }

private noncomputable def leaf7036InnerLog : WideLogData :=
  innerPair778Data

set_option maxRecDepth 1000000 in
private theorem leaf7036LocalValidity :
    LeafFacts leaf7036Box leaf7036Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7036Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (11452394153/11451432960) }) = true
      norm_num [leaf7036Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7036CertificateValid :
    WideCertificateValid leaf7036Box leaf7036Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk160ValidityFacts chi351ValidityFacts
    leaf7036LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7036CoverageChecked :
    coverageCheck (innerAD leaf7036Box) leaf7036InnerLog = true := by
  rfl'

private theorem leaf7036InnerLogValid :
    leaf7036InnerLog.Valid 8 (innerAD leaf7036Box) :=
  wideLogDataValid_of_cachedCheck endpoint489PositiveFacts
    endpoint500PositiveFacts.valid leaf7036CoverageChecked

private noncomputable def leaf7036InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629785/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7036InputLogOnePlusV_eq :
    leaf7036InputLogOnePlusV = outerEnclosure 24
      (leaf7036Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7036RoundedFacts : LeafRoundedFacts 8
    leaf7036Certificate.logOnePlusV leaf7036InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7036InputLogOnePlusV_eq }

private noncomputable def leaf7036Inputs : Inputs :=
  inputsOfCaches globalInput sk160RoundedInputs
    chi351InputQChi innerPair778Input
    leaf7036InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7036LowerChecked :
    lowerCheck 24 leaf7036Box leaf7036Inputs = true := by
  rfl'

private theorem leaf7036CoversExact : CoversExact 8
    leaf7036Box leaf7036Certificate leaf7036InnerLog leaf7036Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk160RoundedFacts chi351RoundedFacts
    innerPair778RoundedFacts leaf7036RoundedFacts (by rfl)

private theorem leaf7036FlatSound : Sound leaf7036Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7036CertificateValid
    leaf7036InnerLogValid leaf7036CoversExact leaf7036LowerChecked

private noncomputable def leaf7037Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (83/128), chiHi := (21/32) }

private noncomputable def leaf7037Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (134218023/134217728) }, vSqrt := { lower := (65527/65536), upper := (34357182459/34354233344) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (476851495/268435456) }, upper := { exponent := 1, mantissa := (29/16) } }, logOuter := sk160LogOuterCertificate, logK := sk160LogKCertificate, logChi := chi352LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (68711415803/68708466688) } }, logDArg := sk160LogDArgCertificate }

private noncomputable def leaf7037InnerLog : WideLogData :=
  innerPair778Data

set_option maxRecDepth 1000000 in
private theorem leaf7037LocalValidity :
    LeafFacts leaf7037Box leaf7037Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7037Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (34357182459/34354233344) }) = true
      norm_num [leaf7037Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7037CertificateValid :
    WideCertificateValid leaf7037Box leaf7037Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk160ValidityFacts chi352ValidityFacts
    leaf7037LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7037CoverageChecked :
    coverageCheck (innerAD leaf7037Box) leaf7037InnerLog = true := by
  rfl'

private theorem leaf7037InnerLogValid :
    leaf7037InnerLog.Valid 8 (innerAD leaf7037Box) :=
  wideLogDataValid_of_cachedCheck endpoint489PositiveFacts
    endpoint500PositiveFacts.valid leaf7037CoverageChecked

private noncomputable def leaf7037InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629801/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7037InputLogOnePlusV_eq :
    leaf7037InputLogOnePlusV = outerEnclosure 24
      (leaf7037Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7037RoundedFacts : LeafRoundedFacts 8
    leaf7037Certificate.logOnePlusV leaf7037InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7037InputLogOnePlusV_eq }

private noncomputable def leaf7037Inputs : Inputs :=
  inputsOfCaches globalInput sk160RoundedInputs
    chi352InputQChi innerPair778Input
    leaf7037InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7037LowerChecked :
    lowerCheck 24 leaf7037Box leaf7037Inputs = true := by
  rfl'

private theorem leaf7037CoversExact : CoversExact 8
    leaf7037Box leaf7037Certificate leaf7037InnerLog leaf7037Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk160RoundedFacts chi352RoundedFacts
    innerPair778RoundedFacts leaf7037RoundedFacts (by rfl)

private theorem leaf7037FlatSound : Sound leaf7037Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7037CertificateValid
    leaf7037InnerLogValid leaf7037CoversExact leaf7037LowerChecked

private noncomputable def leaf7038Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (21/32), chiHi := (85/128) }

private noncomputable def leaf7038Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (134218019/134217728) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34354428928) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (464465951/268435456) }, upper := { exponent := 1, mantissa := (7233/4096) } }, logOuter := sk157LogOuterCertificate, logK := sk157LogKCertificate, logChi := chi353LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68711611387/68708857856) } }, logDArg := sk157LogDArgCertificate }

private noncomputable def leaf7038InnerLog : WideLogData :=
  innerPair775Data

set_option maxRecDepth 1000000 in
private theorem leaf7038LocalValidity :
    LeafFacts leaf7038Box leaf7038Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7038Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34354428928) }) = true
      norm_num [leaf7038Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7038CertificateValid :
    WideCertificateValid leaf7038Box leaf7038Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk157ValidityFacts chi353ValidityFacts
    leaf7038LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7038CoverageChecked :
    coverageCheck (innerAD leaf7038Box) leaf7038InnerLog = true := by
  rfl'

private theorem leaf7038InnerLogValid :
    leaf7038InnerLog.Valid 8 (innerAD leaf7038Box) :=
  wideLogDataValid_of_cachedCheck endpoint488PositiveFacts
    endpoint498PositiveFacts.valid leaf7038CoverageChecked

private noncomputable def leaf7038InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629753/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7038InputLogOnePlusV_eq :
    leaf7038InputLogOnePlusV = outerEnclosure 24
      (leaf7038Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7038RoundedFacts : LeafRoundedFacts 8
    leaf7038Certificate.logOnePlusV leaf7038InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7038InputLogOnePlusV_eq }

private noncomputable def leaf7038Inputs : Inputs :=
  inputsOfCaches globalInput sk157RoundedInputs
    chi353InputQChi innerPair775Input
    leaf7038InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7038LowerChecked :
    lowerCheck 24 leaf7038Box leaf7038Inputs = true := by
  rfl'

private theorem leaf7038CoversExact : CoversExact 8
    leaf7038Box leaf7038Certificate leaf7038InnerLog leaf7038Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk157RoundedFacts chi353RoundedFacts
    innerPair775RoundedFacts leaf7038RoundedFacts (by rfl)

private theorem leaf7038FlatSound : Sound leaf7038Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7038CertificateValid
    leaf7038InnerLogValid leaf7038CoversExact leaf7038LowerChecked

private noncomputable def leaf7039Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (85/128), chiHi := (43/64) }

private noncomputable def leaf7039Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (134218021/134217728) }, vSqrt := { lower := (8191/8192), upper := (11452394153/11451455488) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (468397869/268435456) }, upper := { exponent := 1, mantissa := (3647/2048) } }, logOuter := sk157LogOuterCertificate, logK := sk157LogKCertificate, logChi := chi354LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (22903849641/22902910976) } }, logDArg := sk157LogDArgCertificate }

private noncomputable def leaf7039InnerLog : WideLogData :=
  innerPair775Data

set_option maxRecDepth 1000000 in
private theorem leaf7039LocalValidity :
    LeafFacts leaf7039Box leaf7039Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7039Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (11452394153/11451455488) }) = true
      norm_num [leaf7039Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7039CertificateValid :
    WideCertificateValid leaf7039Box leaf7039Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk157ValidityFacts chi354ValidityFacts
    leaf7039LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7039CoverageChecked :
    coverageCheck (innerAD leaf7039Box) leaf7039InnerLog = true := by
  rfl'

private theorem leaf7039InnerLogValid :
    leaf7039InnerLog.Valid 8 (innerAD leaf7039Box) :=
  wideLogDataValid_of_cachedCheck endpoint488PositiveFacts
    endpoint498PositiveFacts.valid leaf7039CoverageChecked

private noncomputable def leaf7039InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453721/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf7039InputLogOnePlusV_eq :
    leaf7039InputLogOnePlusV = outerEnclosure 24
      (leaf7039Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7039RoundedFacts : LeafRoundedFacts 8
    leaf7039Certificate.logOnePlusV leaf7039InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7039InputLogOnePlusV_eq }

private noncomputable def leaf7039Inputs : Inputs :=
  inputsOfCaches globalInput sk157RoundedInputs
    chi354InputQChi innerPair775Input
    leaf7039InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7039LowerChecked :
    lowerCheck 24 leaf7039Box leaf7039Inputs = true := by
  rfl'

private theorem leaf7039CoversExact : CoversExact 8
    leaf7039Box leaf7039Certificate leaf7039InnerLog leaf7039Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk157RoundedFacts chi354RoundedFacts
    innerPair775RoundedFacts leaf7039RoundedFacts (by rfl)

private theorem leaf7039FlatSound : Sound leaf7039Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7039CertificateValid
    leaf7039InnerLogValid leaf7039CoversExact leaf7039LowerChecked

private noncomputable def leaf7040Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (21/32), chiHi := (85/128) }

private noncomputable def leaf7040Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (134218021/134217728) }, vSqrt := { lower := (8191/8192), upper := (11452394153/11451447296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (469970637/268435456) }, upper := { exponent := 1, mantissa := (3659/2048) } }, logOuter := sk158LogOuterCertificate, logK := sk158LogKCertificate, logChi := chi353LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (22903841449/22902894592) } }, logDArg := sk158LogDArgCertificate }

private noncomputable def leaf7040InnerLog : WideLogData :=
  innerPair778Data

set_option maxRecDepth 1000000 in
private theorem leaf7040LocalValidity :
    LeafFacts leaf7040Box leaf7040Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7040Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (11452394153/11451447296) }) = true
      norm_num [leaf7040Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7040CertificateValid :
    WideCertificateValid leaf7040Box leaf7040Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk158ValidityFacts chi353ValidityFacts
    leaf7040LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7040CoverageChecked :
    coverageCheck (innerAD leaf7040Box) leaf7040InnerLog = true := by
  rfl'

private theorem leaf7040InnerLogValid :
    leaf7040InnerLog.Valid 8 (innerAD leaf7040Box) :=
  wideLogDataValid_of_cachedCheck endpoint489PositiveFacts
    endpoint500PositiveFacts.valid leaf7040CoverageChecked

private noncomputable def leaf7040InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814887/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf7040InputLogOnePlusV_eq :
    leaf7040InputLogOnePlusV = outerEnclosure 24
      (leaf7040Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7040RoundedFacts : LeafRoundedFacts 8
    leaf7040Certificate.logOnePlusV leaf7040InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7040InputLogOnePlusV_eq }

private noncomputable def leaf7040Inputs : Inputs :=
  inputsOfCaches globalInput sk158RoundedInputs
    chi353InputQChi innerPair778Input
    leaf7040InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7040LowerChecked :
    lowerCheck 24 leaf7040Box leaf7040Inputs = true := by
  rfl'

private theorem leaf7040CoversExact : CoversExact 8
    leaf7040Box leaf7040Certificate leaf7040InnerLog leaf7040Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk158RoundedFacts chi353RoundedFacts
    innerPair778RoundedFacts leaf7040RoundedFacts (by rfl)

private theorem leaf7040FlatSound : Sound leaf7040Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7040CertificateValid
    leaf7040InnerLogValid leaf7040CoversExact leaf7040LowerChecked

private noncomputable def leaf7041Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (85/128), chiHi := (43/64) }

private noncomputable def leaf7041Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (134218023/134217728) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34354278400) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (473968087/268435456) }, upper := { exponent := 1, mantissa := (1845/1024) } }, logOuter := sk158LogOuterCertificate, logK := sk158LogKCertificate, logChi := chi354LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68711460859/68708556800) } }, logDArg := sk158LogDArgCertificate }

private noncomputable def leaf7041InnerLog : WideLogData :=
  innerPair778Data

set_option maxRecDepth 1000000 in
private theorem leaf7041LocalValidity :
    LeafFacts leaf7041Box leaf7041Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7041Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34354278400) }) = true
      norm_num [leaf7041Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7041CertificateValid :
    WideCertificateValid leaf7041Box leaf7041Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk158ValidityFacts chi354ValidityFacts
    leaf7041LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7041CoverageChecked :
    coverageCheck (innerAD leaf7041Box) leaf7041InnerLog = true := by
  rfl'

private theorem leaf7041InnerLogValid :
    leaf7041InnerLog.Valid 8 (innerAD leaf7041Box) :=
  wideLogDataValid_of_cachedCheck endpoint489PositiveFacts
    endpoint500PositiveFacts.valid leaf7041CoverageChecked

private noncomputable def leaf7041InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814895/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf7041InputLogOnePlusV_eq :
    leaf7041InputLogOnePlusV = outerEnclosure 24
      (leaf7041Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7041RoundedFacts : LeafRoundedFacts 8
    leaf7041Certificate.logOnePlusV leaf7041InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7041InputLogOnePlusV_eq }

private noncomputable def leaf7041Inputs : Inputs :=
  inputsOfCaches globalInput sk158RoundedInputs
    chi354InputQChi innerPair778Input
    leaf7041InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7041LowerChecked :
    lowerCheck 24 leaf7041Box leaf7041Inputs = true := by
  rfl'

private theorem leaf7041CoversExact : CoversExact 8
    leaf7041Box leaf7041Certificate leaf7041InnerLog leaf7041Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk158RoundedFacts chi354RoundedFacts
    innerPair778RoundedFacts leaf7041RoundedFacts (by rfl)

private theorem leaf7041FlatSound : Sound leaf7041Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7041CertificateValid
    leaf7041InnerLogValid leaf7041CoversExact leaf7041LowerChecked

private noncomputable def leaf7042Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (43/64), chiHi := (87/128) }

private noncomputable def leaf7042Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (134218023/134217728) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34354304000) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (472329787/268435456) }, upper := { exponent := 1, mantissa := (7355/4096) } }, logOuter := sk157LogOuterCertificate, logK := sk157LogKCertificate, logChi := chi355LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68711486459/68708608000) } }, logDArg := sk157LogDArgCertificate }

private noncomputable def leaf7042InnerLog : WideLogData :=
  innerPair778Data

set_option maxRecDepth 1000000 in
private theorem leaf7042LocalValidity :
    LeafFacts leaf7042Box leaf7042Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7042Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34354304000) }) = true
      norm_num [leaf7042Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7042CertificateValid :
    WideCertificateValid leaf7042Box leaf7042Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk157ValidityFacts chi355ValidityFacts
    leaf7042LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7042CoverageChecked :
    coverageCheck (innerAD leaf7042Box) leaf7042InnerLog = true := by
  rfl'

private theorem leaf7042InnerLogValid :
    leaf7042InnerLog.Valid 8 (innerAD leaf7042Box) :=
  wideLogDataValid_of_cachedCheck endpoint489PositiveFacts
    endpoint500PositiveFacts.valid leaf7042CoverageChecked

private noncomputable def leaf7042InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453723/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf7042InputLogOnePlusV_eq :
    leaf7042InputLogOnePlusV = outerEnclosure 24
      (leaf7042Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7042RoundedFacts : LeafRoundedFacts 8
    leaf7042Certificate.logOnePlusV leaf7042InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7042InputLogOnePlusV_eq }

private noncomputable def leaf7042Inputs : Inputs :=
  inputsOfCaches globalInput sk157RoundedInputs
    chi355InputQChi innerPair778Input
    leaf7042InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7042LowerChecked :
    lowerCheck 24 leaf7042Box leaf7042Inputs = true := by
  rfl'

private theorem leaf7042CoversExact : CoversExact 8
    leaf7042Box leaf7042Certificate leaf7042InnerLog leaf7042Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk157RoundedFacts chi355RoundedFacts
    innerPair778RoundedFacts leaf7042RoundedFacts (by rfl)

private theorem leaf7042FlatSound : Sound leaf7042Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7042CertificateValid
    leaf7042InnerLogValid leaf7042CoversExact leaf7042LowerChecked

private noncomputable def leaf7043Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (87/128), chiHi := (11/16) }

private noncomputable def leaf7043Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (134218025/134217728) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34354241536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (476261705/268435456) }, upper := { exponent := 1, mantissa := (927/512) } }, logOuter := sk157LogOuterCertificate, logK := sk157LogKCertificate, logChi := chi356LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68711423995/68708483072) } }, logDArg := sk157LogDArgCertificate }

private noncomputable def leaf7043InnerLog : WideLogData :=
  innerPair778Data

set_option maxRecDepth 1000000 in
private theorem leaf7043LocalValidity :
    LeafFacts leaf7043Box leaf7043Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7043Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34354241536) }) = true
      norm_num [leaf7043Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7043CertificateValid :
    WideCertificateValid leaf7043Box leaf7043Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk157ValidityFacts chi356ValidityFacts
    leaf7043LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7043CoverageChecked :
    coverageCheck (innerAD leaf7043Box) leaf7043InnerLog = true := by
  rfl'

private theorem leaf7043InnerLogValid :
    leaf7043InnerLog.Valid 8 (innerAD leaf7043Box) :=
  wideLogDataValid_of_cachedCheck endpoint489PositiveFacts
    endpoint500PositiveFacts.valid leaf7043CoverageChecked

private noncomputable def leaf7043InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629799/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7043InputLogOnePlusV_eq :
    leaf7043InputLogOnePlusV = outerEnclosure 24
      (leaf7043Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7043RoundedFacts : LeafRoundedFacts 8
    leaf7043Certificate.logOnePlusV leaf7043InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7043InputLogOnePlusV_eq }

private noncomputable def leaf7043Inputs : Inputs :=
  inputsOfCaches globalInput sk157RoundedInputs
    chi356InputQChi innerPair778Input
    leaf7043InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7043LowerChecked :
    lowerCheck 24 leaf7043Box leaf7043Inputs = true := by
  rfl'

private theorem leaf7043CoversExact : CoversExact 8
    leaf7043Box leaf7043Certificate leaf7043InnerLog leaf7043Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk157RoundedFacts chi356RoundedFacts
    innerPair778RoundedFacts leaf7043RoundedFacts (by rfl)

private theorem leaf7043FlatSound : Sound leaf7043Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7043CertificateValid
    leaf7043InnerLogValid leaf7043CoversExact leaf7043LowerChecked

private noncomputable def leaf7044Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (43/64), chiHi := (87/128) }

private noncomputable def leaf7044Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (134218025/134217728) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34354214912) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (477965537/268435456) }, upper := { exponent := 1, mantissa := (3721/2048) } }, logOuter := sk158LogOuterCertificate, logK := sk158LogKCertificate, logChi := chi355LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68711397371/68708429824) } }, logDArg := sk158LogDArgCertificate }

private noncomputable def leaf7044InnerLog : WideLogData :=
  innerPair779Data

set_option maxRecDepth 1000000 in
private theorem leaf7044LocalValidity :
    LeafFacts leaf7044Box leaf7044Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7044Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34354214912) }) = true
      norm_num [leaf7044Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7044CertificateValid :
    WideCertificateValid leaf7044Box leaf7044Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk158ValidityFacts chi355ValidityFacts
    leaf7044LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7044CoverageChecked :
    coverageCheck (innerAD leaf7044Box) leaf7044InnerLog = true := by
  rfl'

private theorem leaf7044InnerLogValid :
    leaf7044InnerLog.Valid 8 (innerAD leaf7044Box) :=
  wideLogDataValid_of_cachedCheck endpoint489PositiveFacts
    endpoint501PositiveFacts.valid leaf7044CoverageChecked

private noncomputable def leaf7044InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629805/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7044InputLogOnePlusV_eq :
    leaf7044InputLogOnePlusV = outerEnclosure 24
      (leaf7044Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7044RoundedFacts : LeafRoundedFacts 8
    leaf7044Certificate.logOnePlusV leaf7044InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7044InputLogOnePlusV_eq }

private noncomputable def leaf7044Inputs : Inputs :=
  inputsOfCaches globalInput sk158RoundedInputs
    chi355InputQChi innerPair779Input
    leaf7044InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7044LowerChecked :
    lowerCheck 24 leaf7044Box leaf7044Inputs = true := by
  rfl'

private theorem leaf7044CoversExact : CoversExact 8
    leaf7044Box leaf7044Certificate leaf7044InnerLog leaf7044Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk158RoundedFacts chi355RoundedFacts
    innerPair779RoundedFacts leaf7044RoundedFacts (by rfl)

private theorem leaf7044FlatSound : Sound leaf7044Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7044CertificateValid
    leaf7044InnerLogValid leaf7044CoversExact leaf7044LowerChecked

private noncomputable def leaf7045Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (87/128), chiHi := (11/16) }

private noncomputable def leaf7045Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (134218027/134217728) }, vSqrt := { lower := (8191/8192), upper := (11452394153/11451383808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (481962987/268435456) }, upper := { exponent := 1, mantissa := (469/256) } }, logOuter := sk158LogOuterCertificate, logK := sk158LogKCertificate, logChi := chi356LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (22903777961/22902767616) } }, logDArg := sk158LogDArgCertificate }

private noncomputable def leaf7045InnerLog : WideLogData :=
  innerPair794Data

set_option maxRecDepth 1000000 in
private theorem leaf7045LocalValidity :
    LeafFacts leaf7045Box leaf7045Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7045Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (11452394153/11451383808) }) = true
      norm_num [leaf7045Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7045CertificateValid :
    WideCertificateValid leaf7045Box leaf7045Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk158ValidityFacts chi356ValidityFacts
    leaf7045LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7045CoverageChecked :
    coverageCheck (innerAD leaf7045Box) leaf7045InnerLog = true := by
  rfl'

private theorem leaf7045InnerLogValid :
    leaf7045InnerLog.Valid 8 (innerAD leaf7045Box) :=
  wideLogDataValid_of_cachedCheck endpoint498PositiveFacts
    endpoint501PositiveFacts.valid leaf7045CoverageChecked

private noncomputable def leaf7045InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629821/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7045InputLogOnePlusV_eq :
    leaf7045InputLogOnePlusV = outerEnclosure 24
      (leaf7045Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7045RoundedFacts : LeafRoundedFacts 8
    leaf7045Certificate.logOnePlusV leaf7045InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7045InputLogOnePlusV_eq }

private noncomputable def leaf7045Inputs : Inputs :=
  inputsOfCaches globalInput sk158RoundedInputs
    chi356InputQChi innerPair794Input
    leaf7045InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7045LowerChecked :
    lowerCheck 24 leaf7045Box leaf7045Inputs = true := by
  rfl'

private theorem leaf7045CoversExact : CoversExact 8
    leaf7045Box leaf7045Certificate leaf7045InnerLog leaf7045Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk158RoundedFacts chi356RoundedFacts
    innerPair794RoundedFacts leaf7045RoundedFacts (by rfl)

private theorem leaf7045FlatSound : Sound leaf7045Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7045CertificateValid
    leaf7045InnerLogValid leaf7045CoversExact leaf7045LowerChecked

private noncomputable def leaf7046Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (21/32), chiHi := (85/128) }

private noncomputable def leaf7046Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (134218023/134217728) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34354254848) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (475475323/268435456) }, upper := { exponent := 1, mantissa := (7403/4096) } }, logOuter := sk159LogOuterCertificate, logK := sk159LogKCertificate, logChi := chi353LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68711437307/68708509696) } }, logDArg := sk159LogDArgCertificate }

private noncomputable def leaf7046InnerLog : WideLogData :=
  innerPair778Data

set_option maxRecDepth 1000000 in
private theorem leaf7046LocalValidity :
    LeafFacts leaf7046Box leaf7046Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7046Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34354254848) }) = true
      norm_num [leaf7046Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7046CertificateValid :
    WideCertificateValid leaf7046Box leaf7046Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk159ValidityFacts chi353ValidityFacts
    leaf7046LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7046CoverageChecked :
    coverageCheck (innerAD leaf7046Box) leaf7046InnerLog = true := by
  rfl'

private theorem leaf7046InnerLogValid :
    leaf7046InnerLog.Valid 8 (innerAD leaf7046Box) :=
  wideLogDataValid_of_cachedCheck endpoint489PositiveFacts
    endpoint500PositiveFacts.valid leaf7046CoverageChecked

private noncomputable def leaf7046InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907449/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf7046InputLogOnePlusV_eq :
    leaf7046InputLogOnePlusV = outerEnclosure 24
      (leaf7046Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7046RoundedFacts : LeafRoundedFacts 8
    leaf7046Certificate.logOnePlusV leaf7046InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7046InputLogOnePlusV_eq }

private noncomputable def leaf7046Inputs : Inputs :=
  inputsOfCaches globalInput sk159RoundedInputs
    chi353InputQChi innerPair778Input
    leaf7046InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7046LowerChecked :
    lowerCheck 24 leaf7046Box leaf7046Inputs = true := by
  rfl'

private theorem leaf7046CoversExact : CoversExact 8
    leaf7046Box leaf7046Certificate leaf7046InnerLog leaf7046Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk159RoundedFacts chi353RoundedFacts
    innerPair778RoundedFacts leaf7046RoundedFacts (by rfl)

private theorem leaf7046FlatSound : Sound leaf7046Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7046CertificateValid
    leaf7046InnerLogValid leaf7046CoversExact leaf7046LowerChecked

private noncomputable def leaf7047Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (85/128), chiHi := (43/64) }

private noncomputable def leaf7047Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (134218025/134217728) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34354190336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (479538305/268435456) }, upper := { exponent := 1, mantissa := (3733/2048) } }, logOuter := sk159LogOuterCertificate, logK := sk159LogKCertificate, logChi := chi354LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68711372795/68708380672) } }, logDArg := sk159LogDArgCertificate }

private noncomputable def leaf7047InnerLog : WideLogData :=
  innerPair794Data

set_option maxRecDepth 1000000 in
private theorem leaf7047LocalValidity :
    LeafFacts leaf7047Box leaf7047Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7047Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34354190336) }) = true
      norm_num [leaf7047Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7047CertificateValid :
    WideCertificateValid leaf7047Box leaf7047Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk159ValidityFacts chi354ValidityFacts
    leaf7047LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7047CoverageChecked :
    coverageCheck (innerAD leaf7047Box) leaf7047InnerLog = true := by
  rfl'

private theorem leaf7047InnerLogValid :
    leaf7047InnerLog.Valid 8 (innerAD leaf7047Box) :=
  wideLogDataValid_of_cachedCheck endpoint498PositiveFacts
    endpoint501PositiveFacts.valid leaf7047CoverageChecked

private noncomputable def leaf7047InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629811/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7047InputLogOnePlusV_eq :
    leaf7047InputLogOnePlusV = outerEnclosure 24
      (leaf7047Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7047RoundedFacts : LeafRoundedFacts 8
    leaf7047Certificate.logOnePlusV leaf7047InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7047InputLogOnePlusV_eq }

private noncomputable def leaf7047Inputs : Inputs :=
  inputsOfCaches globalInput sk159RoundedInputs
    chi354InputQChi innerPair794Input
    leaf7047InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7047LowerChecked :
    lowerCheck 24 leaf7047Box leaf7047Inputs = true := by
  rfl'

private theorem leaf7047CoversExact : CoversExact 8
    leaf7047Box leaf7047Certificate leaf7047InnerLog leaf7047Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk159RoundedFacts chi354RoundedFacts
    innerPair794RoundedFacts leaf7047RoundedFacts (by rfl)

private theorem leaf7047FlatSound : Sound leaf7047Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7047CertificateValid
    leaf7047InnerLogValid leaf7047CoversExact leaf7047LowerChecked

private noncomputable def leaf7048Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (21/32), chiHi := (85/128) }

private noncomputable def leaf7048Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (134218025/134217728) }, vSqrt := { lower := (65527/65536), upper := (34357182459/34354167808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (480980009/268435456) }, upper := { exponent := 1, mantissa := (117/64) } }, logOuter := sk160LogOuterCertificate, logK := sk160LogKCertificate, logChi := chi353LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (68711350267/68708335616) } }, logDArg := sk160LogDArgCertificate }

private noncomputable def leaf7048InnerLog : WideLogData :=
  innerPair794Data

set_option maxRecDepth 1000000 in
private theorem leaf7048LocalValidity :
    LeafFacts leaf7048Box leaf7048Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7048Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (34357182459/34354167808) }) = true
      norm_num [leaf7048Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7048CertificateValid :
    WideCertificateValid leaf7048Box leaf7048Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk160ValidityFacts chi353ValidityFacts
    leaf7048LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7048CoverageChecked :
    coverageCheck (innerAD leaf7048Box) leaf7048InnerLog = true := by
  rfl'

private theorem leaf7048InnerLogValid :
    leaf7048InnerLog.Valid 8 (innerAD leaf7048Box) :=
  wideLogDataValid_of_cachedCheck endpoint498PositiveFacts
    endpoint501PositiveFacts.valid leaf7048CoverageChecked

private noncomputable def leaf7048InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629817/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7048InputLogOnePlusV_eq :
    leaf7048InputLogOnePlusV = outerEnclosure 24
      (leaf7048Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7048RoundedFacts : LeafRoundedFacts 8
    leaf7048Certificate.logOnePlusV leaf7048InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7048InputLogOnePlusV_eq }

private noncomputable def leaf7048Inputs : Inputs :=
  inputsOfCaches globalInput sk160RoundedInputs
    chi353InputQChi innerPair794Input
    leaf7048InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7048LowerChecked :
    lowerCheck 24 leaf7048Box leaf7048Inputs = true := by
  rfl'

private theorem leaf7048CoversExact : CoversExact 8
    leaf7048Box leaf7048Certificate leaf7048InnerLog leaf7048Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk160RoundedFacts chi353RoundedFacts
    innerPair794RoundedFacts leaf7048RoundedFacts (by rfl)

private theorem leaf7048FlatSound : Sound leaf7048Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7048CertificateValid
    leaf7048InnerLogValid leaf7048CoversExact leaf7048LowerChecked

private noncomputable def leaf7049Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (85/128), chiHi := (43/64) }

private noncomputable def leaf7049Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (134218027/134217728) }, vSqrt := { lower := (65527/65536), upper := (11452394153/11451367424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (485108523/268435456) }, upper := { exponent := 1, mantissa := (59/32) } }, logOuter := sk160LogOuterCertificate, logK := sk160LogKCertificate, logChi := chi354LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (22903761577/22902734848) } }, logDArg := sk160LogDArgCertificate }

private noncomputable def leaf7049InnerLog : WideLogData :=
  innerPair794Data

set_option maxRecDepth 1000000 in
private theorem leaf7049LocalValidity :
    LeafFacts leaf7049Box leaf7049Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7049Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (11452394153/11451367424) }) = true
      norm_num [leaf7049Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7049CertificateValid :
    WideCertificateValid leaf7049Box leaf7049Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk160ValidityFacts chi354ValidityFacts
    leaf7049LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7049CoverageChecked :
    coverageCheck (innerAD leaf7049Box) leaf7049InnerLog = true := by
  rfl'

private theorem leaf7049InnerLogValid :
    leaf7049InnerLog.Valid 8 (innerAD leaf7049Box) :=
  wideLogDataValid_of_cachedCheck endpoint498PositiveFacts
    endpoint501PositiveFacts.valid leaf7049CoverageChecked

private noncomputable def leaf7049InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629833/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7049InputLogOnePlusV_eq :
    leaf7049InputLogOnePlusV = outerEnclosure 24
      (leaf7049Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7049RoundedFacts : LeafRoundedFacts 8
    leaf7049Certificate.logOnePlusV leaf7049InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7049InputLogOnePlusV_eq }

private noncomputable def leaf7049Inputs : Inputs :=
  inputsOfCaches globalInput sk160RoundedInputs
    chi354InputQChi innerPair794Input
    leaf7049InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7049LowerChecked :
    lowerCheck 24 leaf7049Box leaf7049Inputs = true := by
  rfl'

private theorem leaf7049CoversExact : CoversExact 8
    leaf7049Box leaf7049Certificate leaf7049InnerLog leaf7049Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk160RoundedFacts chi354RoundedFacts
    innerPair794RoundedFacts leaf7049RoundedFacts (by rfl)

private theorem leaf7049FlatSound : Sound leaf7049Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7049CertificateValid
    leaf7049InnerLogValid leaf7049CoversExact leaf7049LowerChecked

private noncomputable def leaf7050Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (43/64), chiHi := (87/128) }

private noncomputable def leaf7050Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (134218027/134217728) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34354125824) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (483601287/268435456) }, upper := { exponent := 1, mantissa := (7529/4096) } }, logOuter := sk159LogOuterCertificate, logK := sk159LogKCertificate, logChi := chi355LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68711308283/68708251648) } }, logDArg := sk159LogDArgCertificate }

private noncomputable def leaf7050InnerLog : WideLogData :=
  innerPair794Data

set_option maxRecDepth 1000000 in
private theorem leaf7050LocalValidity :
    LeafFacts leaf7050Box leaf7050Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7050Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34354125824) }) = true
      norm_num [leaf7050Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7050CertificateValid :
    WideCertificateValid leaf7050Box leaf7050Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk159ValidityFacts chi355ValidityFacts
    leaf7050LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7050CoverageChecked :
    coverageCheck (innerAD leaf7050Box) leaf7050InnerLog = true := by
  rfl'

private theorem leaf7050InnerLogValid :
    leaf7050InnerLog.Valid 8 (innerAD leaf7050Box) :=
  wideLogDataValid_of_cachedCheck endpoint498PositiveFacts
    endpoint501PositiveFacts.valid leaf7050CoverageChecked

private noncomputable def leaf7050InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629827/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7050InputLogOnePlusV_eq :
    leaf7050InputLogOnePlusV = outerEnclosure 24
      (leaf7050Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7050RoundedFacts : LeafRoundedFacts 8
    leaf7050Certificate.logOnePlusV leaf7050InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7050InputLogOnePlusV_eq }

private noncomputable def leaf7050Inputs : Inputs :=
  inputsOfCaches globalInput sk159RoundedInputs
    chi355InputQChi innerPair794Input
    leaf7050InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7050LowerChecked :
    lowerCheck 24 leaf7050Box leaf7050Inputs = true := by
  rfl'

private theorem leaf7050CoversExact : CoversExact 8
    leaf7050Box leaf7050Certificate leaf7050InnerLog leaf7050Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk159RoundedFacts chi355RoundedFacts
    innerPair794RoundedFacts leaf7050RoundedFacts (by rfl)

private theorem leaf7050FlatSound : Sound leaf7050Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7050CertificateValid
    leaf7050InnerLogValid leaf7050CoversExact leaf7050LowerChecked

private noncomputable def leaf7051Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (87/128), chiHi := (11/16) }

private noncomputable def leaf7051Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (134218029/134217728) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34354061312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (487664269/268435456) }, upper := { exponent := 1, mantissa := (949/512) } }, logOuter := sk159LogOuterCertificate, logK := sk159LogKCertificate, logChi := chi356LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68711243771/68708122624) } }, logDArg := sk159LogDArgCertificate }

private noncomputable def leaf7051InnerLog : WideLogData :=
  innerPair798Data

set_option maxRecDepth 1000000 in
private theorem leaf7051LocalValidity :
    LeafFacts leaf7051Box leaf7051Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7051Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34354061312) }) = true
      norm_num [leaf7051Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7051CertificateValid :
    WideCertificateValid leaf7051Box leaf7051Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk159ValidityFacts chi356ValidityFacts
    leaf7051LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7051CoverageChecked :
    coverageCheck (innerAD leaf7051Box) leaf7051InnerLog = true := by
  rfl'

private theorem leaf7051InnerLogValid :
    leaf7051InnerLog.Valid 8 (innerAD leaf7051Box) :=
  wideLogDataValid_of_cachedCheck endpoint500PositiveFacts
    endpoint502PositiveFacts.valid leaf7051CoverageChecked

private noncomputable def leaf7051InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629843/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7051InputLogOnePlusV_eq :
    leaf7051InputLogOnePlusV = outerEnclosure 24
      (leaf7051Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7051RoundedFacts : LeafRoundedFacts 8
    leaf7051Certificate.logOnePlusV leaf7051InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7051InputLogOnePlusV_eq }

private noncomputable def leaf7051Inputs : Inputs :=
  inputsOfCaches globalInput sk159RoundedInputs
    chi356InputQChi innerPair798Input
    leaf7051InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7051LowerChecked :
    lowerCheck 24 leaf7051Box leaf7051Inputs = true := by
  rfl'

private theorem leaf7051CoversExact : CoversExact 8
    leaf7051Box leaf7051Certificate leaf7051InnerLog leaf7051Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk159RoundedFacts chi356RoundedFacts
    innerPair798RoundedFacts leaf7051RoundedFacts (by rfl)

private theorem leaf7051FlatSound : Sound leaf7051Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7051CertificateValid
    leaf7051InnerLogValid leaf7051CoversExact leaf7051LowerChecked

private noncomputable def leaf7052Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (43/64), chiHi := (87/128) }

private noncomputable def leaf7052Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (134218029/134217728) }, vSqrt := { lower := (65527/65536), upper := (34357182459/34354036736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (489237037/268435456) }, upper := { exponent := 1, mantissa := (119/64) } }, logOuter := sk160LogOuterCertificate, logK := sk160LogKCertificate, logChi := chi355LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (68711219195/68708073472) } }, logDArg := sk160LogDArgCertificate }

private noncomputable def leaf7052InnerLog : WideLogData :=
  innerPair798Data

set_option maxRecDepth 1000000 in
private theorem leaf7052LocalValidity :
    LeafFacts leaf7052Box leaf7052Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7052Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (34357182459/34354036736) }) = true
      norm_num [leaf7052Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7052CertificateValid :
    WideCertificateValid leaf7052Box leaf7052Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk160ValidityFacts chi355ValidityFacts
    leaf7052LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7052CoverageChecked :
    coverageCheck (innerAD leaf7052Box) leaf7052InnerLog = true := by
  rfl'

private theorem leaf7052InnerLogValid :
    leaf7052InnerLog.Valid 8 (innerAD leaf7052Box) :=
  wideLogDataValid_of_cachedCheck endpoint500PositiveFacts
    endpoint502PositiveFacts.valid leaf7052CoverageChecked

private noncomputable def leaf7052InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629849/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7052InputLogOnePlusV_eq :
    leaf7052InputLogOnePlusV = outerEnclosure 24
      (leaf7052Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7052RoundedFacts : LeafRoundedFacts 8
    leaf7052Certificate.logOnePlusV leaf7052InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7052InputLogOnePlusV_eq }

private noncomputable def leaf7052Inputs : Inputs :=
  inputsOfCaches globalInput sk160RoundedInputs
    chi355InputQChi innerPair798Input
    leaf7052InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7052LowerChecked :
    lowerCheck 24 leaf7052Box leaf7052Inputs = true := by
  rfl'

private theorem leaf7052CoversExact : CoversExact 8
    leaf7052Box leaf7052Certificate leaf7052InnerLog leaf7052Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk160RoundedFacts chi355RoundedFacts
    innerPair798RoundedFacts leaf7052RoundedFacts (by rfl)

private theorem leaf7052FlatSound : Sound leaf7052Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7052CertificateValid
    leaf7052InnerLogValid leaf7052CoversExact leaf7052LowerChecked

private noncomputable def leaf7053Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (87/128), chiHi := (11/16) }

private noncomputable def leaf7053Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (134218031/134217728) }, vSqrt := { lower := (65527/65536), upper := (34357182459/34353971200) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (493365551/268435456) }, upper := { exponent := 1, mantissa := (15/8) } }, logOuter := sk160LogOuterCertificate, logK := sk160LogKCertificate, logChi := chi356LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (68711153659/68707942400) } }, logDArg := sk160LogDArgCertificate }

private noncomputable def leaf7053InnerLog : WideLogData :=
  innerPair798Data

set_option maxRecDepth 1000000 in
private theorem leaf7053LocalValidity :
    LeafFacts leaf7053Box leaf7053Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7053Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (34357182459/34353971200) }) = true
      norm_num [leaf7053Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7053CertificateValid :
    WideCertificateValid leaf7053Box leaf7053Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk160ValidityFacts chi356ValidityFacts
    leaf7053LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7053CoverageChecked :
    coverageCheck (innerAD leaf7053Box) leaf7053InnerLog = true := by
  rfl'

private theorem leaf7053InnerLogValid :
    leaf7053InnerLog.Valid 8 (innerAD leaf7053Box) :=
  wideLogDataValid_of_cachedCheck endpoint500PositiveFacts
    endpoint502PositiveFacts.valid leaf7053CoverageChecked

private noncomputable def leaf7053InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629865/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7053InputLogOnePlusV_eq :
    leaf7053InputLogOnePlusV = outerEnclosure 24
      (leaf7053Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7053RoundedFacts : LeafRoundedFacts 8
    leaf7053Certificate.logOnePlusV leaf7053InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7053InputLogOnePlusV_eq }

private noncomputable def leaf7053Inputs : Inputs :=
  inputsOfCaches globalInput sk160RoundedInputs
    chi356InputQChi innerPair798Input
    leaf7053InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7053LowerChecked :
    lowerCheck 24 leaf7053Box leaf7053Inputs = true := by
  rfl'

private theorem leaf7053CoversExact : CoversExact 8
    leaf7053Box leaf7053Certificate leaf7053InnerLog leaf7053Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk160RoundedFacts chi356RoundedFacts
    innerPair798RoundedFacts leaf7053RoundedFacts (by rfl)

private theorem leaf7053FlatSound : Sound leaf7053Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7053CertificateValid
    leaf7053InnerLogValid leaf7053CoversExact leaf7053LowerChecked

private noncomputable def leaf7054Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (11/16), chiHi := (89/128) }

private noncomputable def leaf7054Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (134218027/134217728) }, vSqrt := { lower := (8191/8192), upper := (602757587/602704896) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (480193623/268435456) }, upper := { exponent := 1, mantissa := (7477/4096) } }, logOuter := sk157LogOuterCertificate, logK := sk157LogKCertificate, logChi := chi357LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (1205462483/1205409792) } }, logDArg := sk157LogDArgCertificate }

private noncomputable def leaf7054InnerLog : WideLogData :=
  innerPair794Data

set_option maxRecDepth 1000000 in
private theorem leaf7054LocalValidity :
    LeafFacts leaf7054Box leaf7054Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7054Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (602757587/602704896) }) = true
      norm_num [leaf7054Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7054CertificateValid :
    WideCertificateValid leaf7054Box leaf7054Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk157ValidityFacts chi357ValidityFacts
    leaf7054LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7054CoverageChecked :
    coverageCheck (innerAD leaf7054Box) leaf7054InnerLog = true := by
  rfl'

private theorem leaf7054InnerLogValid :
    leaf7054InnerLog.Valid 8 (innerAD leaf7054Box) :=
  wideLogDataValid_of_cachedCheck endpoint498PositiveFacts
    endpoint501PositiveFacts.valid leaf7054CoverageChecked

private noncomputable def leaf7054InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814907/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf7054InputLogOnePlusV_eq :
    leaf7054InputLogOnePlusV = outerEnclosure 24
      (leaf7054Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7054RoundedFacts : LeafRoundedFacts 8
    leaf7054Certificate.logOnePlusV leaf7054InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7054InputLogOnePlusV_eq }

private noncomputable def leaf7054Inputs : Inputs :=
  inputsOfCaches globalInput sk157RoundedInputs
    chi357InputQChi innerPair794Input
    leaf7054InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7054LowerChecked :
    lowerCheck 24 leaf7054Box leaf7054Inputs = true := by
  rfl'

private theorem leaf7054CoversExact : CoversExact 8
    leaf7054Box leaf7054Certificate leaf7054InnerLog leaf7054Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk157RoundedFacts chi357RoundedFacts
    innerPair794RoundedFacts leaf7054RoundedFacts (by rfl)

private theorem leaf7054FlatSound : Sound leaf7054Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7054CertificateValid
    leaf7054InnerLogValid leaf7054CoversExact leaf7054LowerChecked

private noncomputable def leaf7055Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (89/128), chiHi := (45/64) }

private noncomputable def leaf7055Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (134218029/134217728) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34354116608) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (484125541/268435456) }, upper := { exponent := 1, mantissa := (3769/2048) } }, logOuter := sk157LogOuterCertificate, logK := sk157LogKCertificate, logChi := chi358LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68711299067/68708233216) } }, logDArg := sk157LogDArgCertificate }

private noncomputable def leaf7055InnerLog : WideLogData :=
  innerPair794Data

set_option maxRecDepth 1000000 in
private theorem leaf7055LocalValidity :
    LeafFacts leaf7055Box leaf7055Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7055Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34354116608) }) = true
      norm_num [leaf7055Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7055CertificateValid :
    WideCertificateValid leaf7055Box leaf7055Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk157ValidityFacts chi358ValidityFacts
    leaf7055LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7055CoverageChecked :
    coverageCheck (innerAD leaf7055Box) leaf7055InnerLog = true := by
  rfl'

private theorem leaf7055InnerLogValid :
    leaf7055InnerLog.Valid 8 (innerAD leaf7055Box) :=
  wideLogDataValid_of_cachedCheck endpoint498PositiveFacts
    endpoint501PositiveFacts.valid leaf7055CoverageChecked

private noncomputable def leaf7055InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629829/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7055InputLogOnePlusV_eq :
    leaf7055InputLogOnePlusV = outerEnclosure 24
      (leaf7055Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7055RoundedFacts : LeafRoundedFacts 8
    leaf7055Certificate.logOnePlusV leaf7055InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7055InputLogOnePlusV_eq }

private noncomputable def leaf7055Inputs : Inputs :=
  inputsOfCaches globalInput sk157RoundedInputs
    chi358InputQChi innerPair794Input
    leaf7055InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7055LowerChecked :
    lowerCheck 24 leaf7055Box leaf7055Inputs = true := by
  rfl'

private theorem leaf7055CoversExact : CoversExact 8
    leaf7055Box leaf7055Certificate leaf7055InnerLog leaf7055Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk157RoundedFacts chi358RoundedFacts
    innerPair794RoundedFacts leaf7055RoundedFacts (by rfl)

private theorem leaf7055FlatSound : Sound leaf7055Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7055CertificateValid
    leaf7055InnerLogValid leaf7055CoversExact leaf7055LowerChecked

private noncomputable def leaf7056Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (11/16), chiHi := (89/128) }

private noncomputable def leaf7056Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (134218029/134217728) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34354087936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (485960437/268435456) }, upper := { exponent := 1, mantissa := (3783/2048) } }, logOuter := sk158LogOuterCertificate, logK := sk158LogKCertificate, logChi := chi357LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68711270395/68708175872) } }, logDArg := sk158LogDArgCertificate }

private noncomputable def leaf7056InnerLog : WideLogData :=
  innerPair795Data

set_option maxRecDepth 1000000 in
private theorem leaf7056LocalValidity :
    LeafFacts leaf7056Box leaf7056Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7056Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34354087936) }) = true
      norm_num [leaf7056Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7056CertificateValid :
    WideCertificateValid leaf7056Box leaf7056Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk158ValidityFacts chi357ValidityFacts
    leaf7056LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7056CoverageChecked :
    coverageCheck (innerAD leaf7056Box) leaf7056InnerLog = true := by
  rfl'

private theorem leaf7056InnerLogValid :
    leaf7056InnerLog.Valid 8 (innerAD leaf7056Box) :=
  wideLogDataValid_of_cachedCheck endpoint498PositiveFacts
    endpoint502PositiveFacts.valid leaf7056CoverageChecked

private noncomputable def leaf7056InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907459/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf7056InputLogOnePlusV_eq :
    leaf7056InputLogOnePlusV = outerEnclosure 24
      (leaf7056Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7056RoundedFacts : LeafRoundedFacts 8
    leaf7056Certificate.logOnePlusV leaf7056InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7056InputLogOnePlusV_eq }

private noncomputable def leaf7056Inputs : Inputs :=
  inputsOfCaches globalInput sk158RoundedInputs
    chi357InputQChi innerPair795Input
    leaf7056InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7056LowerChecked :
    lowerCheck 24 leaf7056Box leaf7056Inputs = true := by
  rfl'

private theorem leaf7056CoversExact : CoversExact 8
    leaf7056Box leaf7056Certificate leaf7056InnerLog leaf7056Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk158RoundedFacts chi357RoundedFacts
    innerPair795RoundedFacts leaf7056RoundedFacts (by rfl)

private theorem leaf7056FlatSound : Sound leaf7056Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7056CertificateValid
    leaf7056InnerLogValid leaf7056CoversExact leaf7056LowerChecked

private noncomputable def leaf7057Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (89/128), chiHi := (45/64) }

private noncomputable def leaf7057Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (134218031/134217728) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34354024448) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (489957887/268435456) }, upper := { exponent := 1, mantissa := (1907/1024) } }, logOuter := sk158LogOuterCertificate, logK := sk158LogKCertificate, logChi := chi358LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68711206907/68708048896) } }, logDArg := sk158LogDArgCertificate }

private noncomputable def leaf7057InnerLog : WideLogData :=
  innerPair798Data

set_option maxRecDepth 1000000 in
private theorem leaf7057LocalValidity :
    LeafFacts leaf7057Box leaf7057Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7057Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34354024448) }) = true
      norm_num [leaf7057Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7057CertificateValid :
    WideCertificateValid leaf7057Box leaf7057Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk158ValidityFacts chi358ValidityFacts
    leaf7057LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7057CoverageChecked :
    coverageCheck (innerAD leaf7057Box) leaf7057InnerLog = true := by
  rfl'

private theorem leaf7057InnerLogValid :
    leaf7057InnerLog.Valid 8 (innerAD leaf7057Box) :=
  wideLogDataValid_of_cachedCheck endpoint500PositiveFacts
    endpoint502PositiveFacts.valid leaf7057CoverageChecked

private noncomputable def leaf7057InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907463/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf7057InputLogOnePlusV_eq :
    leaf7057InputLogOnePlusV = outerEnclosure 24
      (leaf7057Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7057RoundedFacts : LeafRoundedFacts 8
    leaf7057Certificate.logOnePlusV leaf7057InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7057InputLogOnePlusV_eq }

private noncomputable def leaf7057Inputs : Inputs :=
  inputsOfCaches globalInput sk158RoundedInputs
    chi358InputQChi innerPair798Input
    leaf7057InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7057LowerChecked :
    lowerCheck 24 leaf7057Box leaf7057Inputs = true := by
  rfl'

private theorem leaf7057CoversExact : CoversExact 8
    leaf7057Box leaf7057Certificate leaf7057InnerLog leaf7057Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk158RoundedFacts chi358RoundedFacts
    innerPair798RoundedFacts leaf7057RoundedFacts (by rfl)

private theorem leaf7057FlatSound : Sound leaf7057Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7057CertificateValid
    leaf7057InnerLogValid leaf7057CoversExact leaf7057LowerChecked

private noncomputable def leaf7058Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (45/64), chiHi := (23/32) }

private noncomputable def leaf7058Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109077/67108864) }, vSqrt := { lower := (8191/8192), upper := (11452394153/11451330560) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (244012285/134217728) }, upper := { exponent := 1, mantissa := (1915/1024) } }, logOuter := sk157LogOuterCertificate, logK := sk157LogKCertificate, logChi := chi342LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (22903724713/22902661120) } }, logDArg := sk157LogDArgCertificate }

private noncomputable def leaf7058InnerLog : WideLogData :=
  innerPair798Data

set_option maxRecDepth 1000000 in
private theorem leaf7058LocalValidity :
    LeafFacts leaf7058Box leaf7058Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7058Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (11452394153/11451330560) }) = true
      norm_num [leaf7058Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7058CertificateValid :
    WideCertificateValid leaf7058Box leaf7058Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk157ValidityFacts chi342ValidityFacts
    leaf7058LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7058CoverageChecked :
    coverageCheck (innerAD leaf7058Box) leaf7058InnerLog = true := by
  rfl'

private theorem leaf7058InnerLogValid :
    leaf7058InnerLog.Valid 8 (innerAD leaf7058Box) :=
  wideLogDataValid_of_cachedCheck endpoint500PositiveFacts
    endpoint502PositiveFacts.valid leaf7058CoverageChecked

private noncomputable def leaf7058InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907465/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf7058InputLogOnePlusV_eq :
    leaf7058InputLogOnePlusV = outerEnclosure 24
      (leaf7058Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7058RoundedFacts : LeafRoundedFacts 8
    leaf7058Certificate.logOnePlusV leaf7058InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7058InputLogOnePlusV_eq }

private noncomputable def leaf7058Inputs : Inputs :=
  inputsOfCaches globalInput sk157RoundedInputs
    chi342InputQChi innerPair798Input
    leaf7058InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7058LowerChecked :
    lowerCheck 24 leaf7058Box leaf7058Inputs = true := by
  rfl'

private theorem leaf7058CoversExact : CoversExact 8
    leaf7058Box leaf7058Certificate leaf7058InnerLog leaf7058Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk157RoundedFacts chi342RoundedFacts
    innerPair798RoundedFacts leaf7058RoundedFacts (by rfl)

private theorem leaf7058FlatSound : Sound leaf7058Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7058CertificateValid
    leaf7058InnerLogValid leaf7058CoversExact leaf7058LowerChecked

private noncomputable def leaf7059Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (45/64), chiHi := (23/32) }

private noncomputable def leaf7059Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109079/67108864) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34353897472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (246961223/134217728) }, upper := { exponent := 1, mantissa := (969/512) } }, logOuter := sk158LogOuterCertificate, logK := sk158LogKCertificate, logChi := chi342LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68711079931/68707794944) } }, logDArg := sk158LogDArgCertificate }

private noncomputable def leaf7059InnerLog : WideLogData :=
  innerPair860Data

set_option maxRecDepth 1000000 in
private theorem leaf7059LocalValidity :
    LeafFacts leaf7059Box leaf7059Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7059Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34353897472) }) = true
      norm_num [leaf7059Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7059CertificateValid :
    WideCertificateValid leaf7059Box leaf7059Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk158ValidityFacts chi342ValidityFacts
    leaf7059LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7059CoverageChecked :
    coverageCheck (innerAD leaf7059Box) leaf7059InnerLog = true := by
  rfl'

private theorem leaf7059InnerLogValid :
    leaf7059InnerLog.Valid 8 (innerAD leaf7059Box) :=
  wideLogDataValid_of_cachedCheck endpoint570PositiveFacts
    endpoint571PositiveFacts.valid leaf7059CoverageChecked

private noncomputable def leaf7059InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629883/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7059InputLogOnePlusV_eq :
    leaf7059InputLogOnePlusV = outerEnclosure 24
      (leaf7059Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7059RoundedFacts : LeafRoundedFacts 8
    leaf7059Certificate.logOnePlusV leaf7059InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7059InputLogOnePlusV_eq }

private noncomputable def leaf7059Inputs : Inputs :=
  inputsOfCaches globalInput sk158RoundedInputs
    chi342InputQChi innerPair860Input
    leaf7059InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7059LowerChecked :
    lowerCheck 24 leaf7059Box leaf7059Inputs = true := by
  rfl'

private theorem leaf7059CoversExact : CoversExact 8
    leaf7059Box leaf7059Certificate leaf7059InnerLog leaf7059Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk158RoundedFacts chi342RoundedFacts
    innerPair860RoundedFacts leaf7059RoundedFacts (by rfl)

private theorem leaf7059FlatSound : Sound leaf7059Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7059CertificateValid
    leaf7059InnerLogValid leaf7059CoversExact leaf7059LowerChecked

private noncomputable def leaf7060Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (11/16), chiHi := (89/128) }

private noncomputable def leaf7060Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (134218031/134217728) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34353996800) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (491727251/268435456) }, upper := { exponent := 1, mantissa := (7655/4096) } }, logOuter := sk159LogOuterCertificate, logK := sk159LogKCertificate, logChi := chi357LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68711179259/68707993600) } }, logDArg := sk159LogDArgCertificate }

private noncomputable def leaf7060InnerLog : WideLogData :=
  innerPair798Data

set_option maxRecDepth 1000000 in
private theorem leaf7060LocalValidity :
    LeafFacts leaf7060Box leaf7060Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7060Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34353996800) }) = true
      norm_num [leaf7060Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7060CertificateValid :
    WideCertificateValid leaf7060Box leaf7060Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk159ValidityFacts chi357ValidityFacts
    leaf7060LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7060CoverageChecked :
    coverageCheck (innerAD leaf7060Box) leaf7060InnerLog = true := by
  rfl'

private theorem leaf7060InnerLogValid :
    leaf7060InnerLog.Valid 8 (innerAD leaf7060Box) :=
  wideLogDataValid_of_cachedCheck endpoint500PositiveFacts
    endpoint502PositiveFacts.valid leaf7060CoverageChecked

private noncomputable def leaf7060InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629859/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7060InputLogOnePlusV_eq :
    leaf7060InputLogOnePlusV = outerEnclosure 24
      (leaf7060Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7060RoundedFacts : LeafRoundedFacts 8
    leaf7060Certificate.logOnePlusV leaf7060InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7060InputLogOnePlusV_eq }

private noncomputable def leaf7060Inputs : Inputs :=
  inputsOfCaches globalInput sk159RoundedInputs
    chi357InputQChi innerPair798Input
    leaf7060InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7060LowerChecked :
    lowerCheck 24 leaf7060Box leaf7060Inputs = true := by
  rfl'

private theorem leaf7060CoversExact : CoversExact 8
    leaf7060Box leaf7060Certificate leaf7060InnerLog leaf7060Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk159RoundedFacts chi357RoundedFacts
    innerPair798RoundedFacts leaf7060RoundedFacts (by rfl)

private theorem leaf7060FlatSound : Sound leaf7060Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7060CertificateValid
    leaf7060InnerLogValid leaf7060CoversExact leaf7060LowerChecked

private noncomputable def leaf7061Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (89/128), chiHi := (45/64) }

private noncomputable def leaf7061Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (134218033/134217728) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34353932288) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (495790233/268435456) }, upper := { exponent := 1, mantissa := (3859/2048) } }, logOuter := sk159LogOuterCertificate, logK := sk159LogKCertificate, logChi := chi358LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68711114747/68707864576) } }, logDArg := sk159LogDArgCertificate }

private noncomputable def leaf7061InnerLog : WideLogData :=
  innerPair801Data

set_option maxRecDepth 1000000 in
private theorem leaf7061LocalValidity :
    LeafFacts leaf7061Box leaf7061Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7061Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34353932288) }) = true
      norm_num [leaf7061Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7061CertificateValid :
    WideCertificateValid leaf7061Box leaf7061Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk159ValidityFacts chi358ValidityFacts
    leaf7061LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7061CoverageChecked :
    coverageCheck (innerAD leaf7061Box) leaf7061InnerLog = true := by
  rfl'

private theorem leaf7061InnerLogValid :
    leaf7061InnerLog.Valid 8 (innerAD leaf7061Box) :=
  wideLogDataValid_of_cachedCheck endpoint501PositiveFacts
    endpoint503PositiveFacts.valid leaf7061CoverageChecked

private noncomputable def leaf7061InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814937/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf7061InputLogOnePlusV_eq :
    leaf7061InputLogOnePlusV = outerEnclosure 24
      (leaf7061Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7061RoundedFacts : LeafRoundedFacts 8
    leaf7061Certificate.logOnePlusV leaf7061InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7061InputLogOnePlusV_eq }

private noncomputable def leaf7061Inputs : Inputs :=
  inputsOfCaches globalInput sk159RoundedInputs
    chi358InputQChi innerPair801Input
    leaf7061InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7061LowerChecked :
    lowerCheck 24 leaf7061Box leaf7061Inputs = true := by
  rfl'

private theorem leaf7061CoversExact : CoversExact 8
    leaf7061Box leaf7061Certificate leaf7061InnerLog leaf7061Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk159RoundedFacts chi358RoundedFacts
    innerPair801RoundedFacts leaf7061RoundedFacts (by rfl)

private theorem leaf7061FlatSound : Sound leaf7061Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7061CertificateValid
    leaf7061InnerLogValid leaf7061CoversExact leaf7061LowerChecked

private noncomputable def leaf7062Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (11/16), chiHi := (89/128) }

private noncomputable def leaf7062Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (134218033/134217728) }, vSqrt := { lower := (65527/65536), upper := (11452394153/11451301888) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (497494065/268435456) }, upper := { exponent := 1, mantissa := (121/64) } }, logOuter := sk160LogOuterCertificate, logK := sk160LogKCertificate, logChi := chi357LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (22903696041/22902603776) } }, logDArg := sk160LogDArgCertificate }

private noncomputable def leaf7062InnerLog : WideLogData :=
  innerPair801Data

set_option maxRecDepth 1000000 in
private theorem leaf7062LocalValidity :
    LeafFacts leaf7062Box leaf7062Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7062Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (11452394153/11451301888) }) = true
      norm_num [leaf7062Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7062CertificateValid :
    WideCertificateValid leaf7062Box leaf7062Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk160ValidityFacts chi357ValidityFacts
    leaf7062LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7062CoverageChecked :
    coverageCheck (innerAD leaf7062Box) leaf7062InnerLog = true := by
  rfl'

private theorem leaf7062InnerLogValid :
    leaf7062InnerLog.Valid 8 (innerAD leaf7062Box) :=
  wideLogDataValid_of_cachedCheck endpoint501PositiveFacts
    endpoint503PositiveFacts.valid leaf7062CoverageChecked

private noncomputable def leaf7062InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629881/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7062InputLogOnePlusV_eq :
    leaf7062InputLogOnePlusV = outerEnclosure 24
      (leaf7062Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7062RoundedFacts : LeafRoundedFacts 8
    leaf7062Certificate.logOnePlusV leaf7062InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7062InputLogOnePlusV_eq }

private noncomputable def leaf7062Inputs : Inputs :=
  inputsOfCaches globalInput sk160RoundedInputs
    chi357InputQChi innerPair801Input
    leaf7062InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7062LowerChecked :
    lowerCheck 24 leaf7062Box leaf7062Inputs = true := by
  rfl'

private theorem leaf7062CoversExact : CoversExact 8
    leaf7062Box leaf7062Certificate leaf7062InnerLog leaf7062Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk160RoundedFacts chi357RoundedFacts
    innerPair801RoundedFacts leaf7062RoundedFacts (by rfl)

private theorem leaf7062FlatSound : Sound leaf7062Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7062CertificateValid
    leaf7062InnerLogValid leaf7062CoversExact leaf7062LowerChecked

private noncomputable def leaf7063Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (89/128), chiHi := (45/64) }

private noncomputable def leaf7063Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (134218035/134217728) }, vSqrt := { lower := (65527/65536), upper := (34357182459/34353840128) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (501622579/268435456) }, upper := { exponent := 1, mantissa := (61/32) } }, logOuter := sk160LogOuterCertificate, logK := sk160LogKCertificate, logChi := chi358LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (68711022587/68707680256) } }, logDArg := sk160LogDArgCertificate }

private noncomputable def leaf7063InnerLog : WideLogData :=
  innerPair801Data

set_option maxRecDepth 1000000 in
private theorem leaf7063LocalValidity :
    LeafFacts leaf7063Box leaf7063Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7063Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (34357182459/34353840128) }) = true
      norm_num [leaf7063Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7063CertificateValid :
    WideCertificateValid leaf7063Box leaf7063Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk160ValidityFacts chi358ValidityFacts
    leaf7063LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7063CoverageChecked :
    coverageCheck (innerAD leaf7063Box) leaf7063InnerLog = true := by
  rfl'

private theorem leaf7063InnerLogValid :
    leaf7063InnerLog.Valid 8 (innerAD leaf7063Box) :=
  wideLogDataValid_of_cachedCheck endpoint501PositiveFacts
    endpoint503PositiveFacts.valid leaf7063CoverageChecked

private noncomputable def leaf7063InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629897/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7063InputLogOnePlusV_eq :
    leaf7063InputLogOnePlusV = outerEnclosure 24
      (leaf7063Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7063RoundedFacts : LeafRoundedFacts 8
    leaf7063Certificate.logOnePlusV leaf7063InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7063InputLogOnePlusV_eq }

private noncomputable def leaf7063Inputs : Inputs :=
  inputsOfCaches globalInput sk160RoundedInputs
    chi358InputQChi innerPair801Input
    leaf7063InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7063LowerChecked :
    lowerCheck 24 leaf7063Box leaf7063Inputs = true := by
  rfl'

private theorem leaf7063CoversExact : CoversExact 8
    leaf7063Box leaf7063Certificate leaf7063InnerLog leaf7063Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk160RoundedFacts chi358RoundedFacts
    innerPair801RoundedFacts leaf7063RoundedFacts (by rfl)

private theorem leaf7063FlatSound : Sound leaf7063Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7063CertificateValid
    leaf7063InnerLogValid leaf7063CoversExact leaf7063LowerChecked

private noncomputable def leaf7064Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (45/64), chiHi := (91/128) }

private noncomputable def leaf7064Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (134218035/134217728) }, vSqrt := { lower := (8191/8192), upper := (1808272761/1808098304) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (499853215/268435456) }, upper := { exponent := 1, mantissa := (7781/4096) } }, logOuter := sk159LogOuterCertificate, logK := sk159LogKCertificate, logChi := chi359LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (3616371065/3616196608) } }, logDArg := sk159LogDArgCertificate }

private noncomputable def leaf7064InnerLog : WideLogData :=
  innerPair801Data

set_option maxRecDepth 1000000 in
private theorem leaf7064LocalValidity :
    LeafFacts leaf7064Box leaf7064Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7064Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (1808272761/1808098304) }) = true
      norm_num [leaf7064Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7064CertificateValid :
    WideCertificateValid leaf7064Box leaf7064Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk159ValidityFacts chi359ValidityFacts
    leaf7064LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7064CoverageChecked :
    coverageCheck (innerAD leaf7064Box) leaf7064InnerLog = true := by
  rfl'

private theorem leaf7064InnerLogValid :
    leaf7064InnerLog.Valid 8 (innerAD leaf7064Box) :=
  wideLogDataValid_of_cachedCheck endpoint501PositiveFacts
    endpoint503PositiveFacts.valid leaf7064CoverageChecked

private noncomputable def leaf7064InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814945/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf7064InputLogOnePlusV_eq :
    leaf7064InputLogOnePlusV = outerEnclosure 24
      (leaf7064Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7064RoundedFacts : LeafRoundedFacts 8
    leaf7064Certificate.logOnePlusV leaf7064InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7064InputLogOnePlusV_eq }

private noncomputable def leaf7064Inputs : Inputs :=
  inputsOfCaches globalInput sk159RoundedInputs
    chi359InputQChi innerPair801Input
    leaf7064InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7064LowerChecked :
    lowerCheck 24 leaf7064Box leaf7064Inputs = true := by
  rfl'

private theorem leaf7064CoversExact : CoversExact 8
    leaf7064Box leaf7064Certificate leaf7064InnerLog leaf7064Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk159RoundedFacts chi359RoundedFacts
    innerPair801RoundedFacts leaf7064RoundedFacts (by rfl)

private theorem leaf7064FlatSound : Sound leaf7064Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7064CertificateValid
    leaf7064InnerLogValid leaf7064CoversExact leaf7064LowerChecked

private noncomputable def leaf7065Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (91/128), chiHi := (23/32) }

private noncomputable def leaf7065Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (134218037/134217728) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34353803264) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (503916197/268435456) }, upper := { exponent := 1, mantissa := (1961/1024) } }, logOuter := sk159LogOuterCertificate, logK := sk159LogKCertificate, logChi := chi360LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68710985723/68707606528) } }, logDArg := sk159LogDArgCertificate }

private noncomputable def leaf7065InnerLog : WideLogData :=
  innerPair805Data

set_option maxRecDepth 1000000 in
private theorem leaf7065LocalValidity :
    LeafFacts leaf7065Box leaf7065Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7065Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34353803264) }) = true
      norm_num [leaf7065Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7065CertificateValid :
    WideCertificateValid leaf7065Box leaf7065Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk159ValidityFacts chi360ValidityFacts
    leaf7065LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7065CoverageChecked :
    coverageCheck (innerAD leaf7065Box) leaf7065InnerLog = true := by
  rfl'

private theorem leaf7065InnerLogValid :
    leaf7065InnerLog.Valid 8 (innerAD leaf7065Box) :=
  wideLogDataValid_of_cachedCheck endpoint502PositiveFacts
    endpoint504PositiveFacts.valid leaf7065CoverageChecked

private noncomputable def leaf7065InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814953/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf7065InputLogOnePlusV_eq :
    leaf7065InputLogOnePlusV = outerEnclosure 24
      (leaf7065Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7065RoundedFacts : LeafRoundedFacts 8
    leaf7065Certificate.logOnePlusV leaf7065InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7065InputLogOnePlusV_eq }

private noncomputable def leaf7065Inputs : Inputs :=
  inputsOfCaches globalInput sk159RoundedInputs
    chi360InputQChi innerPair805Input
    leaf7065InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7065LowerChecked :
    lowerCheck 24 leaf7065Box leaf7065Inputs = true := by
  rfl'

private theorem leaf7065CoversExact : CoversExact 8
    leaf7065Box leaf7065Certificate leaf7065InnerLog leaf7065Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk159RoundedFacts chi360RoundedFacts
    innerPair805RoundedFacts leaf7065RoundedFacts (by rfl)

private theorem leaf7065FlatSound : Sound leaf7065Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7065CertificateValid
    leaf7065InnerLogValid leaf7065CoversExact leaf7065LowerChecked

private noncomputable def leaf7066Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (45/64), chiHi := (91/128) }

private noncomputable def leaf7066Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (134218037/134217728) }, vSqrt := { lower := (65527/65536), upper := (34357182459/34353774592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (505751093/268435456) }, upper := { exponent := 1, mantissa := (123/64) } }, logOuter := sk160LogOuterCertificate, logK := sk160LogKCertificate, logChi := chi359LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (68710957051/68707549184) } }, logDArg := sk160LogDArgCertificate }

private noncomputable def leaf7066InnerLog : WideLogData :=
  innerPair805Data

set_option maxRecDepth 1000000 in
private theorem leaf7066LocalValidity :
    LeafFacts leaf7066Box leaf7066Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7066Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (34357182459/34353774592) }) = true
      norm_num [leaf7066Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7066CertificateValid :
    WideCertificateValid leaf7066Box leaf7066Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk160ValidityFacts chi359ValidityFacts
    leaf7066LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7066CoverageChecked :
    coverageCheck (innerAD leaf7066Box) leaf7066InnerLog = true := by
  rfl'

private theorem leaf7066InnerLogValid :
    leaf7066InnerLog.Valid 8 (innerAD leaf7066Box) :=
  wideLogDataValid_of_cachedCheck endpoint502PositiveFacts
    endpoint504PositiveFacts.valid leaf7066CoverageChecked

private noncomputable def leaf7066InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629913/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7066InputLogOnePlusV_eq :
    leaf7066InputLogOnePlusV = outerEnclosure 24
      (leaf7066Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7066RoundedFacts : LeafRoundedFacts 8
    leaf7066Certificate.logOnePlusV leaf7066InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7066InputLogOnePlusV_eq }

private noncomputable def leaf7066Inputs : Inputs :=
  inputsOfCaches globalInput sk160RoundedInputs
    chi359InputQChi innerPair805Input
    leaf7066InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7066LowerChecked :
    lowerCheck 24 leaf7066Box leaf7066Inputs = true := by
  rfl'

private theorem leaf7066CoversExact : CoversExact 8
    leaf7066Box leaf7066Certificate leaf7066InnerLog leaf7066Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk160RoundedFacts chi359RoundedFacts
    innerPair805RoundedFacts leaf7066RoundedFacts (by rfl)

private theorem leaf7066FlatSound : Sound leaf7066Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7066CertificateValid
    leaf7066InnerLogValid leaf7066CoversExact leaf7066LowerChecked

private noncomputable def leaf7067Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (91/128), chiHi := (23/32) }

private noncomputable def leaf7067Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (134218039/134217728) }, vSqrt := { lower := (65527/65536), upper := (11452394153/11451236352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (509879607/268435456) }, upper := { exponent := 1, mantissa := (31/16) } }, logOuter := sk160LogOuterCertificate, logK := sk160LogKCertificate, logChi := chi360LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (22903630505/22902472704) } }, logDArg := sk160LogDArgCertificate }

private noncomputable def leaf7067InnerLog : WideLogData :=
  innerPair805Data

set_option maxRecDepth 1000000 in
private theorem leaf7067LocalValidity :
    LeafFacts leaf7067Box leaf7067Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7067Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (11452394153/11451236352) }) = true
      norm_num [leaf7067Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7067CertificateValid :
    WideCertificateValid leaf7067Box leaf7067Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk160ValidityFacts chi360ValidityFacts
    leaf7067LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7067CoverageChecked :
    coverageCheck (innerAD leaf7067Box) leaf7067InnerLog = true := by
  rfl'

private theorem leaf7067InnerLogValid :
    leaf7067InnerLog.Valid 8 (innerAD leaf7067Box) :=
  wideLogDataValid_of_cachedCheck endpoint502PositiveFacts
    endpoint504PositiveFacts.valid leaf7067CoverageChecked

private noncomputable def leaf7067InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629929/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7067InputLogOnePlusV_eq :
    leaf7067InputLogOnePlusV = outerEnclosure 24
      (leaf7067Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7067RoundedFacts : LeafRoundedFacts 8
    leaf7067Certificate.logOnePlusV leaf7067InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7067InputLogOnePlusV_eq }

private noncomputable def leaf7067Inputs : Inputs :=
  inputsOfCaches globalInput sk160RoundedInputs
    chi360InputQChi innerPair805Input
    leaf7067InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7067LowerChecked :
    lowerCheck 24 leaf7067Box leaf7067Inputs = true := by
  rfl'

private theorem leaf7067CoversExact : CoversExact 8
    leaf7067Box leaf7067Certificate leaf7067InnerLog leaf7067Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk160RoundedFacts chi360RoundedFacts
    innerPair805RoundedFacts leaf7067RoundedFacts (by rfl)

private theorem leaf7067FlatSound : Sound leaf7067Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7067CertificateValid
    leaf7067InnerLogValid leaf7067CoversExact leaf7067LowerChecked

private noncomputable def leaf7068Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (23/32), chiHi := (47/64) }

private noncomputable def leaf7068Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109079/67108864) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34353866752) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (247944203/134217728) }, upper := { exponent := 1, mantissa := (3891/2048) } }, logOuter := sk157LogOuterCertificate, logK := sk157LogKCertificate, logChi := chi343LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68711049211/68707733504) } }, logDArg := sk157LogDArgCertificate }

private noncomputable def leaf7068InnerLog : WideLogData :=
  innerPair801Data

set_option maxRecDepth 1000000 in
private theorem leaf7068LocalValidity :
    LeafFacts leaf7068Box leaf7068Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7068Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34353866752) }) = true
      norm_num [leaf7068Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7068CertificateValid :
    WideCertificateValid leaf7068Box leaf7068Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk157ValidityFacts chi343ValidityFacts
    leaf7068LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7068CoverageChecked :
    coverageCheck (innerAD leaf7068Box) leaf7068InnerLog = true := by
  rfl'

private theorem leaf7068InnerLogValid :
    leaf7068InnerLog.Valid 8 (innerAD leaf7068Box) :=
  wideLogDataValid_of_cachedCheck endpoint501PositiveFacts
    endpoint503PositiveFacts.valid leaf7068CoverageChecked

private noncomputable def leaf7068InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814945/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf7068InputLogOnePlusV_eq :
    leaf7068InputLogOnePlusV = outerEnclosure 24
      (leaf7068Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7068RoundedFacts : LeafRoundedFacts 8
    leaf7068Certificate.logOnePlusV leaf7068InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7068InputLogOnePlusV_eq }

private noncomputable def leaf7068Inputs : Inputs :=
  inputsOfCaches globalInput sk157RoundedInputs
    chi343InputQChi innerPair801Input
    leaf7068InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7068LowerChecked :
    lowerCheck 24 leaf7068Box leaf7068Inputs = true := by
  rfl'

private theorem leaf7068CoversExact : CoversExact 8
    leaf7068Box leaf7068Certificate leaf7068InnerLog leaf7068Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk157RoundedFacts chi343RoundedFacts
    innerPair801RoundedFacts leaf7068RoundedFacts (by rfl)

private theorem leaf7068FlatSound : Sound leaf7068Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7068CertificateValid
    leaf7068InnerLogValid leaf7068CoversExact leaf7068LowerChecked

private noncomputable def leaf7069Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (23/32), chiHi := (47/64) }

private noncomputable def leaf7069Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109081/67108864) }, vSqrt := { lower := (8191/8192), upper := (602757587/602697728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (250958673/134217728) }, upper := { exponent := 1, mantissa := (1969/1024) } }, logOuter := sk158LogOuterCertificate, logK := sk158LogKCertificate, logChi := chi343LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (1205455315/1205395456) } }, logDArg := sk158LogDArgCertificate }

private noncomputable def leaf7069InnerLog : WideLogData :=
  innerPair861Data

set_option maxRecDepth 1000000 in
private theorem leaf7069LocalValidity :
    LeafFacts leaf7069Box leaf7069Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7069Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (602757587/602697728) }) = true
      norm_num [leaf7069Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7069CertificateValid :
    WideCertificateValid leaf7069Box leaf7069Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk158ValidityFacts chi343ValidityFacts
    leaf7069LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7069CoverageChecked :
    coverageCheck (innerAD leaf7069Box) leaf7069InnerLog = true := by
  rfl'

private theorem leaf7069InnerLogValid :
    leaf7069InnerLog.Valid 8 (innerAD leaf7069Box) :=
  wideLogDataValid_of_cachedCheck endpoint572PositiveFacts
    endpoint573PositiveFacts.valid leaf7069CoverageChecked

private noncomputable def leaf7069InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814957/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf7069InputLogOnePlusV_eq :
    leaf7069InputLogOnePlusV = outerEnclosure 24
      (leaf7069Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7069RoundedFacts : LeafRoundedFacts 8
    leaf7069Certificate.logOnePlusV leaf7069InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7069InputLogOnePlusV_eq }

private noncomputable def leaf7069Inputs : Inputs :=
  inputsOfCaches globalInput sk158RoundedInputs
    chi343InputQChi innerPair861Input
    leaf7069InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7069LowerChecked :
    lowerCheck 24 leaf7069Box leaf7069Inputs = true := by
  rfl'

private theorem leaf7069CoversExact : CoversExact 8
    leaf7069Box leaf7069Certificate leaf7069InnerLog leaf7069Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk158RoundedFacts chi343RoundedFacts
    innerPair861RoundedFacts leaf7069RoundedFacts (by rfl)

private theorem leaf7069FlatSound : Sound leaf7069Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7069CertificateValid
    leaf7069InnerLogValid leaf7069CoversExact leaf7069LowerChecked

private noncomputable def leaf7070Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (47/64), chiHi := (3/4) }

private noncomputable def leaf7070Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109081/67108864) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34353741824) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (251876121/134217728) }, upper := { exponent := 1, mantissa := (247/128) } }, logOuter := sk157LogOuterCertificate, logK := sk157LogKCertificate, logChi := chi344LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68710924283/68707483648) } }, logDArg := sk157LogDArgCertificate }

private noncomputable def leaf7070InnerLog : WideLogData :=
  innerPair805Data

set_option maxRecDepth 1000000 in
private theorem leaf7070LocalValidity :
    LeafFacts leaf7070Box leaf7070Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7070Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34353741824) }) = true
      norm_num [leaf7070Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7070CertificateValid :
    WideCertificateValid leaf7070Box leaf7070Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk157ValidityFacts chi344ValidityFacts
    leaf7070LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7070CoverageChecked :
    coverageCheck (innerAD leaf7070Box) leaf7070InnerLog = true := by
  rfl'

private theorem leaf7070InnerLogValid :
    leaf7070InnerLog.Valid 8 (innerAD leaf7070Box) :=
  wideLogDataValid_of_cachedCheck endpoint502PositiveFacts
    endpoint504PositiveFacts.valid leaf7070CoverageChecked

private noncomputable def leaf7070InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629921/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7070InputLogOnePlusV_eq :
    leaf7070InputLogOnePlusV = outerEnclosure 24
      (leaf7070Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7070RoundedFacts : LeafRoundedFacts 8
    leaf7070Certificate.logOnePlusV leaf7070InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7070InputLogOnePlusV_eq }

private noncomputable def leaf7070Inputs : Inputs :=
  inputsOfCaches globalInput sk157RoundedInputs
    chi344InputQChi innerPair805Input
    leaf7070InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7070LowerChecked :
    lowerCheck 24 leaf7070Box leaf7070Inputs = true := by
  rfl'

private theorem leaf7070CoversExact : CoversExact 8
    leaf7070Box leaf7070Certificate leaf7070InnerLog leaf7070Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk157RoundedFacts chi344RoundedFacts
    innerPair805RoundedFacts leaf7070RoundedFacts (by rfl)

private theorem leaf7070FlatSound : Sound leaf7070Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7070CertificateValid
    leaf7070InnerLogValid leaf7070CoversExact leaf7070LowerChecked

private noncomputable def leaf7071Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (47/64), chiHi := (3/4) }

private noncomputable def leaf7071Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109083/67108864) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34353643520) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (254956123/134217728) }, upper := { exponent := 1, mantissa := (125/64) } }, logOuter := sk158LogOuterCertificate, logK := sk158LogKCertificate, logChi := chi344LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68710825979/68707287040) } }, logDArg := sk158LogDArgCertificate }

private noncomputable def leaf7071InnerLog : WideLogData :=
  innerPair806Data

set_option maxRecDepth 1000000 in
private theorem leaf7071LocalValidity :
    LeafFacts leaf7071Box leaf7071Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7071Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34353643520) }) = true
      norm_num [leaf7071Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7071CertificateValid :
    WideCertificateValid leaf7071Box leaf7071Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk158ValidityFacts chi344ValidityFacts
    leaf7071LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7071CoverageChecked :
    coverageCheck (innerAD leaf7071Box) leaf7071InnerLog = true := by
  rfl'

private theorem leaf7071InnerLogValid :
    leaf7071InnerLog.Valid 8 (innerAD leaf7071Box) :=
  wideLogDataValid_of_cachedCheck endpoint502PositiveFacts
    endpoint505PositiveFacts.valid leaf7071CoverageChecked

private noncomputable def leaf7071InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629945/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7071InputLogOnePlusV_eq :
    leaf7071InputLogOnePlusV = outerEnclosure 24
      (leaf7071Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7071RoundedFacts : LeafRoundedFacts 8
    leaf7071Certificate.logOnePlusV leaf7071InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7071InputLogOnePlusV_eq }

private noncomputable def leaf7071Inputs : Inputs :=
  inputsOfCaches globalInput sk158RoundedInputs
    chi344InputQChi innerPair806Input
    leaf7071InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7071LowerChecked :
    lowerCheck 24 leaf7071Box leaf7071Inputs = true := by
  rfl'

private theorem leaf7071CoversExact : CoversExact 8
    leaf7071Box leaf7071Certificate leaf7071InnerLog leaf7071Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk158RoundedFacts chi344RoundedFacts
    innerPair806RoundedFacts leaf7071RoundedFacts (by rfl)

private theorem leaf7071FlatSound : Sound leaf7071Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7071CertificateValid
    leaf7071InnerLogValid leaf7071CoversExact leaf7071LowerChecked

private noncomputable def leaf7072Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (23/32), chiHi := (47/64) }

private noncomputable def leaf7072Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109083/67108864) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34353674240) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (253973143/134217728) }, upper := { exponent := 1, mantissa := (3985/2048) } }, logOuter := sk159LogOuterCertificate, logK := sk159LogKCertificate, logChi := chi343LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68710856699/68707348480) } }, logDArg := sk159LogDArgCertificate }

private noncomputable def leaf7072InnerLog : WideLogData :=
  innerPair863Data

set_option maxRecDepth 1000000 in
private theorem leaf7072LocalValidity :
    LeafFacts leaf7072Box leaf7072Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7072Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34353674240) }) = true
      norm_num [leaf7072Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7072CertificateValid :
    WideCertificateValid leaf7072Box leaf7072Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk159ValidityFacts chi343ValidityFacts
    leaf7072LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7072CoverageChecked :
    coverageCheck (innerAD leaf7072Box) leaf7072InnerLog = true := by
  rfl'

private theorem leaf7072InnerLogValid :
    leaf7072InnerLog.Valid 8 (innerAD leaf7072Box) :=
  wideLogDataValid_of_cachedCheck endpoint574PositiveFacts
    endpoint575PositiveFacts.valid leaf7072CoverageChecked

private noncomputable def leaf7072InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629937/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7072InputLogOnePlusV_eq :
    leaf7072InputLogOnePlusV = outerEnclosure 24
      (leaf7072Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7072RoundedFacts : LeafRoundedFacts 8
    leaf7072Certificate.logOnePlusV leaf7072InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7072InputLogOnePlusV_eq }

private noncomputable def leaf7072Inputs : Inputs :=
  inputsOfCaches globalInput sk159RoundedInputs
    chi343InputQChi innerPair863Input
    leaf7072InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7072LowerChecked :
    lowerCheck 24 leaf7072Box leaf7072Inputs = true := by
  rfl'

private theorem leaf7072CoversExact : CoversExact 8
    leaf7072Box leaf7072Certificate leaf7072InnerLog leaf7072Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk159RoundedFacts chi343RoundedFacts
    innerPair863RoundedFacts leaf7072RoundedFacts (by rfl)

private theorem leaf7072FlatSound : Sound leaf7072Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7072CertificateValid
    leaf7072InnerLogValid leaf7072CoversExact leaf7072LowerChecked

private noncomputable def leaf7073Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (23/32), chiHi := (47/64) }

private noncomputable def leaf7073Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109085/67108864) }, vSqrt := { lower := (65527/65536), upper := (34357182459/34353577984) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (256987613/134217728) }, upper := { exponent := 1, mantissa := (63/32) } }, logOuter := sk160LogOuterCertificate, logK := sk160LogKCertificate, logChi := chi343LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (68710760443/68707155968) } }, logDArg := sk160LogDArgCertificate }

private noncomputable def leaf7073InnerLog : WideLogData :=
  innerPair808Data

set_option maxRecDepth 1000000 in
private theorem leaf7073LocalValidity :
    LeafFacts leaf7073Box leaf7073Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7073Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (34357182459/34353577984) }) = true
      norm_num [leaf7073Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7073CertificateValid :
    WideCertificateValid leaf7073Box leaf7073Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk160ValidityFacts chi343ValidityFacts
    leaf7073LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7073CoverageChecked :
    coverageCheck (innerAD leaf7073Box) leaf7073InnerLog = true := by
  rfl'

private theorem leaf7073InnerLogValid :
    leaf7073InnerLog.Valid 8 (innerAD leaf7073Box) :=
  wideLogDataValid_of_cachedCheck endpoint503PositiveFacts
    endpoint505PositiveFacts.valid leaf7073CoverageChecked

private noncomputable def leaf7073InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629961/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7073InputLogOnePlusV_eq :
    leaf7073InputLogOnePlusV = outerEnclosure 24
      (leaf7073Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7073RoundedFacts : LeafRoundedFacts 8
    leaf7073Certificate.logOnePlusV leaf7073InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7073InputLogOnePlusV_eq }

private noncomputable def leaf7073Inputs : Inputs :=
  inputsOfCaches globalInput sk160RoundedInputs
    chi343InputQChi innerPair808Input
    leaf7073InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7073LowerChecked :
    lowerCheck 24 leaf7073Box leaf7073Inputs = true := by
  rfl'

private theorem leaf7073CoversExact : CoversExact 8
    leaf7073Box leaf7073Certificate leaf7073InnerLog leaf7073Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk160RoundedFacts chi343RoundedFacts
    innerPair808RoundedFacts leaf7073RoundedFacts (by rfl)

private theorem leaf7073FlatSound : Sound leaf7073Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7073CertificateValid
    leaf7073InnerLogValid leaf7073CoversExact leaf7073LowerChecked

private noncomputable def leaf7074Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (47/64), chiHi := (3/4) }

private noncomputable def leaf7074Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109085/67108864) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34353545216) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (258036125/134217728) }, upper := { exponent := 1, mantissa := (253/128) } }, logOuter := sk159LogOuterCertificate, logK := sk159LogKCertificate, logChi := chi344LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68710727675/68707090432) } }, logDArg := sk159LogDArgCertificate }

private noncomputable def leaf7074InnerLog : WideLogData :=
  innerPair865Data

set_option maxRecDepth 1000000 in
private theorem leaf7074LocalValidity :
    LeafFacts leaf7074Box leaf7074Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7074Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34353545216) }) = true
      norm_num [leaf7074Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7074CertificateValid :
    WideCertificateValid leaf7074Box leaf7074Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk159ValidityFacts chi344ValidityFacts
    leaf7074LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7074CoverageChecked :
    coverageCheck (innerAD leaf7074Box) leaf7074InnerLog = true := by
  rfl'

private theorem leaf7074InnerLogValid :
    leaf7074InnerLog.Valid 8 (innerAD leaf7074Box) :=
  wideLogDataValid_of_cachedCheck endpoint576PositiveFacts
    endpoint577PositiveFacts.valid leaf7074CoverageChecked

private noncomputable def leaf7074InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629969/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7074InputLogOnePlusV_eq :
    leaf7074InputLogOnePlusV = outerEnclosure 24
      (leaf7074Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7074RoundedFacts : LeafRoundedFacts 8
    leaf7074Certificate.logOnePlusV leaf7074InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7074InputLogOnePlusV_eq }

private noncomputable def leaf7074Inputs : Inputs :=
  inputsOfCaches globalInput sk159RoundedInputs
    chi344InputQChi innerPair865Input
    leaf7074InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7074LowerChecked :
    lowerCheck 24 leaf7074Box leaf7074Inputs = true := by
  rfl'

private theorem leaf7074CoversExact : CoversExact 8
    leaf7074Box leaf7074Certificate leaf7074InnerLog leaf7074Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk159RoundedFacts chi344RoundedFacts
    innerPair865RoundedFacts leaf7074RoundedFacts (by rfl)

private theorem leaf7074FlatSound : Sound leaf7074Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7074CertificateValid
    leaf7074InnerLogValid leaf7074CoversExact leaf7074LowerChecked

private noncomputable def leaf7075Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (47/64), chiHi := (3/4) }

private noncomputable def leaf7075Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109087/67108864) }, vSqrt := { lower := (65527/65536), upper := (17178329085/17176723456) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (261116127/134217728) }, upper := { exponent := 2, mantissa := (1) } }, logOuter := sk160LogOuterCertificate, logK := sk160LogKCertificate, logChi := chi344LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (34355052541/34353446912) } }, logDArg := sk160LogDArgCertificate }

private noncomputable def leaf7075InnerLog : WideLogData :=
  innerPair811Data

set_option maxRecDepth 1000000 in
private theorem leaf7075LocalValidity :
    LeafFacts leaf7075Box leaf7075Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7075Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (17178329085/17176723456) }) = true
      norm_num [leaf7075Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7075CertificateValid :
    WideCertificateValid leaf7075Box leaf7075Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk160ValidityFacts chi344ValidityFacts
    leaf7075LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7075CoverageChecked :
    coverageCheck (innerAD leaf7075Box) leaf7075InnerLog = true := by
  rfl'

private theorem leaf7075InnerLogValid :
    leaf7075InnerLog.Valid 8 (innerAD leaf7075Box) :=
  wideLogDataValid_of_cachedCheck endpoint504PositiveFacts
    endpoint506PositiveFacts.valid leaf7075CoverageChecked

private noncomputable def leaf7075InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629865/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7075InputLogOnePlusV_eq :
    leaf7075InputLogOnePlusV = outerEnclosure 24
      (leaf7075Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7075RoundedFacts : LeafRoundedFacts 8
    leaf7075Certificate.logOnePlusV leaf7075InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7075InputLogOnePlusV_eq }

private noncomputable def leaf7075Inputs : Inputs :=
  inputsOfCaches globalInput sk160RoundedInputs
    chi344InputQChi innerPair811Input
    leaf7075InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7075LowerChecked :
    lowerCheck 24 leaf7075Box leaf7075Inputs = true := by
  rfl'

private theorem leaf7075CoversExact : CoversExact 8
    leaf7075Box leaf7075Certificate leaf7075InnerLog leaf7075Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk160RoundedFacts chi344RoundedFacts
    innerPair811RoundedFacts leaf7075RoundedFacts (by rfl)

private theorem leaf7075FlatSound : Sound leaf7075Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7075CertificateValid
    leaf7075InnerLogValid leaf7075CoversExact leaf7075LowerChecked

private noncomputable def component143Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (5/8), chiHi := (41/64) }

set_option maxRecDepth 1000000 in
private theorem component143Node0_sound : Sound component143Node0Box :=
  sound_of_literal_split component143Node0Box leaf7022Box leaf7023Box
    .chi (81/128) (by rfl) (by rfl)
    leaf7022FlatSound leaf7023FlatSound

private noncomputable def component143Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (5/8), chiHi := (41/64) }

set_option maxRecDepth 1000000 in
private theorem component143Node1_sound : Sound component143Node1Box :=
  sound_of_literal_split component143Node1Box leaf7024Box leaf7025Box
    .chi (81/128) (by rfl) (by rfl)
    leaf7024FlatSound leaf7025FlatSound

private noncomputable def component143Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (5/8), chiHi := (41/64) }

set_option maxRecDepth 1000000 in
private theorem component143Node2_sound : Sound component143Node2Box :=
  sound_of_literal_split component143Node2Box component143Node0Box component143Node1Box
    .k (61/16) (by rfl) (by rfl)
    component143Node0_sound component143Node1_sound

private noncomputable def component143Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (41/64), chiHi := (21/32) }

set_option maxRecDepth 1000000 in
private theorem component143Node3_sound : Sound component143Node3Box :=
  sound_of_literal_split component143Node3Box leaf7026Box leaf7027Box
    .chi (83/128) (by rfl) (by rfl)
    leaf7026FlatSound leaf7027FlatSound

private noncomputable def component143Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (41/64), chiHi := (21/32) }

set_option maxRecDepth 1000000 in
private theorem component143Node4_sound : Sound component143Node4Box :=
  sound_of_literal_split component143Node4Box leaf7028Box leaf7029Box
    .chi (83/128) (by rfl) (by rfl)
    leaf7028FlatSound leaf7029FlatSound

private noncomputable def component143Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (41/64), chiHi := (21/32) }

set_option maxRecDepth 1000000 in
private theorem component143Node5_sound : Sound component143Node5Box :=
  sound_of_literal_split component143Node5Box component143Node3Box component143Node4Box
    .k (61/16) (by rfl) (by rfl)
    component143Node3_sound component143Node4_sound

private noncomputable def component143Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (5/8), chiHi := (21/32) }

set_option maxRecDepth 1000000 in
private theorem component143Node6_sound : Sound component143Node6Box :=
  sound_of_literal_split component143Node6Box component143Node2Box component143Node5Box
    .chi (41/64) (by rfl) (by rfl)
    component143Node2_sound component143Node5_sound

private noncomputable def component143Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (5/8), chiHi := (41/64) }

set_option maxRecDepth 1000000 in
private theorem component143Node7_sound : Sound component143Node7Box :=
  sound_of_literal_split component143Node7Box leaf7030Box leaf7031Box
    .chi (81/128) (by rfl) (by rfl)
    leaf7030FlatSound leaf7031FlatSound

private noncomputable def component143Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (5/8), chiHi := (41/64) }

set_option maxRecDepth 1000000 in
private theorem component143Node8_sound : Sound component143Node8Box :=
  sound_of_literal_split component143Node8Box leaf7032Box leaf7033Box
    .chi (81/128) (by rfl) (by rfl)
    leaf7032FlatSound leaf7033FlatSound

private noncomputable def component143Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (5/8), chiHi := (41/64) }

set_option maxRecDepth 1000000 in
private theorem component143Node9_sound : Sound component143Node9Box :=
  sound_of_literal_split component143Node9Box component143Node7Box component143Node8Box
    .k (63/16) (by rfl) (by rfl)
    component143Node7_sound component143Node8_sound

private noncomputable def component143Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (41/64), chiHi := (21/32) }

set_option maxRecDepth 1000000 in
private theorem component143Node10_sound : Sound component143Node10Box :=
  sound_of_literal_split component143Node10Box leaf7034Box leaf7035Box
    .chi (83/128) (by rfl) (by rfl)
    leaf7034FlatSound leaf7035FlatSound

private noncomputable def component143Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (41/64), chiHi := (21/32) }

set_option maxRecDepth 1000000 in
private theorem component143Node11_sound : Sound component143Node11Box :=
  sound_of_literal_split component143Node11Box leaf7036Box leaf7037Box
    .chi (83/128) (by rfl) (by rfl)
    leaf7036FlatSound leaf7037FlatSound

private noncomputable def component143Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (41/64), chiHi := (21/32) }

set_option maxRecDepth 1000000 in
private theorem component143Node12_sound : Sound component143Node12Box :=
  sound_of_literal_split component143Node12Box component143Node10Box component143Node11Box
    .k (63/16) (by rfl) (by rfl)
    component143Node10_sound component143Node11_sound

private noncomputable def component143Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (5/8), chiHi := (21/32) }

set_option maxRecDepth 1000000 in
private theorem component143Node13_sound : Sound component143Node13Box :=
  sound_of_literal_split component143Node13Box component143Node9Box component143Node12Box
    .chi (41/64) (by rfl) (by rfl)
    component143Node9_sound component143Node12_sound

private noncomputable def component143Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (4), chiLo := (5/8), chiHi := (21/32) }

set_option maxRecDepth 1000000 in
private theorem component143Node14_sound : Sound component143Node14Box :=
  sound_of_literal_split component143Node14Box component143Node6Box component143Node13Box
    .k (31/8) (by rfl) (by rfl)
    component143Node6_sound component143Node13_sound

private noncomputable def component143Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (21/32), chiHi := (43/64) }

set_option maxRecDepth 1000000 in
private theorem component143Node15_sound : Sound component143Node15Box :=
  sound_of_literal_split component143Node15Box leaf7038Box leaf7039Box
    .chi (85/128) (by rfl) (by rfl)
    leaf7038FlatSound leaf7039FlatSound

private noncomputable def component143Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (21/32), chiHi := (43/64) }

set_option maxRecDepth 1000000 in
private theorem component143Node16_sound : Sound component143Node16Box :=
  sound_of_literal_split component143Node16Box leaf7040Box leaf7041Box
    .chi (85/128) (by rfl) (by rfl)
    leaf7040FlatSound leaf7041FlatSound

private noncomputable def component143Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (21/32), chiHi := (43/64) }

set_option maxRecDepth 1000000 in
private theorem component143Node17_sound : Sound component143Node17Box :=
  sound_of_literal_split component143Node17Box component143Node15Box component143Node16Box
    .k (61/16) (by rfl) (by rfl)
    component143Node15_sound component143Node16_sound

private noncomputable def component143Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (43/64), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component143Node18_sound : Sound component143Node18Box :=
  sound_of_literal_split component143Node18Box leaf7042Box leaf7043Box
    .chi (87/128) (by rfl) (by rfl)
    leaf7042FlatSound leaf7043FlatSound

private noncomputable def component143Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (43/64), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component143Node19_sound : Sound component143Node19Box :=
  sound_of_literal_split component143Node19Box leaf7044Box leaf7045Box
    .chi (87/128) (by rfl) (by rfl)
    leaf7044FlatSound leaf7045FlatSound

private noncomputable def component143Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (43/64), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component143Node20_sound : Sound component143Node20Box :=
  sound_of_literal_split component143Node20Box component143Node18Box component143Node19Box
    .k (61/16) (by rfl) (by rfl)
    component143Node18_sound component143Node19_sound

private noncomputable def component143Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (21/32), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component143Node21_sound : Sound component143Node21Box :=
  sound_of_literal_split component143Node21Box component143Node17Box component143Node20Box
    .chi (43/64) (by rfl) (by rfl)
    component143Node17_sound component143Node20_sound

private noncomputable def component143Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (21/32), chiHi := (43/64) }

set_option maxRecDepth 1000000 in
private theorem component143Node22_sound : Sound component143Node22Box :=
  sound_of_literal_split component143Node22Box leaf7046Box leaf7047Box
    .chi (85/128) (by rfl) (by rfl)
    leaf7046FlatSound leaf7047FlatSound

private noncomputable def component143Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (21/32), chiHi := (43/64) }

set_option maxRecDepth 1000000 in
private theorem component143Node23_sound : Sound component143Node23Box :=
  sound_of_literal_split component143Node23Box leaf7048Box leaf7049Box
    .chi (85/128) (by rfl) (by rfl)
    leaf7048FlatSound leaf7049FlatSound

private noncomputable def component143Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (21/32), chiHi := (43/64) }

set_option maxRecDepth 1000000 in
private theorem component143Node24_sound : Sound component143Node24Box :=
  sound_of_literal_split component143Node24Box component143Node22Box component143Node23Box
    .k (63/16) (by rfl) (by rfl)
    component143Node22_sound component143Node23_sound

private noncomputable def component143Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (43/64), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component143Node25_sound : Sound component143Node25Box :=
  sound_of_literal_split component143Node25Box leaf7050Box leaf7051Box
    .chi (87/128) (by rfl) (by rfl)
    leaf7050FlatSound leaf7051FlatSound

private noncomputable def component143Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (43/64), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component143Node26_sound : Sound component143Node26Box :=
  sound_of_literal_split component143Node26Box leaf7052Box leaf7053Box
    .chi (87/128) (by rfl) (by rfl)
    leaf7052FlatSound leaf7053FlatSound

private noncomputable def component143Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (43/64), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component143Node27_sound : Sound component143Node27Box :=
  sound_of_literal_split component143Node27Box component143Node25Box component143Node26Box
    .k (63/16) (by rfl) (by rfl)
    component143Node25_sound component143Node26_sound

private noncomputable def component143Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (21/32), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component143Node28_sound : Sound component143Node28Box :=
  sound_of_literal_split component143Node28Box component143Node24Box component143Node27Box
    .chi (43/64) (by rfl) (by rfl)
    component143Node24_sound component143Node27_sound

private noncomputable def component143Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (4), chiLo := (21/32), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component143Node29_sound : Sound component143Node29Box :=
  sound_of_literal_split component143Node29Box component143Node21Box component143Node28Box
    .k (31/8) (by rfl) (by rfl)
    component143Node21_sound component143Node28_sound

private noncomputable def component143Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (4), chiLo := (5/8), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component143Node30_sound : Sound component143Node30Box :=
  sound_of_literal_split component143Node30Box component143Node14Box component143Node29Box
    .chi (21/32) (by rfl) (by rfl)
    component143Node14_sound component143Node29_sound

private noncomputable def component143Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (11/16), chiHi := (45/64) }

set_option maxRecDepth 1000000 in
private theorem component143Node31_sound : Sound component143Node31Box :=
  sound_of_literal_split component143Node31Box leaf7054Box leaf7055Box
    .chi (89/128) (by rfl) (by rfl)
    leaf7054FlatSound leaf7055FlatSound

private noncomputable def component143Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (11/16), chiHi := (45/64) }

set_option maxRecDepth 1000000 in
private theorem component143Node32_sound : Sound component143Node32Box :=
  sound_of_literal_split component143Node32Box leaf7056Box leaf7057Box
    .chi (89/128) (by rfl) (by rfl)
    leaf7056FlatSound leaf7057FlatSound

private noncomputable def component143Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (11/16), chiHi := (45/64) }

set_option maxRecDepth 1000000 in
private theorem component143Node33_sound : Sound component143Node33Box :=
  sound_of_literal_split component143Node33Box component143Node31Box component143Node32Box
    .k (61/16) (by rfl) (by rfl)
    component143Node31_sound component143Node32_sound

private noncomputable def component143Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (45/64), chiHi := (23/32) }

set_option maxRecDepth 1000000 in
private theorem component143Node34_sound : Sound component143Node34Box :=
  sound_of_literal_split component143Node34Box leaf7058Box leaf7059Box
    .k (61/16) (by rfl) (by rfl)
    leaf7058FlatSound leaf7059FlatSound

private noncomputable def component143Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (11/16), chiHi := (23/32) }

set_option maxRecDepth 1000000 in
private theorem component143Node35_sound : Sound component143Node35Box :=
  sound_of_literal_split component143Node35Box component143Node33Box component143Node34Box
    .chi (45/64) (by rfl) (by rfl)
    component143Node33_sound component143Node34_sound

private noncomputable def component143Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (11/16), chiHi := (45/64) }

set_option maxRecDepth 1000000 in
private theorem component143Node36_sound : Sound component143Node36Box :=
  sound_of_literal_split component143Node36Box leaf7060Box leaf7061Box
    .chi (89/128) (by rfl) (by rfl)
    leaf7060FlatSound leaf7061FlatSound

private noncomputable def component143Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (11/16), chiHi := (45/64) }

set_option maxRecDepth 1000000 in
private theorem component143Node37_sound : Sound component143Node37Box :=
  sound_of_literal_split component143Node37Box leaf7062Box leaf7063Box
    .chi (89/128) (by rfl) (by rfl)
    leaf7062FlatSound leaf7063FlatSound

private noncomputable def component143Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (11/16), chiHi := (45/64) }

set_option maxRecDepth 1000000 in
private theorem component143Node38_sound : Sound component143Node38Box :=
  sound_of_literal_split component143Node38Box component143Node36Box component143Node37Box
    .k (63/16) (by rfl) (by rfl)
    component143Node36_sound component143Node37_sound

private noncomputable def component143Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (45/64), chiHi := (23/32) }

set_option maxRecDepth 1000000 in
private theorem component143Node39_sound : Sound component143Node39Box :=
  sound_of_literal_split component143Node39Box leaf7064Box leaf7065Box
    .chi (91/128) (by rfl) (by rfl)
    leaf7064FlatSound leaf7065FlatSound

private noncomputable def component143Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (45/64), chiHi := (23/32) }

set_option maxRecDepth 1000000 in
private theorem component143Node40_sound : Sound component143Node40Box :=
  sound_of_literal_split component143Node40Box leaf7066Box leaf7067Box
    .chi (91/128) (by rfl) (by rfl)
    leaf7066FlatSound leaf7067FlatSound

private noncomputable def component143Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (45/64), chiHi := (23/32) }

set_option maxRecDepth 1000000 in
private theorem component143Node41_sound : Sound component143Node41Box :=
  sound_of_literal_split component143Node41Box component143Node39Box component143Node40Box
    .k (63/16) (by rfl) (by rfl)
    component143Node39_sound component143Node40_sound

private noncomputable def component143Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (11/16), chiHi := (23/32) }

set_option maxRecDepth 1000000 in
private theorem component143Node42_sound : Sound component143Node42Box :=
  sound_of_literal_split component143Node42Box component143Node38Box component143Node41Box
    .chi (45/64) (by rfl) (by rfl)
    component143Node38_sound component143Node41_sound

private noncomputable def component143Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (4), chiLo := (11/16), chiHi := (23/32) }

set_option maxRecDepth 1000000 in
private theorem component143Node43_sound : Sound component143Node43Box :=
  sound_of_literal_split component143Node43Box component143Node35Box component143Node42Box
    .k (31/8) (by rfl) (by rfl)
    component143Node35_sound component143Node42_sound

private noncomputable def component143Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (23/32), chiHi := (47/64) }

set_option maxRecDepth 1000000 in
private theorem component143Node44_sound : Sound component143Node44Box :=
  sound_of_literal_split component143Node44Box leaf7068Box leaf7069Box
    .k (61/16) (by rfl) (by rfl)
    leaf7068FlatSound leaf7069FlatSound

private noncomputable def component143Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (47/64), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component143Node45_sound : Sound component143Node45Box :=
  sound_of_literal_split component143Node45Box leaf7070Box leaf7071Box
    .k (61/16) (by rfl) (by rfl)
    leaf7070FlatSound leaf7071FlatSound

private noncomputable def component143Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (23/32), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component143Node46_sound : Sound component143Node46Box :=
  sound_of_literal_split component143Node46Box component143Node44Box component143Node45Box
    .chi (47/64) (by rfl) (by rfl)
    component143Node44_sound component143Node45_sound

private noncomputable def component143Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (23/32), chiHi := (47/64) }

set_option maxRecDepth 1000000 in
private theorem component143Node47_sound : Sound component143Node47Box :=
  sound_of_literal_split component143Node47Box leaf7072Box leaf7073Box
    .k (63/16) (by rfl) (by rfl)
    leaf7072FlatSound leaf7073FlatSound

private noncomputable def component143Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (47/64), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component143Node48_sound : Sound component143Node48Box :=
  sound_of_literal_split component143Node48Box leaf7074Box leaf7075Box
    .k (63/16) (by rfl) (by rfl)
    leaf7074FlatSound leaf7075FlatSound

private noncomputable def component143Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (23/32), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component143Node49_sound : Sound component143Node49Box :=
  sound_of_literal_split component143Node49Box component143Node47Box component143Node48Box
    .chi (47/64) (by rfl) (by rfl)
    component143Node47_sound component143Node48_sound

private noncomputable def component143Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (4), chiLo := (23/32), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component143Node50_sound : Sound component143Node50Box :=
  sound_of_literal_split component143Node50Box component143Node46Box component143Node49Box
    .k (31/8) (by rfl) (by rfl)
    component143Node46_sound component143Node49_sound

private noncomputable def component143Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (4), chiLo := (11/16), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component143Node51_sound : Sound component143Node51Box :=
  sound_of_literal_split component143Node51Box component143Node43Box component143Node50Box
    .chi (23/32) (by rfl) (by rfl)
    component143Node43_sound component143Node50_sound

noncomputable def component143Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (4), chiLo := (5/8), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
theorem component143_sound : Sound component143Box :=
  sound_of_literal_split component143Box component143Node30Box component143Node51Box
    .chi (11/16) (by rfl) (by rfl)
    component143Node30_sound component143Node51_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
