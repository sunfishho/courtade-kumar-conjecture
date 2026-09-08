import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch6
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch10
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch8
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch9
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheSKBatch2
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

private noncomputable def leaf5531Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (11/32), chiHi := (89/256) }

private noncomputable def leaf5531Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871339/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356890368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1251922903/1073741824) }, upper := { exponent := 1, mantissa := (19317/16384) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi297LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715612927/68713780736) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf5531InnerLog : WideLogData :=
  innerPair659Data

set_option maxRecDepth 1000000 in
private theorem leaf5531LocalValidity :
    LeafFacts leaf5531Box leaf5531Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5531Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356890368) }) = true
      norm_num [leaf5531Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5531CertificateValid :
    WideCertificateValid leaf5531Box leaf5531Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi297ValidityFacts
    leaf5531LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5531CoverageChecked :
    coverageCheck (innerAD leaf5531Box) leaf5531InnerLog = true := by
  rfl'

private theorem leaf5531InnerLogValid :
    leaf5531InnerLog.Valid 8 (innerAD leaf5531Box) :=
  wideLogDataValid_of_cachedCheck endpoint404PositiveFacts
    endpoint405PositiveFacts.valid leaf5531CoverageChecked

private noncomputable def leaf5531InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453691/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5531InputLogOnePlusV_eq :
    leaf5531InputLogOnePlusV = outerEnclosure 24
      (leaf5531Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5531RoundedFacts : LeafRoundedFacts 8
    leaf5531Certificate.logOnePlusV leaf5531InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5531InputLogOnePlusV_eq }

private noncomputable def leaf5531Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi297InputQChi innerPair659Input
    leaf5531InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5531LowerChecked :
    lowerCheck 24 leaf5531Box leaf5531Inputs = true := by
  rfl'

private theorem leaf5531CoversExact : CoversExact 8
    leaf5531Box leaf5531Certificate leaf5531InnerLog leaf5531Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi297RoundedFacts
    innerPair659RoundedFacts leaf5531RoundedFacts (by rfl)

private theorem leaf5531FlatSound : Sound leaf5531Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5531CertificateValid
    leaf5531InnerLogValid leaf5531CoversExact leaf5531LowerChecked

private noncomputable def leaf5532Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (89/256), chiHi := (45/128) }

private noncomputable def leaf5532Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871341/536870912) }, vSqrt := { lower := (8191/8192), upper := (4908388937/4908122624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1260048869/1073741824) }, upper := { exponent := 1, mantissa := (9721/8192) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi298LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (9816511561/9816245248) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf5532InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf5532LocalValidity :
    LeafFacts leaf5532Box leaf5532Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5532Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4908388937/4908122624) }) = true
      norm_num [leaf5532Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5532CertificateValid :
    WideCertificateValid leaf5532Box leaf5532Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi298ValidityFacts
    leaf5532LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5532CoverageChecked :
    coverageCheck (innerAD leaf5532Box) leaf5532InnerLog = true := by
  rfl'

private theorem leaf5532InnerLogValid :
    leaf5532InnerLog.Valid 8 (innerAD leaf5532Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf5532CoverageChecked

private noncomputable def leaf5532InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (363423/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf5532InputLogOnePlusV_eq :
    leaf5532InputLogOnePlusV = outerEnclosure 24
      (leaf5532Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5532RoundedFacts : LeafRoundedFacts 8
    leaf5532Certificate.logOnePlusV leaf5532InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5532InputLogOnePlusV_eq }

private noncomputable def leaf5532Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi298InputQChi innerPair272Input
    leaf5532InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5532LowerChecked :
    lowerCheck 24 leaf5532Box leaf5532Inputs = true := by
  rfl'

private theorem leaf5532CoversExact : CoversExact 8
    leaf5532Box leaf5532Certificate leaf5532InnerLog leaf5532Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi298RoundedFacts
    innerPair272RoundedFacts leaf5532RoundedFacts (by rfl)

private theorem leaf5532FlatSound : Sound leaf5532Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5532CertificateValid
    leaf5532InnerLogValid leaf5532CoversExact leaf5532LowerChecked

private noncomputable def leaf5533Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (251/64), chiLo := (11/32), chiHi := (89/256) }

private noncomputable def leaf5533Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742503/1073741824) }, vSqrt := { lower := (8191/8192), upper := (3272257731/3272083712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2515412379/2147483648) }, upper := { exponent := 1, mantissa := (38723/32768) } }, logOuter := sk235LogOuterCertificate, logK := sk235LogKCertificate, logChi := chi297LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (6544341443/6544167424) } }, logDArg := sk235LogDArgCertificate }

private noncomputable def leaf5533InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf5533LocalValidity :
    LeafFacts leaf5533Box leaf5533Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5533Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (3272257731/3272083712) }) = true
      norm_num [leaf5533Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5533CertificateValid :
    WideCertificateValid leaf5533Box leaf5533Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk235ValidityFacts chi297ValidityFacts
    leaf5533LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5533CoverageChecked :
    coverageCheck (innerAD leaf5533Box) leaf5533InnerLog = true := by
  rfl'

private theorem leaf5533InnerLogValid :
    leaf5533InnerLog.Valid 8 (innerAD leaf5533Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf5533CoverageChecked

private noncomputable def leaf5533InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629527/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5533InputLogOnePlusV_eq :
    leaf5533InputLogOnePlusV = outerEnclosure 24
      (leaf5533Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5533RoundedFacts : LeafRoundedFacts 8
    leaf5533Certificate.logOnePlusV leaf5533InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5533InputLogOnePlusV_eq }

private noncomputable def leaf5533Inputs : Inputs :=
  inputsOfCaches globalInput sk235RoundedInputs
    chi297InputQChi innerPair272Input
    leaf5533InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5533LowerChecked :
    lowerCheck 24 leaf5533Box leaf5533Inputs = true := by
  rfl'

private theorem leaf5533CoversExact : CoversExact 8
    leaf5533Box leaf5533Certificate leaf5533InnerLog leaf5533Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk235RoundedFacts chi297RoundedFacts
    innerPair272RoundedFacts leaf5533RoundedFacts (by rfl)

private theorem leaf5533FlatSound : Sound leaf5533Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5533CertificateValid
    leaf5533InnerLogValid leaf5533CoversExact leaf5533LowerChecked

private noncomputable def leaf5534Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (11/32), chiHi := (89/256) }

private noncomputable def leaf5534Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742505/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68713735168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2521179193/2147483648) }, upper := { exponent := 1, mantissa := (9703/8192) } }, logOuter := sk236LogOuterCertificate, logK := sk236LogKCertificate, logChi := chi297LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431147519/137427470336) } }, logDArg := sk236LogDArgCertificate }

private noncomputable def leaf5534InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf5534LocalValidity :
    LeafFacts leaf5534Box leaf5534Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5534Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68713735168) }) = true
      norm_num [leaf5534Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5534CertificateValid :
    WideCertificateValid leaf5534Box leaf5534Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk236ValidityFacts chi297ValidityFacts
    leaf5534LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5534CoverageChecked :
    coverageCheck (innerAD leaf5534Box) leaf5534InnerLog = true := by
  rfl'

private theorem leaf5534InnerLogValid :
    leaf5534InnerLog.Valid 8 (innerAD leaf5534Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf5534CoverageChecked

private noncomputable def leaf5534InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814765/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5534InputLogOnePlusV_eq :
    leaf5534InputLogOnePlusV = outerEnclosure 24
      (leaf5534Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5534RoundedFacts : LeafRoundedFacts 8
    leaf5534Certificate.logOnePlusV leaf5534InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5534InputLogOnePlusV_eq }

private noncomputable def leaf5534Inputs : Inputs :=
  inputsOfCaches globalInput sk236RoundedInputs
    chi297InputQChi innerPair272Input
    leaf5534InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5534LowerChecked :
    lowerCheck 24 leaf5534Box leaf5534Inputs = true := by
  rfl'

private theorem leaf5534CoversExact : CoversExact 8
    leaf5534Box leaf5534Certificate leaf5534InnerLog leaf5534Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk236RoundedFacts chi297RoundedFacts
    innerPair272RoundedFacts leaf5534RoundedFacts (by rfl)

private theorem leaf5534FlatSound : Sound leaf5534Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5534CertificateValid
    leaf5534InnerLogValid leaf5534CoversExact leaf5534LowerChecked

private noncomputable def leaf5535Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (89/256), chiHi := (45/128) }

private noncomputable def leaf5535Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871343/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356835328) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1265881215/1073741824) }, upper := { exponent := 1, mantissa := (4883/4096) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi298LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715557887/68713670656) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf5535InnerLog : WideLogData :=
  innerPair660Data

set_option maxRecDepth 1000000 in
private theorem leaf5535LocalValidity :
    LeafFacts leaf5535Box leaf5535Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5535Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356835328) }) = true
      norm_num [leaf5535Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5535CertificateValid :
    WideCertificateValid leaf5535Box leaf5535Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi298ValidityFacts
    leaf5535LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5535CoverageChecked :
    coverageCheck (innerAD leaf5535Box) leaf5535InnerLog = true := by
  rfl'

private theorem leaf5535InnerLogValid :
    leaf5535InnerLog.Valid 8 (innerAD leaf5535Box) :=
  wideLogDataValid_of_cachedCheck endpoint406PositiveFacts
    endpoint407PositiveFacts.valid leaf5535CoverageChecked

private noncomputable def leaf5535InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814771/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5535InputLogOnePlusV_eq :
    leaf5535InputLogOnePlusV = outerEnclosure 24
      (leaf5535Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5535RoundedFacts : LeafRoundedFacts 8
    leaf5535Certificate.logOnePlusV leaf5535InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5535InputLogOnePlusV_eq }

private noncomputable def leaf5535Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi298InputQChi innerPair660Input
    leaf5535InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5535LowerChecked :
    lowerCheck 24 leaf5535Box leaf5535Inputs = true := by
  rfl'

private theorem leaf5535CoversExact : CoversExact 8
    leaf5535Box leaf5535Certificate leaf5535InnerLog leaf5535Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi298RoundedFacts
    innerPair660RoundedFacts leaf5535RoundedFacts (by rfl)

private theorem leaf5535FlatSound : Sound leaf5535Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5535CertificateValid
    leaf5535InnerLogValid leaf5535CoversExact leaf5535LowerChecked

private noncomputable def leaf5536Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (45/128), chiHi := (91/256) }

private noncomputable def leaf5536Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871343/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356826368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1268174835/1073741824) }, upper := { exponent := 1, mantissa := (19567/16384) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi299LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715548927/68713652736) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf5536InnerLog : WideLogData :=
  innerPair575Data

set_option maxRecDepth 1000000 in
private theorem leaf5536LocalValidity :
    LeafFacts leaf5536Box leaf5536Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5536Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356826368) }) = true
      norm_num [leaf5536Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5536CertificateValid :
    WideCertificateValid leaf5536Box leaf5536Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi299ValidityFacts
    leaf5536LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5536CoverageChecked :
    coverageCheck (innerAD leaf5536Box) leaf5536InnerLog = true := by
  rfl'

private theorem leaf5536InnerLogValid :
    leaf5536InnerLog.Valid 8 (innerAD leaf5536Box) :=
  wideLogDataValid_of_cachedCheck endpoint299PositiveFacts
    endpoint304PositiveFacts.valid leaf5536CoverageChecked

private noncomputable def leaf5536InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453693/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5536InputLogOnePlusV_eq :
    leaf5536InputLogOnePlusV = outerEnclosure 24
      (leaf5536Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5536RoundedFacts : LeafRoundedFacts 8
    leaf5536Certificate.logOnePlusV leaf5536InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5536InputLogOnePlusV_eq }

private noncomputable def leaf5536Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi299InputQChi innerPair575Input
    leaf5536InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5536LowerChecked :
    lowerCheck 24 leaf5536Box leaf5536Inputs = true := by
  rfl'

private theorem leaf5536CoversExact : CoversExact 8
    leaf5536Box leaf5536Certificate leaf5536InnerLog leaf5536Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi299RoundedFacts
    innerPair575RoundedFacts leaf5536RoundedFacts (by rfl)

private theorem leaf5536FlatSound : Sound leaf5536Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5536CertificateValid
    leaf5536InnerLogValid leaf5536CoversExact leaf5536LowerChecked

private noncomputable def leaf5537Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (91/256), chiHi := (23/64) }

private noncomputable def leaf5537Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871345/536870912) }, vSqrt := { lower := (8191/8192), upper := (2021101327/2020987904) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1276300801/1073741824) }, upper := { exponent := 1, mantissa := (4923/4096) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi300LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (4042089231/4041975808) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf5537InnerLog : WideLogData :=
  innerPair282Data

set_option maxRecDepth 1000000 in
private theorem leaf5537LocalValidity :
    LeafFacts leaf5537Box leaf5537Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5537Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (2021101327/2020987904) }) = true
      norm_num [leaf5537Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5537CertificateValid :
    WideCertificateValid leaf5537Box leaf5537Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi300ValidityFacts
    leaf5537LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5537CoverageChecked :
    coverageCheck (innerAD leaf5537Box) leaf5537InnerLog = true := by
  rfl'

private theorem leaf5537InnerLogValid :
    leaf5537InnerLog.Valid 8 (innerAD leaf5537Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint305PositiveFacts.valid leaf5537CoverageChecked

private noncomputable def leaf5537InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726847/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf5537InputLogOnePlusV_eq :
    leaf5537InputLogOnePlusV = outerEnclosure 24
      (leaf5537Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5537RoundedFacts : LeafRoundedFacts 8
    leaf5537Certificate.logOnePlusV leaf5537InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5537InputLogOnePlusV_eq }

private noncomputable def leaf5537Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi300InputQChi innerPair282Input
    leaf5537InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5537LowerChecked :
    lowerCheck 24 leaf5537Box leaf5537Inputs = true := by
  rfl'

private theorem leaf5537CoversExact : CoversExact 8
    leaf5537Box leaf5537Certificate leaf5537InnerLog leaf5537Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi300RoundedFacts
    innerPair282RoundedFacts leaf5537RoundedFacts (by rfl)

private theorem leaf5537FlatSound : Sound leaf5537Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5537CertificateValid
    leaf5537InnerLogValid leaf5537CoversExact leaf5537LowerChecked

private noncomputable def leaf5538Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (45/128), chiHi := (91/256) }

private noncomputable def leaf5538Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871345/536870912) }, vSqrt := { lower := (8191/8192), upper := (2021101327/2020988416) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1274072713/1073741824) }, upper := { exponent := 1, mantissa := (9829/8192) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi299LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (4042089743/4041976832) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf5538InnerLog : WideLogData :=
  innerPair661Data

set_option maxRecDepth 1000000 in
private theorem leaf5538LocalValidity :
    LeafFacts leaf5538Box leaf5538Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5538Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (2021101327/2020988416) }) = true
      norm_num [leaf5538Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5538CertificateValid :
    WideCertificateValid leaf5538Box leaf5538Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi299ValidityFacts
    leaf5538LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5538CoverageChecked :
    coverageCheck (innerAD leaf5538Box) leaf5538InnerLog = true := by
  rfl'

private theorem leaf5538InnerLogValid :
    leaf5538InnerLog.Valid 8 (innerAD leaf5538Box) :=
  wideLogDataValid_of_cachedCheck endpoint408PositiveFacts
    endpoint409PositiveFacts.valid leaf5538CoverageChecked

private noncomputable def leaf5538InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629549/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5538InputLogOnePlusV_eq :
    leaf5538InputLogOnePlusV = outerEnclosure 24
      (leaf5538Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5538RoundedFacts : LeafRoundedFacts 8
    leaf5538Certificate.logOnePlusV leaf5538InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5538InputLogOnePlusV_eq }

private noncomputable def leaf5538Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi299InputQChi innerPair661Input
    leaf5538InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5538LowerChecked :
    lowerCheck 24 leaf5538Box leaf5538Inputs = true := by
  rfl'

private theorem leaf5538CoversExact : CoversExact 8
    leaf5538Box leaf5538Certificate leaf5538InnerLog leaf5538Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi299RoundedFacts
    innerPair661RoundedFacts leaf5538RoundedFacts (by rfl)

private theorem leaf5538FlatSound : Sound leaf5538Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5538CertificateValid
    leaf5538InnerLogValid leaf5538CoversExact leaf5538LowerChecked

private noncomputable def leaf5539Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (91/256), chiHi := (23/64) }

private noncomputable def leaf5539Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871347/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356770816) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1282264211/1073741824) }, upper := { exponent := 1, mantissa := (2473/2048) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi300LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715493375/68713541632) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf5539InnerLog : WideLogData :=
  innerPair283Data

set_option maxRecDepth 1000000 in
private theorem leaf5539LocalValidity :
    LeafFacts leaf5539Box leaf5539Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5539Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356770816) }) = true
      norm_num [leaf5539Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5539CertificateValid :
    WideCertificateValid leaf5539Box leaf5539Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi300ValidityFacts
    leaf5539LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5539CoverageChecked :
    coverageCheck (innerAD leaf5539Box) leaf5539InnerLog = true := by
  rfl'

private theorem leaf5539InnerLogValid :
    leaf5539InnerLog.Valid 8 (innerAD leaf5539Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint308PositiveFacts.valid leaf5539CoverageChecked

private noncomputable def leaf5539InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629557/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5539InputLogOnePlusV_eq :
    leaf5539InputLogOnePlusV = outerEnclosure 24
      (leaf5539Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5539RoundedFacts : LeafRoundedFacts 8
    leaf5539Certificate.logOnePlusV leaf5539InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5539InputLogOnePlusV_eq }

private noncomputable def leaf5539Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi300InputQChi innerPair283Input
    leaf5539InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5539LowerChecked :
    lowerCheck 24 leaf5539Box leaf5539Inputs = true := by
  rfl'

private theorem leaf5539CoversExact : CoversExact 8
    leaf5539Box leaf5539Certificate leaf5539InnerLog leaf5539Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi300RoundedFacts
    innerPair283RoundedFacts leaf5539RoundedFacts (by rfl)

private theorem leaf5539FlatSound : Sound leaf5539Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5539CertificateValid
    leaf5539InnerLogValid leaf5539CoversExact leaf5539LowerChecked

private noncomputable def leaf5540Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (11/32), chiHi := (89/256) }

private noncomputable def leaf5540Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742507/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68713712384) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2526946007/2147483648) }, upper := { exponent := 1, mantissa := (38901/32768) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi297LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431124735/137427424768) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf5540InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf5540LocalValidity :
    LeafFacts leaf5540Box leaf5540Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5540Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68713712384) }) = true
      norm_num [leaf5540Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5540CertificateValid :
    WideCertificateValid leaf5540Box leaf5540Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi297ValidityFacts
    leaf5540LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5540CoverageChecked :
    coverageCheck (innerAD leaf5540Box) leaf5540InnerLog = true := by
  rfl'

private theorem leaf5540InnerLogValid :
    leaf5540InnerLog.Valid 8 (innerAD leaf5540Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf5540CoverageChecked

private noncomputable def leaf5540InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907383/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5540InputLogOnePlusV_eq :
    leaf5540InputLogOnePlusV = outerEnclosure 24
      (leaf5540Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5540RoundedFacts : LeafRoundedFacts 8
    leaf5540Certificate.logOnePlusV leaf5540InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5540InputLogOnePlusV_eq }

private noncomputable def leaf5540Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi297InputQChi innerPair272Input
    leaf5540InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5540LowerChecked :
    lowerCheck 24 leaf5540Box leaf5540Inputs = true := by
  rfl'

private theorem leaf5540CoversExact : CoversExact 8
    leaf5540Box leaf5540Certificate leaf5540InnerLog leaf5540Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi297RoundedFacts
    innerPair272RoundedFacts leaf5540RoundedFacts (by rfl)

private theorem leaf5540FlatSound : Sound leaf5540Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5540CertificateValid
    leaf5540InnerLogValid leaf5540CoversExact leaf5540LowerChecked

private noncomputable def leaf5541Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (11/32), chiHi := (89/256) }

private noncomputable def leaf5541Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742509/1073741824) }, vSqrt := { lower := (8191/8192), upper := (7635268039/7634854400) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2532712821/2147483648) }, upper := { exponent := 1, mantissa := (19495/16384) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi297LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (15270122439/15269708800) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf5541InnerLog : WideLogData :=
  innerPair273Data

set_option maxRecDepth 1000000 in
private theorem leaf5541LocalValidity :
    LeafFacts leaf5541Box leaf5541Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5541Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (7635268039/7634854400) }) = true
      norm_num [leaf5541Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5541CertificateValid :
    WideCertificateValid leaf5541Box leaf5541Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi297ValidityFacts
    leaf5541LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5541CoverageChecked :
    coverageCheck (innerAD leaf5541Box) leaf5541InnerLog = true := by
  rfl'

private theorem leaf5541InnerLogValid :
    leaf5541InnerLog.Valid 8 (innerAD leaf5541Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint78PositiveFacts.valid leaf5541CoverageChecked

private noncomputable def leaf5541InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629535/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5541InputLogOnePlusV_eq :
    leaf5541InputLogOnePlusV = outerEnclosure 24
      (leaf5541Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5541RoundedFacts : LeafRoundedFacts 8
    leaf5541Certificate.logOnePlusV leaf5541InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5541InputLogOnePlusV_eq }

private noncomputable def leaf5541Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi297InputQChi innerPair273Input
    leaf5541InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5541LowerChecked :
    lowerCheck 24 leaf5541Box leaf5541Inputs = true := by
  rfl'

private theorem leaf5541CoversExact : CoversExact 8
    leaf5541Box leaf5541Certificate leaf5541InnerLog leaf5541Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi297RoundedFacts
    innerPair273RoundedFacts leaf5541RoundedFacts (by rfl)

private theorem leaf5541FlatSound : Sound leaf5541Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5541CertificateValid
    leaf5541InnerLogValid leaf5541CoversExact leaf5541LowerChecked

private noncomputable def leaf5542Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (89/256), chiHi := (45/128) }

private noncomputable def leaf5542Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742509/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68713647616) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2543460069/2147483648) }, upper := { exponent := 1, mantissa := (19577/16384) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi298LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431059967/137427295232) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf5542InnerLog : WideLogData :=
  innerPair273Data

set_option maxRecDepth 1000000 in
private theorem leaf5542LocalValidity :
    LeafFacts leaf5542Box leaf5542Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5542Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68713647616) }) = true
      norm_num [leaf5542Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5542CertificateValid :
    WideCertificateValid leaf5542Box leaf5542Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi298ValidityFacts
    leaf5542LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5542CoverageChecked :
    coverageCheck (innerAD leaf5542Box) leaf5542InnerLog = true := by
  rfl'

private theorem leaf5542InnerLogValid :
    leaf5542InnerLog.Valid 8 (innerAD leaf5542Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint78PositiveFacts.valid leaf5542CoverageChecked

private noncomputable def leaf5542InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907385/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5542InputLogOnePlusV_eq :
    leaf5542InputLogOnePlusV = outerEnclosure 24
      (leaf5542Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5542RoundedFacts : LeafRoundedFacts 8
    leaf5542Certificate.logOnePlusV leaf5542InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5542InputLogOnePlusV_eq }

private noncomputable def leaf5542Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi298InputQChi innerPair273Input
    leaf5542InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5542LowerChecked :
    lowerCheck 24 leaf5542Box leaf5542Inputs = true := by
  rfl'

private theorem leaf5542CoversExact : CoversExact 8
    leaf5542Box leaf5542Certificate leaf5542InnerLog leaf5542Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi298RoundedFacts
    innerPair273RoundedFacts leaf5542RoundedFacts (by rfl)

private theorem leaf5542FlatSound : Sound leaf5542Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5542CertificateValid
    leaf5542InnerLogValid leaf5542CoversExact leaf5542LowerChecked

private noncomputable def leaf5543Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (89/256), chiHi := (45/128) }

private noncomputable def leaf5543Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742511/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68713624576) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2549292415/2147483648) }, upper := { exponent := 1, mantissa := (9811/8192) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi298LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431036927/137427249152) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf5543InnerLog : WideLogData :=
  innerPair273Data

set_option maxRecDepth 1000000 in
private theorem leaf5543LocalValidity :
    LeafFacts leaf5543Box leaf5543Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5543Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68713624576) }) = true
      norm_num [leaf5543Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5543CertificateValid :
    WideCertificateValid leaf5543Box leaf5543Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi298ValidityFacts
    leaf5543LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5543CoverageChecked :
    coverageCheck (innerAD leaf5543Box) leaf5543InnerLog = true := by
  rfl'

private theorem leaf5543InnerLogValid :
    leaf5543InnerLog.Valid 8 (innerAD leaf5543Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint78PositiveFacts.valid leaf5543CoverageChecked

private noncomputable def leaf5543InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629543/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5543InputLogOnePlusV_eq :
    leaf5543InputLogOnePlusV = outerEnclosure 24
      (leaf5543Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5543RoundedFacts : LeafRoundedFacts 8
    leaf5543Certificate.logOnePlusV leaf5543InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5543InputLogOnePlusV_eq }

private noncomputable def leaf5543Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi298InputQChi innerPair273Input
    leaf5543InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5543LowerChecked :
    lowerCheck 24 leaf5543Box leaf5543Inputs = true := by
  rfl'

private theorem leaf5543CoversExact : CoversExact 8
    leaf5543Box leaf5543Certificate leaf5543InnerLog leaf5543Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi298RoundedFacts
    innerPair273RoundedFacts leaf5543RoundedFacts (by rfl)

private theorem leaf5543FlatSound : Sound leaf5543Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5543CertificateValid
    leaf5543InnerLogValid leaf5543CoversExact leaf5543LowerChecked

private noncomputable def leaf5544Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (11/32), chiHi := (89/256) }

private noncomputable def leaf5544Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742511/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68713666816) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2538479635/2147483648) }, upper := { exponent := 1, mantissa := (39079/32768) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi297LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431079167/137427333632) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf5544InnerLog : WideLogData :=
  innerPair273Data

set_option maxRecDepth 1000000 in
private theorem leaf5544LocalValidity :
    LeafFacts leaf5544Box leaf5544Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5544Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68713666816) }) = true
      norm_num [leaf5544Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5544CertificateValid :
    WideCertificateValid leaf5544Box leaf5544Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi297ValidityFacts
    leaf5544LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5544CoverageChecked :
    coverageCheck (innerAD leaf5544Box) leaf5544InnerLog = true := by
  rfl'

private theorem leaf5544InnerLogValid :
    leaf5544InnerLog.Valid 8 (innerAD leaf5544Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint78PositiveFacts.valid leaf5544CoverageChecked

private noncomputable def leaf5544InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814769/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5544InputLogOnePlusV_eq :
    leaf5544InputLogOnePlusV = outerEnclosure 24
      (leaf5544Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5544RoundedFacts : LeafRoundedFacts 8
    leaf5544Certificate.logOnePlusV leaf5544InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5544InputLogOnePlusV_eq }

private noncomputable def leaf5544Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi297InputQChi innerPair273Input
    leaf5544InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5544LowerChecked :
    lowerCheck 24 leaf5544Box leaf5544Inputs = true := by
  rfl'

private theorem leaf5544CoversExact : CoversExact 8
    leaf5544Box leaf5544Certificate leaf5544InnerLog leaf5544Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi297RoundedFacts
    innerPair273RoundedFacts leaf5544RoundedFacts (by rfl)

private theorem leaf5544FlatSound : Sound leaf5544Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5544CertificateValid
    leaf5544InnerLogValid leaf5544CoversExact leaf5544LowerChecked

private noncomputable def leaf5545Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (11/32), chiHi := (89/256) }

private noncomputable def leaf5545Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742513/1073741824) }, vSqrt := { lower := (65527/65536), upper := (68717412351/68713644032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2544246449/2147483648) }, upper := { exponent := 1, mantissa := (153/128) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi297LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (137431056383/137427288064) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf5545InnerLog : WideLogData :=
  innerPair273Data

set_option maxRecDepth 1000000 in
private theorem leaf5545LocalValidity :
    LeafFacts leaf5545Box leaf5545Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5545Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (68717412351/68713644032) }) = true
      norm_num [leaf5545Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5545CertificateValid :
    WideCertificateValid leaf5545Box leaf5545Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi297ValidityFacts
    leaf5545LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5545CoverageChecked :
    coverageCheck (innerAD leaf5545Box) leaf5545InnerLog = true := by
  rfl'

private theorem leaf5545InnerLogValid :
    leaf5545InnerLog.Valid 8 (innerAD leaf5545Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint78PositiveFacts.valid leaf5545CoverageChecked

private noncomputable def leaf5545InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629541/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5545InputLogOnePlusV_eq :
    leaf5545InputLogOnePlusV = outerEnclosure 24
      (leaf5545Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5545RoundedFacts : LeafRoundedFacts 8
    leaf5545Certificate.logOnePlusV leaf5545InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5545InputLogOnePlusV_eq }

private noncomputable def leaf5545Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi297InputQChi innerPair273Input
    leaf5545InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5545LowerChecked :
    lowerCheck 24 leaf5545Box leaf5545Inputs = true := by
  rfl'

private theorem leaf5545CoversExact : CoversExact 8
    leaf5545Box leaf5545Certificate leaf5545InnerLog leaf5545Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi297RoundedFacts
    innerPair273RoundedFacts leaf5545RoundedFacts (by rfl)

private theorem leaf5545FlatSound : Sound leaf5545Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5545CertificateValid
    leaf5545InnerLogValid leaf5545CoversExact leaf5545LowerChecked

private noncomputable def leaf5546Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (89/256), chiHi := (45/128) }

private noncomputable def leaf5546Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742513/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68713601536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2555124761/2147483648) }, upper := { exponent := 1, mantissa := (19667/16384) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi298LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431013887/137427203072) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf5546InnerLog : WideLogData :=
  innerPair278Data

set_option maxRecDepth 1000000 in
private theorem leaf5546LocalValidity :
    LeafFacts leaf5546Box leaf5546Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5546Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68713601536) }) = true
      norm_num [leaf5546Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5546CertificateValid :
    WideCertificateValid leaf5546Box leaf5546Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi298ValidityFacts
    leaf5546LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5546CoverageChecked :
    coverageCheck (innerAD leaf5546Box) leaf5546InnerLog = true := by
  rfl'

private theorem leaf5546InnerLogValid :
    leaf5546InnerLog.Valid 8 (innerAD leaf5546Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint78PositiveFacts.valid leaf5546CoverageChecked

private noncomputable def leaf5546InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814773/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5546InputLogOnePlusV_eq :
    leaf5546InputLogOnePlusV = outerEnclosure 24
      (leaf5546Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5546RoundedFacts : LeafRoundedFacts 8
    leaf5546Certificate.logOnePlusV leaf5546InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5546InputLogOnePlusV_eq }

private noncomputable def leaf5546Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi298InputQChi innerPair278Input
    leaf5546InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5546LowerChecked :
    lowerCheck 24 leaf5546Box leaf5546Inputs = true := by
  rfl'

private theorem leaf5546CoversExact : CoversExact 8
    leaf5546Box leaf5546Certificate leaf5546InnerLog leaf5546Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi298RoundedFacts
    innerPair278RoundedFacts leaf5546RoundedFacts (by rfl)

private theorem leaf5546FlatSound : Sound leaf5546Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5546CertificateValid
    leaf5546InnerLogValid leaf5546CoversExact leaf5546LowerChecked

private noncomputable def leaf5547Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (89/256), chiHi := (45/128) }

private noncomputable def leaf5547Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742515/1073741824) }, vSqrt := { lower := (65527/65536), upper := (68717412351/68713578496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2560957107/2147483648) }, upper := { exponent := 1, mantissa := (77/64) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi298LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (137430990847/137427156992) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf5547InnerLog : WideLogData :=
  innerPair278Data

set_option maxRecDepth 1000000 in
private theorem leaf5547LocalValidity :
    LeafFacts leaf5547Box leaf5547Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5547Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (68717412351/68713578496) }) = true
      norm_num [leaf5547Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5547CertificateValid :
    WideCertificateValid leaf5547Box leaf5547Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi298ValidityFacts
    leaf5547LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5547CoverageChecked :
    coverageCheck (innerAD leaf5547Box) leaf5547InnerLog = true := by
  rfl'

private theorem leaf5547InnerLogValid :
    leaf5547InnerLog.Valid 8 (innerAD leaf5547Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint78PositiveFacts.valid leaf5547CoverageChecked

private noncomputable def leaf5547InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629549/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5547InputLogOnePlusV_eq :
    leaf5547InputLogOnePlusV = outerEnclosure 24
      (leaf5547Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5547RoundedFacts : LeafRoundedFacts 8
    leaf5547Certificate.logOnePlusV leaf5547InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5547InputLogOnePlusV_eq }

private noncomputable def leaf5547Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi298InputQChi innerPair278Input
    leaf5547InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5547LowerChecked :
    lowerCheck 24 leaf5547Box leaf5547Inputs = true := by
  rfl'

private theorem leaf5547CoversExact : CoversExact 8
    leaf5547Box leaf5547Certificate leaf5547InnerLog leaf5547Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi298RoundedFacts
    innerPair278RoundedFacts leaf5547RoundedFacts (by rfl)

private theorem leaf5547FlatSound : Sound leaf5547Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5547CertificateValid
    leaf5547InnerLogValid leaf5547CoversExact leaf5547LowerChecked

private noncomputable def leaf5548Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (45/128), chiHi := (91/256) }

private noncomputable def leaf5548Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871347/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356779776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1279970591/1073741824) }, upper := { exponent := 1, mantissa := (19749/16384) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi299LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715502335/68713559552) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf5548InnerLog : WideLogData :=
  innerPair662Data

set_option maxRecDepth 1000000 in
private theorem leaf5548LocalValidity :
    LeafFacts leaf5548Box leaf5548Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5548Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356779776) }) = true
      norm_num [leaf5548Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5548CertificateValid :
    WideCertificateValid leaf5548Box leaf5548Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi299ValidityFacts
    leaf5548LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5548CoverageChecked :
    coverageCheck (innerAD leaf5548Box) leaf5548InnerLog = true := by
  rfl'

private theorem leaf5548InnerLogValid :
    leaf5548InnerLog.Valid 8 (innerAD leaf5548Box) :=
  wideLogDataValid_of_cachedCheck endpoint410PositiveFacts
    endpoint411PositiveFacts.valid leaf5548CoverageChecked

private noncomputable def leaf5548InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629555/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5548InputLogOnePlusV_eq :
    leaf5548InputLogOnePlusV = outerEnclosure 24
      (leaf5548Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5548RoundedFacts : LeafRoundedFacts 8
    leaf5548Certificate.logOnePlusV leaf5548InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5548InputLogOnePlusV_eq }

private noncomputable def leaf5548Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi299InputQChi innerPair662Input
    leaf5548InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5548LowerChecked :
    lowerCheck 24 leaf5548Box leaf5548Inputs = true := by
  rfl'

private theorem leaf5548CoversExact : CoversExact 8
    leaf5548Box leaf5548Certificate leaf5548InnerLog leaf5548Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi299RoundedFacts
    innerPair662RoundedFacts leaf5548RoundedFacts (by rfl)

private theorem leaf5548FlatSound : Sound leaf5548Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5548CertificateValid
    leaf5548InnerLogValid leaf5548CoversExact leaf5548LowerChecked

private noncomputable def leaf5549Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (91/256), chiHi := (23/64) }

private noncomputable def leaf5549Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871349/536870912) }, vSqrt := { lower := (8191/8192), upper := (4908388937/4908106752) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1288227621/1073741824) }, upper := { exponent := 1, mantissa := (4969/4096) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi300LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (9816495689/9816213504) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf5549InnerLog : WideLogData :=
  innerPair663Data

set_option maxRecDepth 1000000 in
private theorem leaf5549LocalValidity :
    LeafFacts leaf5549Box leaf5549Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5549Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4908388937/4908106752) }) = true
      norm_num [leaf5549Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5549CertificateValid :
    WideCertificateValid leaf5549Box leaf5549Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi300ValidityFacts
    leaf5549LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5549CoverageChecked :
    coverageCheck (innerAD leaf5549Box) leaf5549InnerLog = true := by
  rfl'

private theorem leaf5549InnerLogValid :
    leaf5549InnerLog.Valid 8 (innerAD leaf5549Box) :=
  wideLogDataValid_of_cachedCheck endpoint412PositiveFacts
    endpoint413PositiveFacts.valid leaf5549CoverageChecked

private noncomputable def leaf5549InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629563/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5549InputLogOnePlusV_eq :
    leaf5549InputLogOnePlusV = outerEnclosure 24
      (leaf5549Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5549RoundedFacts : LeafRoundedFacts 8
    leaf5549Certificate.logOnePlusV leaf5549InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5549InputLogOnePlusV_eq }

private noncomputable def leaf5549Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi300InputQChi innerPair663Input
    leaf5549InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5549LowerChecked :
    lowerCheck 24 leaf5549Box leaf5549Inputs = true := by
  rfl'

private theorem leaf5549CoversExact : CoversExact 8
    leaf5549Box leaf5549Certificate leaf5549InnerLog leaf5549Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi300RoundedFacts
    innerPair663RoundedFacts leaf5549RoundedFacts (by rfl)

private theorem leaf5549FlatSound : Sound leaf5549Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5549CertificateValid
    leaf5549InnerLogValid leaf5549CoversExact leaf5549LowerChecked

private noncomputable def leaf5550Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (45/128), chiHi := (91/256) }

private noncomputable def leaf5550Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742515/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68713536256) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2571769887/2147483648) }, upper := { exponent := 1, mantissa := (39589/32768) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi299LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137430948607/137427072512) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf5550InnerLog : WideLogData :=
  innerPair278Data

set_option maxRecDepth 1000000 in
private theorem leaf5550LocalValidity :
    LeafFacts leaf5550Box leaf5550Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5550Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68713536256) }) = true
      norm_num [leaf5550Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5550CertificateValid :
    WideCertificateValid leaf5550Box leaf5550Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi299ValidityFacts
    leaf5550LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5550CoverageChecked :
    coverageCheck (innerAD leaf5550Box) leaf5550InnerLog = true := by
  rfl'

private theorem leaf5550InnerLogValid :
    leaf5550InnerLog.Valid 8 (innerAD leaf5550Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint78PositiveFacts.valid leaf5550CoverageChecked

private noncomputable def leaf5550InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814777/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5550InputLogOnePlusV_eq :
    leaf5550InputLogOnePlusV = outerEnclosure 24
      (leaf5550Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5550RoundedFacts : LeafRoundedFacts 8
    leaf5550Certificate.logOnePlusV leaf5550InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5550InputLogOnePlusV_eq }

private noncomputable def leaf5550Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi299InputQChi innerPair278Input
    leaf5550InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5550LowerChecked :
    lowerCheck 24 leaf5550Box leaf5550Inputs = true := by
  rfl'

private theorem leaf5550CoversExact : CoversExact 8
    leaf5550Box leaf5550Certificate leaf5550InnerLog leaf5550Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi299RoundedFacts
    innerPair278RoundedFacts leaf5550RoundedFacts (by rfl)

private theorem leaf5550FlatSound : Sound leaf5550Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5550CertificateValid
    leaf5550InnerLogValid leaf5550CoversExact leaf5550LowerChecked

private noncomputable def leaf5551Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (45/128), chiHi := (91/256) }

private noncomputable def leaf5551Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742517/1073741824) }, vSqrt := { lower := (65527/65536), upper := (22905804117/22904504320) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2577667765/2147483648) }, upper := { exponent := 1, mantissa := (155/128) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi299LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (45810308437/45809008640) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf5551InnerLog : WideLogData :=
  innerPair278Data

set_option maxRecDepth 1000000 in
private theorem leaf5551LocalValidity :
    LeafFacts leaf5551Box leaf5551Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5551Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (22905804117/22904504320) }) = true
      norm_num [leaf5551Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5551CertificateValid :
    WideCertificateValid leaf5551Box leaf5551Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi299ValidityFacts
    leaf5551LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5551CoverageChecked :
    coverageCheck (innerAD leaf5551Box) leaf5551InnerLog = true := by
  rfl'

private theorem leaf5551InnerLogValid :
    leaf5551InnerLog.Valid 8 (innerAD leaf5551Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint78PositiveFacts.valid leaf5551CoverageChecked

private noncomputable def leaf5551InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629557/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5551InputLogOnePlusV_eq :
    leaf5551InputLogOnePlusV = outerEnclosure 24
      (leaf5551Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5551RoundedFacts : LeafRoundedFacts 8
    leaf5551Certificate.logOnePlusV leaf5551InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5551InputLogOnePlusV_eq }

private noncomputable def leaf5551Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi299InputQChi innerPair278Input
    leaf5551InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5551LowerChecked :
    lowerCheck 24 leaf5551Box leaf5551Inputs = true := by
  rfl'

private theorem leaf5551CoversExact : CoversExact 8
    leaf5551Box leaf5551Certificate leaf5551InnerLog leaf5551Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi299RoundedFacts
    innerPair278RoundedFacts leaf5551RoundedFacts (by rfl)

private theorem leaf5551FlatSound : Sound leaf5551Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5551CertificateValid
    leaf5551InnerLogValid leaf5551CoversExact leaf5551LowerChecked

private noncomputable def leaf5552Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (91/256), chiHi := (23/64) }

private noncomputable def leaf5552Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871351/536870912) }, vSqrt := { lower := (65527/65536), upper := (34358722559/34356723712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1294191031/1073741824) }, upper := { exponent := 1, mantissa := (39/32) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi300LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (68715446271/68713447424) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf5552InnerLog : WideLogData :=
  innerPair278Data

set_option maxRecDepth 1000000 in
private theorem leaf5552LocalValidity :
    LeafFacts leaf5552Box leaf5552Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5552Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (34358722559/34356723712) }) = true
      norm_num [leaf5552Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5552CertificateValid :
    WideCertificateValid leaf5552Box leaf5552Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi300ValidityFacts
    leaf5552LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5552CoverageChecked :
    coverageCheck (innerAD leaf5552Box) leaf5552InnerLog = true := by
  rfl'

private theorem leaf5552InnerLogValid :
    leaf5552InnerLog.Valid 8 (innerAD leaf5552Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint78PositiveFacts.valid leaf5552CoverageChecked

private noncomputable def leaf5552InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629569/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5552InputLogOnePlusV_eq :
    leaf5552InputLogOnePlusV = outerEnclosure 24
      (leaf5552Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5552RoundedFacts : LeafRoundedFacts 8
    leaf5552Certificate.logOnePlusV leaf5552InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5552InputLogOnePlusV_eq }

private noncomputable def leaf5552Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi300InputQChi innerPair278Input
    leaf5552InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5552LowerChecked :
    lowerCheck 24 leaf5552Box leaf5552Inputs = true := by
  rfl'

private theorem leaf5552CoversExact : CoversExact 8
    leaf5552Box leaf5552Certificate leaf5552InnerLog leaf5552Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi300RoundedFacts
    innerPair278RoundedFacts leaf5552RoundedFacts (by rfl)

private theorem leaf5552FlatSound : Sound leaf5552Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5552CertificateValid
    leaf5552InnerLogValid leaf5552CoversExact leaf5552LowerChecked

private noncomputable def leaf5553Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (23/64), chiHi := (93/256) }

private noncomputable def leaf5553Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871347/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356762368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1284426767/1073741824) }, upper := { exponent := 1, mantissa := (19817/16384) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi301LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715484927/68713524736) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf5553InnerLog : WideLogData :=
  innerPair585Data

set_option maxRecDepth 1000000 in
private theorem leaf5553LocalValidity :
    LeafFacts leaf5553Box leaf5553Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5553Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356762368) }) = true
      norm_num [leaf5553Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5553CertificateValid :
    WideCertificateValid leaf5553Box leaf5553Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi301ValidityFacts
    leaf5553LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5553CoverageChecked :
    coverageCheck (innerAD leaf5553Box) leaf5553InnerLog = true := by
  rfl'

private theorem leaf5553InnerLogValid :
    leaf5553InnerLog.Valid 8 (innerAD leaf5553Box) :=
  wideLogDataValid_of_cachedCheck endpoint304PositiveFacts
    endpoint308PositiveFacts.valid leaf5553CoverageChecked

private noncomputable def leaf5553InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629559/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5553InputLogOnePlusV_eq :
    leaf5553InputLogOnePlusV = outerEnclosure 24
      (leaf5553Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5553RoundedFacts : LeafRoundedFacts 8
    leaf5553Certificate.logOnePlusV leaf5553InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5553InputLogOnePlusV_eq }

private noncomputable def leaf5553Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi301InputQChi innerPair585Input
    leaf5553InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5553LowerChecked :
    lowerCheck 24 leaf5553Box leaf5553Inputs = true := by
  rfl'

private theorem leaf5553CoversExact : CoversExact 8
    leaf5553Box leaf5553Certificate leaf5553InnerLog leaf5553Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi301RoundedFacts
    innerPair585RoundedFacts leaf5553RoundedFacts (by rfl)

private theorem leaf5553FlatSound : Sound leaf5553Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5553CertificateValid
    leaf5553InnerLogValid leaf5553CoversExact leaf5553LowerChecked

private noncomputable def leaf5554Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (93/256), chiHi := (47/128) }

private noncomputable def leaf5554Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871349/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356730368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1292552733/1073741824) }, upper := { exponent := 1, mantissa := (9971/8192) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi302LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715452927/68713460736) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf5554InnerLog : WideLogData :=
  innerPair278Data

set_option maxRecDepth 1000000 in
private theorem leaf5554LocalValidity :
    LeafFacts leaf5554Box leaf5554Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5554Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356730368) }) = true
      norm_num [leaf5554Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5554CertificateValid :
    WideCertificateValid leaf5554Box leaf5554Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi302ValidityFacts
    leaf5554LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5554CoverageChecked :
    coverageCheck (innerAD leaf5554Box) leaf5554InnerLog = true := by
  rfl'

private theorem leaf5554InnerLogValid :
    leaf5554InnerLog.Valid 8 (innerAD leaf5554Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint78PositiveFacts.valid leaf5554CoverageChecked

private noncomputable def leaf5554InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629567/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5554InputLogOnePlusV_eq :
    leaf5554InputLogOnePlusV = outerEnclosure 24
      (leaf5554Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5554RoundedFacts : LeafRoundedFacts 8
    leaf5554Certificate.logOnePlusV leaf5554InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5554InputLogOnePlusV_eq }

private noncomputable def leaf5554Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi302InputQChi innerPair278Input
    leaf5554InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5554LowerChecked :
    lowerCheck 24 leaf5554Box leaf5554Inputs = true := by
  rfl'

private theorem leaf5554CoversExact : CoversExact 8
    leaf5554Box leaf5554Certificate leaf5554InnerLog leaf5554Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi302RoundedFacts
    innerPair278RoundedFacts leaf5554RoundedFacts (by rfl)

private theorem leaf5554FlatSound : Sound leaf5554Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5554CertificateValid
    leaf5554InnerLogValid leaf5554CoversExact leaf5554LowerChecked

private noncomputable def leaf5555Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (23/64), chiHi := (93/256) }

private noncomputable def leaf5555Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871349/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356738560) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1290455709/1073741824) }, upper := { exponent := 1, mantissa := (9955/8192) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi301LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715461119/68713477120) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf5555InnerLog : WideLogData :=
  innerPair278Data

set_option maxRecDepth 1000000 in
private theorem leaf5555LocalValidity :
    LeafFacts leaf5555Box leaf5555Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5555Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356738560) }) = true
      norm_num [leaf5555Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5555CertificateValid :
    WideCertificateValid leaf5555Box leaf5555Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi301ValidityFacts
    leaf5555LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5555CoverageChecked :
    coverageCheck (innerAD leaf5555Box) leaf5555InnerLog = true := by
  rfl'

private theorem leaf5555InnerLogValid :
    leaf5555InnerLog.Valid 8 (innerAD leaf5555Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint78PositiveFacts.valid leaf5555CoverageChecked

private noncomputable def leaf5555InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629565/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5555InputLogOnePlusV_eq :
    leaf5555InputLogOnePlusV = outerEnclosure 24
      (leaf5555Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5555RoundedFacts : LeafRoundedFacts 8
    leaf5555Certificate.logOnePlusV leaf5555InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5555InputLogOnePlusV_eq }

private noncomputable def leaf5555Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi301InputQChi innerPair278Input
    leaf5555InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5555LowerChecked :
    lowerCheck 24 leaf5555Box leaf5555Inputs = true := by
  rfl'

private theorem leaf5555CoversExact : CoversExact 8
    leaf5555Box leaf5555Certificate leaf5555InnerLog leaf5555Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi301RoundedFacts
    innerPair278RoundedFacts leaf5555RoundedFacts (by rfl)

private theorem leaf5555FlatSound : Sound leaf5555Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5555CertificateValid
    leaf5555InnerLogValid leaf5555CoversExact leaf5555LowerChecked

private noncomputable def leaf5556Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (93/256), chiHi := (47/128) }

private noncomputable def leaf5556Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871351/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356706304) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1298647207/1073741824) }, upper := { exponent := 1, mantissa := (5009/4096) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi302LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715428863/68713412608) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf5556InnerLog : WideLogData :=
  innerPair590Data

set_option maxRecDepth 1000000 in
private theorem leaf5556LocalValidity :
    LeafFacts leaf5556Box leaf5556Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5556Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356706304) }) = true
      norm_num [leaf5556Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5556CertificateValid :
    WideCertificateValid leaf5556Box leaf5556Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi302ValidityFacts
    leaf5556LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5556CoverageChecked :
    coverageCheck (innerAD leaf5556Box) leaf5556InnerLog = true := by
  rfl'

private theorem leaf5556InnerLogValid :
    leaf5556InnerLog.Valid 8 (innerAD leaf5556Box) :=
  wideLogDataValid_of_cachedCheck endpoint305PositiveFacts
    endpoint403PositiveFacts.valid leaf5556CoverageChecked

private noncomputable def leaf5556InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629573/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5556InputLogOnePlusV_eq :
    leaf5556InputLogOnePlusV = outerEnclosure 24
      (leaf5556Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5556RoundedFacts : LeafRoundedFacts 8
    leaf5556Certificate.logOnePlusV leaf5556InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5556InputLogOnePlusV_eq }

private noncomputable def leaf5556Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi302InputQChi innerPair590Input
    leaf5556InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5556LowerChecked :
    lowerCheck 24 leaf5556Box leaf5556Inputs = true := by
  rfl'

private theorem leaf5556CoversExact : CoversExact 8
    leaf5556Box leaf5556Certificate leaf5556InnerLog leaf5556Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi302RoundedFacts
    innerPair590RoundedFacts leaf5556RoundedFacts (by rfl)

private theorem leaf5556FlatSound : Sound leaf5556Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5556CertificateValid
    leaf5556InnerLogValid leaf5556CoversExact leaf5556LowerChecked

private noncomputable def leaf5557Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (47/128), chiHi := (95/256) }

private noncomputable def leaf5557Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871351/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356698368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1300678699/1073741824) }, upper := { exponent := 1, mantissa := (20067/16384) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi303LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715420927/68713396736) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf5557InnerLog : WideLogData :=
  innerPair593Data

set_option maxRecDepth 1000000 in
private theorem leaf5557LocalValidity :
    LeafFacts leaf5557Box leaf5557Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5557Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356698368) }) = true
      norm_num [leaf5557Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5557CertificateValid :
    WideCertificateValid leaf5557Box leaf5557Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi303ValidityFacts
    leaf5557LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5557CoverageChecked :
    coverageCheck (innerAD leaf5557Box) leaf5557InnerLog = true := by
  rfl'

private theorem leaf5557InnerLogValid :
    leaf5557InnerLog.Valid 8 (innerAD leaf5557Box) :=
  wideLogDataValid_of_cachedCheck endpoint308PositiveFacts
    endpoint403PositiveFacts.valid leaf5557CoverageChecked

private noncomputable def leaf5557InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629575/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5557InputLogOnePlusV_eq :
    leaf5557InputLogOnePlusV = outerEnclosure 24
      (leaf5557Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5557RoundedFacts : LeafRoundedFacts 8
    leaf5557Certificate.logOnePlusV leaf5557InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5557InputLogOnePlusV_eq }

private noncomputable def leaf5557Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi303InputQChi innerPair593Input
    leaf5557InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5557LowerChecked :
    lowerCheck 24 leaf5557Box leaf5557Inputs = true := by
  rfl'

private theorem leaf5557CoversExact : CoversExact 8
    leaf5557Box leaf5557Certificate leaf5557InnerLog leaf5557Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi303RoundedFacts
    innerPair593RoundedFacts leaf5557RoundedFacts (by rfl)

private theorem leaf5557FlatSound : Sound leaf5557Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5557CertificateValid
    leaf5557InnerLogValid leaf5557CoversExact leaf5557LowerChecked

private noncomputable def leaf5558Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (95/256), chiHi := (3/8) }

private noncomputable def leaf5558Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871353/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356666368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1308804665/1073741824) }, upper := { exponent := 1, mantissa := (631/512) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi304LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715388927/68713332736) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf5558InnerLog : WideLogData :=
  innerPair289Data

set_option maxRecDepth 1000000 in
private theorem leaf5558LocalValidity :
    LeafFacts leaf5558Box leaf5558Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5558Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356666368) }) = true
      norm_num [leaf5558Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5558CertificateValid :
    WideCertificateValid leaf5558Box leaf5558Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi304ValidityFacts
    leaf5558LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5558CoverageChecked :
    coverageCheck (innerAD leaf5558Box) leaf5558InnerLog = true := by
  rfl'

private theorem leaf5558InnerLogValid :
    leaf5558InnerLog.Valid 8 (innerAD leaf5558Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint94PositiveFacts.valid leaf5558CoverageChecked

private noncomputable def leaf5558InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629583/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5558InputLogOnePlusV_eq :
    leaf5558InputLogOnePlusV = outerEnclosure 24
      (leaf5558Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5558RoundedFacts : LeafRoundedFacts 8
    leaf5558Certificate.logOnePlusV leaf5558InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5558InputLogOnePlusV_eq }

private noncomputable def leaf5558Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi304InputQChi innerPair289Input
    leaf5558InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5558LowerChecked :
    lowerCheck 24 leaf5558Box leaf5558Inputs = true := by
  rfl'

private theorem leaf5558CoversExact : CoversExact 8
    leaf5558Box leaf5558Certificate leaf5558InnerLog leaf5558Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi304RoundedFacts
    innerPair289RoundedFacts leaf5558RoundedFacts (by rfl)

private theorem leaf5558FlatSound : Sound leaf5558Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5558CertificateValid
    leaf5558InnerLogValid leaf5558CoversExact leaf5558LowerChecked

private noncomputable def leaf5559Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (47/128), chiHi := (95/256) }

private noncomputable def leaf5559Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871353/536870912) }, vSqrt := { lower := (8191/8192), upper := (1108345889/1108279808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1306838705/1073741824) }, upper := { exponent := 1, mantissa := (10081/8192) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi303LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (2216625697/2216559616) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf5559InnerLog : WideLogData :=
  innerPair592Data

set_option maxRecDepth 1000000 in
private theorem leaf5559LocalValidity :
    LeafFacts leaf5559Box leaf5559Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5559Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (1108345889/1108279808) }) = true
      norm_num [leaf5559Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5559CertificateValid :
    WideCertificateValid leaf5559Box leaf5559Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi303ValidityFacts
    leaf5559LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5559CoverageChecked :
    coverageCheck (innerAD leaf5559Box) leaf5559InnerLog = true := by
  rfl'

private theorem leaf5559InnerLogValid :
    leaf5559InnerLog.Valid 8 (innerAD leaf5559Box) :=
  wideLogDataValid_of_cachedCheck endpoint308PositiveFacts
    endpoint94PositiveFacts.valid leaf5559CoverageChecked

private noncomputable def leaf5559InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629581/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5559InputLogOnePlusV_eq :
    leaf5559InputLogOnePlusV = outerEnclosure 24
      (leaf5559Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5559RoundedFacts : LeafRoundedFacts 8
    leaf5559Certificate.logOnePlusV leaf5559InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5559InputLogOnePlusV_eq }

private noncomputable def leaf5559Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi303InputQChi innerPair592Input
    leaf5559InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5559LowerChecked :
    lowerCheck 24 leaf5559Box leaf5559Inputs = true := by
  rfl'

private theorem leaf5559CoversExact : CoversExact 8
    leaf5559Box leaf5559Certificate leaf5559InnerLog leaf5559Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi303RoundedFacts
    innerPair592RoundedFacts leaf5559RoundedFacts (by rfl)

private theorem leaf5559FlatSound : Sound leaf5559Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5559CertificateValid
    leaf5559InnerLogValid leaf5559CoversExact leaf5559LowerChecked

private noncomputable def leaf5560Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (95/256), chiHi := (3/8) }

private noncomputable def leaf5560Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871355/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356641792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1315030203/1073741824) }, upper := { exponent := 1, mantissa := (317/256) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi304LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715364351/68713283584) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf5560InnerLog : WideLogData :=
  innerPair290Data

set_option maxRecDepth 1000000 in
private theorem leaf5560LocalValidity :
    LeafFacts leaf5560Box leaf5560Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5560Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356641792) }) = true
      norm_num [leaf5560Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5560CertificateValid :
    WideCertificateValid leaf5560Box leaf5560Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi304ValidityFacts
    leaf5560LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5560CoverageChecked :
    coverageCheck (innerAD leaf5560Box) leaf5560InnerLog = true := by
  rfl'

private theorem leaf5560InnerLogValid :
    leaf5560InnerLog.Valid 8 (innerAD leaf5560Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint414PositiveFacts.valid leaf5560CoverageChecked

private noncomputable def leaf5560InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629589/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5560InputLogOnePlusV_eq :
    leaf5560InputLogOnePlusV = outerEnclosure 24
      (leaf5560Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5560RoundedFacts : LeafRoundedFacts 8
    leaf5560Certificate.logOnePlusV leaf5560InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5560InputLogOnePlusV_eq }

private noncomputable def leaf5560Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi304InputQChi innerPair290Input
    leaf5560InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5560LowerChecked :
    lowerCheck 24 leaf5560Box leaf5560Inputs = true := by
  rfl'

private theorem leaf5560CoversExact : CoversExact 8
    leaf5560Box leaf5560Certificate leaf5560InnerLog leaf5560Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi304RoundedFacts
    innerPair290RoundedFacts leaf5560RoundedFacts (by rfl)

private theorem leaf5560FlatSound : Sound leaf5560Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5560CertificateValid
    leaf5560InnerLogValid leaf5560CoversExact leaf5560LowerChecked

private noncomputable def leaf5561Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (23/64), chiHi := (93/256) }

private noncomputable def leaf5561Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871351/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356714752) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1296484651/1073741824) }, upper := { exponent := 1, mantissa := (20003/16384) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi301LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715437311/68713429504) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf5561InnerLog : WideLogData :=
  innerPair670Data

set_option maxRecDepth 1000000 in
private theorem leaf5561LocalValidity :
    LeafFacts leaf5561Box leaf5561Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5561Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356714752) }) = true
      norm_num [leaf5561Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5561CertificateValid :
    WideCertificateValid leaf5561Box leaf5561Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi301ValidityFacts
    leaf5561LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5561CoverageChecked :
    coverageCheck (innerAD leaf5561Box) leaf5561InnerLog = true := by
  rfl'

private theorem leaf5561InnerLogValid :
    leaf5561InnerLog.Valid 8 (innerAD leaf5561Box) :=
  wideLogDataValid_of_cachedCheck endpoint415PositiveFacts
    endpoint416PositiveFacts.valid leaf5561CoverageChecked

private noncomputable def leaf5561InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629571/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5561InputLogOnePlusV_eq :
    leaf5561InputLogOnePlusV = outerEnclosure 24
      (leaf5561Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5561RoundedFacts : LeafRoundedFacts 8
    leaf5561Certificate.logOnePlusV leaf5561InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5561InputLogOnePlusV_eq }

private noncomputable def leaf5561Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi301InputQChi innerPair670Input
    leaf5561InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5561LowerChecked :
    lowerCheck 24 leaf5561Box leaf5561Inputs = true := by
  rfl'

private theorem leaf5561CoversExact : CoversExact 8
    leaf5561Box leaf5561Certificate leaf5561InnerLog leaf5561Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi301RoundedFacts
    innerPair670RoundedFacts leaf5561RoundedFacts (by rfl)

private theorem leaf5561FlatSound : Sound leaf5561Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5561CertificateValid
    leaf5561InnerLogValid leaf5561CoversExact leaf5561LowerChecked

private noncomputable def leaf5562Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (93/256), chiHi := (47/128) }

private noncomputable def leaf5562Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871353/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356682240) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1304741681/1073741824) }, upper := { exponent := 1, mantissa := (10065/8192) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi302LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715404799/68713364480) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf5562InnerLog : WideLogData :=
  innerPair665Data

set_option maxRecDepth 1000000 in
private theorem leaf5562LocalValidity :
    LeafFacts leaf5562Box leaf5562Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5562Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356682240) }) = true
      norm_num [leaf5562Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5562CertificateValid :
    WideCertificateValid leaf5562Box leaf5562Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi302ValidityFacts
    leaf5562LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5562CoverageChecked :
    coverageCheck (innerAD leaf5562Box) leaf5562InnerLog = true := by
  rfl'

private theorem leaf5562InnerLogValid :
    leaf5562InnerLog.Valid 8 (innerAD leaf5562Box) :=
  wideLogDataValid_of_cachedCheck endpoint413PositiveFacts
    endpoint417PositiveFacts.valid leaf5562CoverageChecked

private noncomputable def leaf5562InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629579/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5562InputLogOnePlusV_eq :
    leaf5562InputLogOnePlusV = outerEnclosure 24
      (leaf5562Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5562RoundedFacts : LeafRoundedFacts 8
    leaf5562Certificate.logOnePlusV leaf5562InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5562InputLogOnePlusV_eq }

private noncomputable def leaf5562Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi302InputQChi innerPair665Input
    leaf5562InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5562LowerChecked :
    lowerCheck 24 leaf5562Box leaf5562Inputs = true := by
  rfl'

private theorem leaf5562CoversExact : CoversExact 8
    leaf5562Box leaf5562Certificate leaf5562InnerLog leaf5562Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi302RoundedFacts
    innerPair665RoundedFacts leaf5562RoundedFacts (by rfl)

private theorem leaf5562FlatSound : Sound leaf5562Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5562CertificateValid
    leaf5562InnerLogValid leaf5562CoversExact leaf5562LowerChecked

private noncomputable def leaf5563Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (23/64), chiHi := (93/256) }

private noncomputable def leaf5563Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871353/536870912) }, vSqrt := { lower := (65527/65536), upper := (34358722559/34356690944) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1302513593/1073741824) }, upper := { exponent := 1, mantissa := (157/128) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi301LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (68715413503/68713381888) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf5563InnerLog : WideLogData :=
  innerPair593Data

set_option maxRecDepth 1000000 in
private theorem leaf5563LocalValidity :
    LeafFacts leaf5563Box leaf5563Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5563Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (34358722559/34356690944) }) = true
      norm_num [leaf5563Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5563CertificateValid :
    WideCertificateValid leaf5563Box leaf5563Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi301ValidityFacts
    leaf5563LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5563CoverageChecked :
    coverageCheck (innerAD leaf5563Box) leaf5563InnerLog = true := by
  rfl'

private theorem leaf5563InnerLogValid :
    leaf5563InnerLog.Valid 8 (innerAD leaf5563Box) :=
  wideLogDataValid_of_cachedCheck endpoint308PositiveFacts
    endpoint403PositiveFacts.valid leaf5563CoverageChecked

private noncomputable def leaf5563InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629577/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5563InputLogOnePlusV_eq :
    leaf5563InputLogOnePlusV = outerEnclosure 24
      (leaf5563Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5563RoundedFacts : LeafRoundedFacts 8
    leaf5563Certificate.logOnePlusV leaf5563InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5563InputLogOnePlusV_eq }

private noncomputable def leaf5563Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi301InputQChi innerPair593Input
    leaf5563InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5563LowerChecked :
    lowerCheck 24 leaf5563Box leaf5563Inputs = true := by
  rfl'

private theorem leaf5563CoversExact : CoversExact 8
    leaf5563Box leaf5563Certificate leaf5563InnerLog leaf5563Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi301RoundedFacts
    innerPair593RoundedFacts leaf5563RoundedFacts (by rfl)

private theorem leaf5563FlatSound : Sound leaf5563Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5563CertificateValid
    leaf5563InnerLogValid leaf5563CoversExact leaf5563LowerChecked

private noncomputable def leaf5564Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (93/256), chiHi := (47/128) }

private noncomputable def leaf5564Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871355/536870912) }, vSqrt := { lower := (65527/65536), upper := (1108345889/1108279296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1310836155/1073741824) }, upper := { exponent := 1, mantissa := (79/64) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi302LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (2216625185/2216558592) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf5564InnerLog : WideLogData :=
  innerPair289Data

set_option maxRecDepth 1000000 in
private theorem leaf5564LocalValidity :
    LeafFacts leaf5564Box leaf5564Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5564Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (1108345889/1108279296) }) = true
      norm_num [leaf5564Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5564CertificateValid :
    WideCertificateValid leaf5564Box leaf5564Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi302ValidityFacts
    leaf5564LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5564CoverageChecked :
    coverageCheck (innerAD leaf5564Box) leaf5564InnerLog = true := by
  rfl'

private theorem leaf5564InnerLogValid :
    leaf5564InnerLog.Valid 8 (innerAD leaf5564Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint94PositiveFacts.valid leaf5564CoverageChecked

private noncomputable def leaf5564InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629585/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5564InputLogOnePlusV_eq :
    leaf5564InputLogOnePlusV = outerEnclosure 24
      (leaf5564Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5564RoundedFacts : LeafRoundedFacts 8
    leaf5564Certificate.logOnePlusV leaf5564InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5564InputLogOnePlusV_eq }

private noncomputable def leaf5564Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi302InputQChi innerPair289Input
    leaf5564InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5564LowerChecked :
    lowerCheck 24 leaf5564Box leaf5564Inputs = true := by
  rfl'

private theorem leaf5564CoversExact : CoversExact 8
    leaf5564Box leaf5564Certificate leaf5564InnerLog leaf5564Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi302RoundedFacts
    innerPair289RoundedFacts leaf5564RoundedFacts (by rfl)

private theorem leaf5564FlatSound : Sound leaf5564Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5564CertificateValid
    leaf5564InnerLogValid leaf5564CoversExact leaf5564LowerChecked

private noncomputable def leaf5565Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (47/128), chiHi := (95/256) }

private noncomputable def leaf5565Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871355/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356649728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1312998711/1073741824) }, upper := { exponent := 1, mantissa := (20257/16384) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi303LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715372287/68713299456) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf5565InnerLog : WideLogData :=
  innerPair290Data

set_option maxRecDepth 1000000 in
private theorem leaf5565LocalValidity :
    LeafFacts leaf5565Box leaf5565Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5565Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356649728) }) = true
      norm_num [leaf5565Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5565CertificateValid :
    WideCertificateValid leaf5565Box leaf5565Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi303ValidityFacts
    leaf5565LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5565CoverageChecked :
    coverageCheck (innerAD leaf5565Box) leaf5565InnerLog = true := by
  rfl'

private theorem leaf5565InnerLogValid :
    leaf5565InnerLog.Valid 8 (innerAD leaf5565Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint414PositiveFacts.valid leaf5565CoverageChecked

private noncomputable def leaf5565InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629587/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5565InputLogOnePlusV_eq :
    leaf5565InputLogOnePlusV = outerEnclosure 24
      (leaf5565Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5565RoundedFacts : LeafRoundedFacts 8
    leaf5565Certificate.logOnePlusV leaf5565InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5565InputLogOnePlusV_eq }

private noncomputable def leaf5565Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi303InputQChi innerPair290Input
    leaf5565InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5565LowerChecked :
    lowerCheck 24 leaf5565Box leaf5565Inputs = true := by
  rfl'

private theorem leaf5565CoversExact : CoversExact 8
    leaf5565Box leaf5565Certificate leaf5565InnerLog leaf5565Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi303RoundedFacts
    innerPair290RoundedFacts leaf5565RoundedFacts (by rfl)

private theorem leaf5565FlatSound : Sound leaf5565Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5565CertificateValid
    leaf5565InnerLogValid leaf5565CoversExact leaf5565LowerChecked

private noncomputable def leaf5566Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (95/256), chiHi := (3/8) }

private noncomputable def leaf5566Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871357/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68713234432) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1321255741/1073741824) }, upper := { exponent := 1, mantissa := (637/512) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi304LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429630973/137426468864) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf5566InnerLog : WideLogData :=
  innerPair285Data

set_option maxRecDepth 1000000 in
private theorem leaf5566LocalValidity :
    LeafFacts leaf5566Box leaf5566Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5566Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68713234432) }) = true
      norm_num [leaf5566Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5566CertificateValid :
    WideCertificateValid leaf5566Box leaf5566Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi304ValidityFacts
    leaf5566LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5566CoverageChecked :
    coverageCheck (innerAD leaf5566Box) leaf5566InnerLog = true := by
  rfl'

private theorem leaf5566InnerLogValid :
    leaf5566InnerLog.Valid 8 (innerAD leaf5566Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint79PositiveFacts.valid leaf5566CoverageChecked

private noncomputable def leaf5566InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629467/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5566InputLogOnePlusV_eq :
    leaf5566InputLogOnePlusV = outerEnclosure 24
      (leaf5566Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5566RoundedFacts : LeafRoundedFacts 8
    leaf5566Certificate.logOnePlusV leaf5566InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5566InputLogOnePlusV_eq }

private noncomputable def leaf5566Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi304InputQChi innerPair285Input
    leaf5566InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5566LowerChecked :
    lowerCheck 24 leaf5566Box leaf5566Inputs = true := by
  rfl'

private theorem leaf5566CoversExact : CoversExact 8
    leaf5566Box leaf5566Certificate leaf5566InnerLog leaf5566Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi304RoundedFacts
    innerPair285RoundedFacts leaf5566RoundedFacts (by rfl)

private theorem leaf5566FlatSound : Sound leaf5566Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5566CertificateValid
    leaf5566InnerLogValid leaf5566CoversExact leaf5566LowerChecked

private noncomputable def leaf5567Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (47/128), chiHi := (95/256) }

private noncomputable def leaf5567Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871357/536870912) }, vSqrt := { lower := (65527/65536), upper := (68716396541/68713250816) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1319158717/1073741824) }, upper := { exponent := 1, mantissa := (159/128) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi303LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (137429647357/137426501632) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf5567InnerLog : WideLogData :=
  innerPair657Data

set_option maxRecDepth 1000000 in
private theorem leaf5567LocalValidity :
    LeafFacts leaf5567Box leaf5567Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5567Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (68716396541/68713250816) }) = true
      norm_num [leaf5567Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5567CertificateValid :
    WideCertificateValid leaf5567Box leaf5567Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi303ValidityFacts
    leaf5567LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5567CoverageChecked :
    coverageCheck (innerAD leaf5567Box) leaf5567InnerLog = true := by
  rfl'

private theorem leaf5567InnerLogValid :
    leaf5567InnerLog.Valid 8 (innerAD leaf5567Box) :=
  wideLogDataValid_of_cachedCheck endpoint403PositiveFacts
    endpoint414PositiveFacts.valid leaf5567CoverageChecked

private noncomputable def leaf5567InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629465/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5567InputLogOnePlusV_eq :
    leaf5567InputLogOnePlusV = outerEnclosure 24
      (leaf5567Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5567RoundedFacts : LeafRoundedFacts 8
    leaf5567Certificate.logOnePlusV leaf5567InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5567InputLogOnePlusV_eq }

private noncomputable def leaf5567Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi303InputQChi innerPair657Input
    leaf5567InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5567LowerChecked :
    lowerCheck 24 leaf5567Box leaf5567Inputs = true := by
  rfl'

private theorem leaf5567CoversExact : CoversExact 8
    leaf5567Box leaf5567Certificate leaf5567InnerLog leaf5567Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi303RoundedFacts
    innerPair657RoundedFacts leaf5567RoundedFacts (by rfl)

private theorem leaf5567FlatSound : Sound leaf5567Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5567CertificateValid
    leaf5567InnerLogValid leaf5567CoversExact leaf5567LowerChecked

private noncomputable def leaf5568Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (95/256), chiHi := (3/8) }

private noncomputable def leaf5568Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871359/536870912) }, vSqrt := { lower := (65527/65536), upper := (68716396541/68713185280) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1327481279/1073741824) }, upper := { exponent := 1, mantissa := (5/4) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi304LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (137429581821/137426370560) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf5568InnerLog : WideLogData :=
  innerPair285Data

set_option maxRecDepth 1000000 in
private theorem leaf5568LocalValidity :
    LeafFacts leaf5568Box leaf5568Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5568Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (68716396541/68713185280) }) = true
      norm_num [leaf5568Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5568CertificateValid :
    WideCertificateValid leaf5568Box leaf5568Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi304ValidityFacts
    leaf5568LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5568CoverageChecked :
    coverageCheck (innerAD leaf5568Box) leaf5568InnerLog = true := by
  rfl'

private theorem leaf5568InnerLogValid :
    leaf5568InnerLog.Valid 8 (innerAD leaf5568Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint79PositiveFacts.valid leaf5568CoverageChecked

private noncomputable def leaf5568InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629473/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5568InputLogOnePlusV_eq :
    leaf5568InputLogOnePlusV = outerEnclosure 24
      (leaf5568Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5568RoundedFacts : LeafRoundedFacts 8
    leaf5568Certificate.logOnePlusV leaf5568InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5568InputLogOnePlusV_eq }

private noncomputable def leaf5568Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi304InputQChi innerPair285Input
    leaf5568InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5568LowerChecked :
    lowerCheck 24 leaf5568Box leaf5568Inputs = true := by
  rfl'

private theorem leaf5568CoversExact : CoversExact 8
    leaf5568Box leaf5568Certificate leaf5568InnerLog leaf5568Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi304RoundedFacts
    innerPair285RoundedFacts leaf5568RoundedFacts (by rfl)

private theorem leaf5568FlatSound : Sound leaf5568Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5568CertificateValid
    leaf5568InnerLogValid leaf5568CoversExact leaf5568LowerChecked

private noncomputable def component112Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (11/32), chiHi := (45/128) }

set_option maxRecDepth 1000000 in
private theorem component112Node0_sound : Sound component112Node0Box :=
  sound_of_literal_split component112Node0Box leaf5531Box leaf5532Box
    .chi (89/256) (by rfl) (by rfl)
    leaf5531FlatSound leaf5532FlatSound

private noncomputable def component112Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (11/32), chiHi := (89/256) }

set_option maxRecDepth 1000000 in
private theorem component112Node1_sound : Sound component112Node1Box :=
  sound_of_literal_split component112Node1Box leaf5533Box leaf5534Box
    .k (251/64) (by rfl) (by rfl)
    leaf5533FlatSound leaf5534FlatSound

private noncomputable def component112Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (11/32), chiHi := (45/128) }

set_option maxRecDepth 1000000 in
private theorem component112Node2_sound : Sound component112Node2Box :=
  sound_of_literal_split component112Node2Box component112Node1Box leaf5535Box
    .chi (89/256) (by rfl) (by rfl)
    component112Node1_sound leaf5535FlatSound

private noncomputable def component112Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (11/32), chiHi := (45/128) }

set_option maxRecDepth 1000000 in
private theorem component112Node3_sound : Sound component112Node3Box :=
  sound_of_literal_split component112Node3Box component112Node0Box component112Node2Box
    .k (125/32) (by rfl) (by rfl)
    component112Node0_sound component112Node2_sound

private noncomputable def component112Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (45/128), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component112Node4_sound : Sound component112Node4Box :=
  sound_of_literal_split component112Node4Box leaf5536Box leaf5537Box
    .chi (91/256) (by rfl) (by rfl)
    leaf5536FlatSound leaf5537FlatSound

private noncomputable def component112Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (45/128), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component112Node5_sound : Sound component112Node5Box :=
  sound_of_literal_split component112Node5Box leaf5538Box leaf5539Box
    .chi (91/256) (by rfl) (by rfl)
    leaf5538FlatSound leaf5539FlatSound

private noncomputable def component112Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (45/128), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component112Node6_sound : Sound component112Node6Box :=
  sound_of_literal_split component112Node6Box component112Node4Box component112Node5Box
    .k (125/32) (by rfl) (by rfl)
    component112Node4_sound component112Node5_sound

private noncomputable def component112Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (11/32), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component112Node7_sound : Sound component112Node7Box :=
  sound_of_literal_split component112Node7Box component112Node3Box component112Node6Box
    .chi (45/128) (by rfl) (by rfl)
    component112Node3_sound component112Node6_sound

private noncomputable def component112Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (11/32), chiHi := (89/256) }

set_option maxRecDepth 1000000 in
private theorem component112Node8_sound : Sound component112Node8Box :=
  sound_of_literal_split component112Node8Box leaf5540Box leaf5541Box
    .k (253/64) (by rfl) (by rfl)
    leaf5540FlatSound leaf5541FlatSound

private noncomputable def component112Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (89/256), chiHi := (45/128) }

set_option maxRecDepth 1000000 in
private theorem component112Node9_sound : Sound component112Node9Box :=
  sound_of_literal_split component112Node9Box leaf5542Box leaf5543Box
    .k (253/64) (by rfl) (by rfl)
    leaf5542FlatSound leaf5543FlatSound

private noncomputable def component112Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (11/32), chiHi := (45/128) }

set_option maxRecDepth 1000000 in
private theorem component112Node10_sound : Sound component112Node10Box :=
  sound_of_literal_split component112Node10Box component112Node8Box component112Node9Box
    .chi (89/256) (by rfl) (by rfl)
    component112Node8_sound component112Node9_sound

private noncomputable def component112Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (11/32), chiHi := (89/256) }

set_option maxRecDepth 1000000 in
private theorem component112Node11_sound : Sound component112Node11Box :=
  sound_of_literal_split component112Node11Box leaf5544Box leaf5545Box
    .k (255/64) (by rfl) (by rfl)
    leaf5544FlatSound leaf5545FlatSound

private noncomputable def component112Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (89/256), chiHi := (45/128) }

set_option maxRecDepth 1000000 in
private theorem component112Node12_sound : Sound component112Node12Box :=
  sound_of_literal_split component112Node12Box leaf5546Box leaf5547Box
    .k (255/64) (by rfl) (by rfl)
    leaf5546FlatSound leaf5547FlatSound

private noncomputable def component112Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (11/32), chiHi := (45/128) }

set_option maxRecDepth 1000000 in
private theorem component112Node13_sound : Sound component112Node13Box :=
  sound_of_literal_split component112Node13Box component112Node11Box component112Node12Box
    .chi (89/256) (by rfl) (by rfl)
    component112Node11_sound component112Node12_sound

private noncomputable def component112Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (11/32), chiHi := (45/128) }

set_option maxRecDepth 1000000 in
private theorem component112Node14_sound : Sound component112Node14Box :=
  sound_of_literal_split component112Node14Box component112Node10Box component112Node13Box
    .k (127/32) (by rfl) (by rfl)
    component112Node10_sound component112Node13_sound

private noncomputable def component112Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (45/128), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component112Node15_sound : Sound component112Node15Box :=
  sound_of_literal_split component112Node15Box leaf5548Box leaf5549Box
    .chi (91/256) (by rfl) (by rfl)
    leaf5548FlatSound leaf5549FlatSound

private noncomputable def component112Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (45/128), chiHi := (91/256) }

set_option maxRecDepth 1000000 in
private theorem component112Node16_sound : Sound component112Node16Box :=
  sound_of_literal_split component112Node16Box leaf5550Box leaf5551Box
    .k (255/64) (by rfl) (by rfl)
    leaf5550FlatSound leaf5551FlatSound

private noncomputable def component112Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (45/128), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component112Node17_sound : Sound component112Node17Box :=
  sound_of_literal_split component112Node17Box component112Node16Box leaf5552Box
    .chi (91/256) (by rfl) (by rfl)
    component112Node16_sound leaf5552FlatSound

private noncomputable def component112Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (45/128), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component112Node18_sound : Sound component112Node18Box :=
  sound_of_literal_split component112Node18Box component112Node15Box component112Node17Box
    .k (127/32) (by rfl) (by rfl)
    component112Node15_sound component112Node17_sound

private noncomputable def component112Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (11/32), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component112Node19_sound : Sound component112Node19Box :=
  sound_of_literal_split component112Node19Box component112Node14Box component112Node18Box
    .chi (45/128) (by rfl) (by rfl)
    component112Node14_sound component112Node18_sound

private noncomputable def component112Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (11/32), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component112Node20_sound : Sound component112Node20Box :=
  sound_of_literal_split component112Node20Box component112Node7Box component112Node19Box
    .k (63/16) (by rfl) (by rfl)
    component112Node7_sound component112Node19_sound

private noncomputable def component112Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (23/64), chiHi := (47/128) }

set_option maxRecDepth 1000000 in
private theorem component112Node21_sound : Sound component112Node21Box :=
  sound_of_literal_split component112Node21Box leaf5553Box leaf5554Box
    .chi (93/256) (by rfl) (by rfl)
    leaf5553FlatSound leaf5554FlatSound

private noncomputable def component112Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (23/64), chiHi := (47/128) }

set_option maxRecDepth 1000000 in
private theorem component112Node22_sound : Sound component112Node22Box :=
  sound_of_literal_split component112Node22Box leaf5555Box leaf5556Box
    .chi (93/256) (by rfl) (by rfl)
    leaf5555FlatSound leaf5556FlatSound

private noncomputable def component112Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (23/64), chiHi := (47/128) }

set_option maxRecDepth 1000000 in
private theorem component112Node23_sound : Sound component112Node23Box :=
  sound_of_literal_split component112Node23Box component112Node21Box component112Node22Box
    .k (125/32) (by rfl) (by rfl)
    component112Node21_sound component112Node22_sound

private noncomputable def component112Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (47/128), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component112Node24_sound : Sound component112Node24Box :=
  sound_of_literal_split component112Node24Box leaf5557Box leaf5558Box
    .chi (95/256) (by rfl) (by rfl)
    leaf5557FlatSound leaf5558FlatSound

private noncomputable def component112Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (47/128), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component112Node25_sound : Sound component112Node25Box :=
  sound_of_literal_split component112Node25Box leaf5559Box leaf5560Box
    .chi (95/256) (by rfl) (by rfl)
    leaf5559FlatSound leaf5560FlatSound

private noncomputable def component112Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (47/128), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component112Node26_sound : Sound component112Node26Box :=
  sound_of_literal_split component112Node26Box component112Node24Box component112Node25Box
    .k (125/32) (by rfl) (by rfl)
    component112Node24_sound component112Node25_sound

private noncomputable def component112Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (23/64), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component112Node27_sound : Sound component112Node27Box :=
  sound_of_literal_split component112Node27Box component112Node23Box component112Node26Box
    .chi (47/128) (by rfl) (by rfl)
    component112Node23_sound component112Node26_sound

private noncomputable def component112Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (23/64), chiHi := (47/128) }

set_option maxRecDepth 1000000 in
private theorem component112Node28_sound : Sound component112Node28Box :=
  sound_of_literal_split component112Node28Box leaf5561Box leaf5562Box
    .chi (93/256) (by rfl) (by rfl)
    leaf5561FlatSound leaf5562FlatSound

private noncomputable def component112Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (23/64), chiHi := (47/128) }

set_option maxRecDepth 1000000 in
private theorem component112Node29_sound : Sound component112Node29Box :=
  sound_of_literal_split component112Node29Box leaf5563Box leaf5564Box
    .chi (93/256) (by rfl) (by rfl)
    leaf5563FlatSound leaf5564FlatSound

private noncomputable def component112Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (23/64), chiHi := (47/128) }

set_option maxRecDepth 1000000 in
private theorem component112Node30_sound : Sound component112Node30Box :=
  sound_of_literal_split component112Node30Box component112Node28Box component112Node29Box
    .k (127/32) (by rfl) (by rfl)
    component112Node28_sound component112Node29_sound

private noncomputable def component112Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (47/128), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component112Node31_sound : Sound component112Node31Box :=
  sound_of_literal_split component112Node31Box leaf5565Box leaf5566Box
    .chi (95/256) (by rfl) (by rfl)
    leaf5565FlatSound leaf5566FlatSound

private noncomputable def component112Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (47/128), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component112Node32_sound : Sound component112Node32Box :=
  sound_of_literal_split component112Node32Box leaf5567Box leaf5568Box
    .chi (95/256) (by rfl) (by rfl)
    leaf5567FlatSound leaf5568FlatSound

private noncomputable def component112Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (47/128), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component112Node33_sound : Sound component112Node33Box :=
  sound_of_literal_split component112Node33Box component112Node31Box component112Node32Box
    .k (127/32) (by rfl) (by rfl)
    component112Node31_sound component112Node32_sound

private noncomputable def component112Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (23/64), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component112Node34_sound : Sound component112Node34Box :=
  sound_of_literal_split component112Node34Box component112Node30Box component112Node33Box
    .chi (47/128) (by rfl) (by rfl)
    component112Node30_sound component112Node33_sound

private noncomputable def component112Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (23/64), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component112Node35_sound : Sound component112Node35Box :=
  sound_of_literal_split component112Node35Box component112Node27Box component112Node34Box
    .k (63/16) (by rfl) (by rfl)
    component112Node27_sound component112Node34_sound

noncomputable def component112Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (11/32), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
theorem component112_sound : Sound component112Box :=
  sound_of_literal_split component112Box component112Node20Box component112Node35Box
    .chi (23/64) (by rfl) (by rfl)
    component112Node20_sound component112Node35_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
