import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch0
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

private noncomputable def leaf575Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (25/16), chiLo := (1/2), chiHi := (17/32) }

private noncomputable def leaf575Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554515/33554432) }, vSqrt := { lower := (16383/16384), upper := (11453093205/11452665856) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (58685871/33554432) }, upper := { exponent := 0, mantissa := (937/512) } }, logOuter := sk35LogOuterCertificate, logK := sk35LogKCertificate, logChi := chi70LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (22905759061/22905331712) } }, logDArg := sk35LogDArgCertificate }

private noncomputable def leaf575InnerLog : WideLogData :=
  innerPair67Data

set_option maxRecDepth 1000000 in
private theorem leaf575LocalValidity :
    LeafFacts leaf575Box leaf575Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf575Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (11453093205/11452665856) }) = true
      norm_num [leaf575Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf575CertificateValid :
    WideCertificateValid leaf575Box leaf575Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk35ValidityFacts chi70ValidityFacts
    leaf575LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf575CoverageChecked :
    coverageCheck (innerAD leaf575Box) leaf575InnerLog = true := by
  rfl'

private theorem leaf575InnerLogValid :
    leaf575InnerLog.Valid 8 (innerAD leaf575Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint22PositiveFacts.valid leaf575CoverageChecked

private noncomputable def leaf575InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814697/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf575InputLogOnePlusV_eq :
    leaf575InputLogOnePlusV = outerEnclosure 24
      (leaf575Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf575RoundedFacts : LeafRoundedFacts 8
    leaf575Certificate.logOnePlusV leaf575InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf575InputLogOnePlusV_eq }

private noncomputable def leaf575Inputs : Inputs :=
  inputsOfCaches globalInput sk35RoundedInputs
    chi70InputQChi innerPair67Input
    leaf575InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf575LowerChecked :
    lowerCheck 24 leaf575Box leaf575Inputs = true := by
  rfl'

private theorem leaf575CoversExact : CoversExact 8
    leaf575Box leaf575Certificate leaf575InnerLog leaf575Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk35RoundedFacts chi70RoundedFacts
    innerPair67RoundedFacts leaf575RoundedFacts (by rfl)

private theorem leaf575FlatSound : Sound leaf575Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf575CertificateValid
    leaf575InnerLogValid leaf575CoversExact leaf575LowerChecked

private noncomputable def leaf576Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (25/16), chiLo := (17/32), chiHi := (9/16) }

private noncomputable def leaf576Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554517/33554432) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34357895168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (60258637/33554432) }, upper := { exponent := 0, mantissa := (481/256) } }, logOuter := sk35LogOuterCertificate, logK := sk35LogKCertificate, logChi := chi71LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717174783/68715790336) } }, logDArg := sk35LogDArgCertificate }

private noncomputable def leaf576InnerLog : WideLogData :=
  innerPair73Data

set_option maxRecDepth 1000000 in
private theorem leaf576LocalValidity :
    LeafFacts leaf576Box leaf576Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf576Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34357895168) }) = true
      norm_num [leaf576Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf576CertificateValid :
    WideCertificateValid leaf576Box leaf576Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk35ValidityFacts chi71ValidityFacts
    leaf576LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf576CoverageChecked :
    coverageCheck (innerAD leaf576Box) leaf576InnerLog = true := by
  rfl'

private theorem leaf576InnerLogValid :
    leaf576InnerLog.Valid 8 (innerAD leaf576Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint23PositiveFacts.valid leaf576CoverageChecked

private noncomputable def leaf576InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629419/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf576InputLogOnePlusV_eq :
    leaf576InputLogOnePlusV = outerEnclosure 24
      (leaf576Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf576RoundedFacts : LeafRoundedFacts 8
    leaf576Certificate.logOnePlusV leaf576InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf576InputLogOnePlusV_eq }

private noncomputable def leaf576Inputs : Inputs :=
  inputsOfCaches globalInput sk35RoundedInputs
    chi71InputQChi innerPair73Input
    leaf576InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf576LowerChecked :
    lowerCheck 24 leaf576Box leaf576Inputs = true := by
  rfl'

private theorem leaf576CoversExact : CoversExact 8
    leaf576Box leaf576Certificate leaf576InnerLog leaf576Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk35RoundedFacts chi71RoundedFacts
    innerPair73RoundedFacts leaf576RoundedFacts (by rfl)

private theorem leaf576FlatSound : Sound leaf576Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf576CertificateValid
    leaf576InnerLogValid leaf576CoversExact leaf576LowerChecked

private noncomputable def leaf577Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/16), kHi := (13/8), chiLo := (1/2), chiHi := (17/32) }

private noncomputable def leaf577Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554517/33554432) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34357927936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (59734381/33554432) }, upper := { exponent := 0, mantissa := (477/256) } }, logOuter := sk36LogOuterCertificate, logK := sk36LogKCertificate, logChi := chi70LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717207551/68715855872) } }, logDArg := sk36LogDArgCertificate }

private noncomputable def leaf577InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf577LocalValidity :
    LeafFacts leaf577Box leaf577Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf577Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34357927936) }) = true
      norm_num [leaf577Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf577CertificateValid :
    WideCertificateValid leaf577Box leaf577Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk36ValidityFacts chi70ValidityFacts
    leaf577LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf577CoverageChecked :
    coverageCheck (innerAD leaf577Box) leaf577InnerLog = true := by
  rfl'

private theorem leaf577InnerLogValid :
    leaf577InnerLog.Valid 8 (innerAD leaf577Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf577CoverageChecked

private noncomputable def leaf577InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629411/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf577InputLogOnePlusV_eq :
    leaf577InputLogOnePlusV = outerEnclosure 24
      (leaf577Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf577RoundedFacts : LeafRoundedFacts 8
    leaf577Certificate.logOnePlusV leaf577InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf577InputLogOnePlusV_eq }

private noncomputable def leaf577Inputs : Inputs :=
  inputsOfCaches globalInput sk36RoundedInputs
    chi70InputQChi innerPair72Input
    leaf577InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf577LowerChecked :
    lowerCheck 24 leaf577Box leaf577Inputs = true := by
  rfl'

private theorem leaf577CoversExact : CoversExact 8
    leaf577Box leaf577Certificate leaf577InnerLog leaf577Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk36RoundedFacts chi70RoundedFacts
    innerPair72RoundedFacts leaf577RoundedFacts (by rfl)

private theorem leaf577FlatSound : Sound leaf577Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf577CertificateValid
    leaf577InnerLogValid leaf577CoversExact leaf577LowerChecked

private noncomputable def leaf578Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/16), kHi := (13/8), chiLo := (17/32), chiHi := (9/16) }

private noncomputable def leaf578Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554519/33554432) }, vSqrt := { lower := (16383/16384), upper := (404226819/404209664) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (61372679/33554432) }, upper := { exponent := 0, mantissa := (245/128) } }, logOuter := sk36LogOuterCertificate, logK := sk36LogKCertificate, logChi := chi71LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (808436483/808419328) } }, logDArg := sk36LogDArgCertificate }

private noncomputable def leaf578InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf578LocalValidity :
    LeafFacts leaf578Box leaf578Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf578Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (404226819/404209664) }) = true
      norm_num [leaf578Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf578CertificateValid :
    WideCertificateValid leaf578Box leaf578Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk36ValidityFacts chi71ValidityFacts
    leaf578LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf578CoverageChecked :
    coverageCheck (innerAD leaf578Box) leaf578InnerLog = true := by
  rfl'

private theorem leaf578InnerLogValid :
    leaf578InnerLog.Valid 8 (innerAD leaf578Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf578CoverageChecked

private noncomputable def leaf578InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629437/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf578InputLogOnePlusV_eq :
    leaf578InputLogOnePlusV = outerEnclosure 24
      (leaf578Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf578RoundedFacts : LeafRoundedFacts 8
    leaf578Certificate.logOnePlusV leaf578InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf578InputLogOnePlusV_eq }

private noncomputable def leaf578Inputs : Inputs :=
  inputsOfCaches globalInput sk36RoundedInputs
    chi71InputQChi innerPair92Input
    leaf578InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf578LowerChecked :
    lowerCheck 24 leaf578Box leaf578Inputs = true := by
  rfl'

private theorem leaf578CoversExact : CoversExact 8
    leaf578Box leaf578Certificate leaf578InnerLog leaf578Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk36RoundedFacts chi71RoundedFacts
    innerPair92RoundedFacts leaf578RoundedFacts (by rfl)

private theorem leaf578FlatSound : Sound leaf578Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf578CertificateValid
    leaf578InnerLogValid leaf578CoversExact leaf578LowerChecked

private noncomputable def leaf579Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (25/16), chiLo := (9/16), chiHi := (19/32) }

private noncomputable def leaf579Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554519/33554432) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34357792768) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (61831403/33554432) }, upper := { exponent := 0, mantissa := (987/512) } }, logOuter := sk35LogOuterCertificate, logK := sk35LogKCertificate, logChi := chi72LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717072383/68715585536) } }, logDArg := sk35LogDArgCertificate }

private noncomputable def leaf579InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf579LocalValidity :
    LeafFacts leaf579Box leaf579Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf579Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34357792768) }) = true
      norm_num [leaf579Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf579CertificateValid :
    WideCertificateValid leaf579Box leaf579Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk35ValidityFacts chi72ValidityFacts
    leaf579LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf579CoverageChecked :
    coverageCheck (innerAD leaf579Box) leaf579InnerLog = true := by
  rfl'

private theorem leaf579InnerLogValid :
    leaf579InnerLog.Valid 8 (innerAD leaf579Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf579CoverageChecked

private noncomputable def leaf579InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (2907361/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf579InputLogOnePlusV_eq :
    leaf579InputLogOnePlusV = outerEnclosure 24
      (leaf579Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf579RoundedFacts : LeafRoundedFacts 8
    leaf579Certificate.logOnePlusV leaf579InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf579InputLogOnePlusV_eq }

private noncomputable def leaf579Inputs : Inputs :=
  inputsOfCaches globalInput sk35RoundedInputs
    chi72InputQChi innerPair92Input
    leaf579InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf579LowerChecked :
    lowerCheck 24 leaf579Box leaf579Inputs = true := by
  rfl'

private theorem leaf579CoversExact : CoversExact 8
    leaf579Box leaf579Certificate leaf579InnerLog leaf579Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk35RoundedFacts chi72RoundedFacts
    innerPair92RoundedFacts leaf579RoundedFacts (by rfl)

private theorem leaf579FlatSound : Sound leaf579Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf579CertificateValid
    leaf579InnerLogValid leaf579CoversExact leaf579LowerChecked

private noncomputable def leaf580Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (25/16), chiLo := (19/32), chiHi := (5/8) }

private noncomputable def leaf580Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554521/33554432) }, vSqrt := { lower := (16383/16384), upper := (5726459221/5726281728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (63404169/33554432) }, upper := { exponent := 0, mantissa := (253/128) } }, logOuter := sk35LogOuterCertificate, logK := sk35LogKCertificate, logChi := chi73LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (11452740949/11452563456) } }, logDArg := sk35LogDArgCertificate }

private noncomputable def leaf580InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf580LocalValidity :
    LeafFacts leaf580Box leaf580Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf580Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (5726459221/5726281728) }) = true
      norm_num [leaf580Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf580CertificateValid :
    WideCertificateValid leaf580Box leaf580Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk35ValidityFacts chi73ValidityFacts
    leaf580LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf580CoverageChecked :
    coverageCheck (innerAD leaf580Box) leaf580InnerLog = true := by
  rfl'

private theorem leaf580InnerLogValid :
    leaf580InnerLog.Valid 8 (innerAD leaf580Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf580CoverageChecked

private noncomputable def leaf580InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629341/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf580InputLogOnePlusV_eq :
    leaf580InputLogOnePlusV = outerEnclosure 24
      (leaf580Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf580RoundedFacts : LeafRoundedFacts 8
    leaf580Certificate.logOnePlusV leaf580InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf580InputLogOnePlusV_eq }

private noncomputable def leaf580Inputs : Inputs :=
  inputsOfCaches globalInput sk35RoundedInputs
    chi73InputQChi innerPair101Input
    leaf580InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf580LowerChecked :
    lowerCheck 24 leaf580Box leaf580Inputs = true := by
  rfl'

private theorem leaf580CoversExact : CoversExact 8
    leaf580Box leaf580Certificate leaf580InnerLog leaf580Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk35RoundedFacts chi73RoundedFacts
    innerPair101RoundedFacts leaf580RoundedFacts (by rfl)

private theorem leaf580FlatSound : Sound leaf580Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf580CertificateValid
    leaf580InnerLogValid leaf580CoversExact leaf580LowerChecked

private noncomputable def leaf581Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/16), kHi := (13/8), chiLo := (9/16), chiHi := (19/32) }

private noncomputable def leaf581Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554521/33554432) }, vSqrt := { lower := (16383/16384), upper := (11453093205/11452571648) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (63010977/33554432) }, upper := { exponent := 0, mantissa := (503/256) } }, logOuter := sk36LogOuterCertificate, logK := sk36LogKCertificate, logChi := chi72LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (22905664853/22905143296) } }, logDArg := sk36LogDArgCertificate }

private noncomputable def leaf581InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf581LocalValidity :
    LeafFacts leaf581Box leaf581Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf581Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (11453093205/11452571648) }) = true
      norm_num [leaf581Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf581CertificateValid :
    WideCertificateValid leaf581Box leaf581Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk36ValidityFacts chi72ValidityFacts
    leaf581LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf581CoverageChecked :
    coverageCheck (innerAD leaf581Box) leaf581InnerLog = true := by
  rfl'

private theorem leaf581InnerLogValid :
    leaf581InnerLog.Valid 8 (innerAD leaf581Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf581CoverageChecked

private noncomputable def leaf581InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629463/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf581InputLogOnePlusV_eq :
    leaf581InputLogOnePlusV = outerEnclosure 24
      (leaf581Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf581RoundedFacts : LeafRoundedFacts 8
    leaf581Certificate.logOnePlusV leaf581InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf581InputLogOnePlusV_eq }

private noncomputable def leaf581Inputs : Inputs :=
  inputsOfCaches globalInput sk36RoundedInputs
    chi72InputQChi innerPair101Input
    leaf581InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf581LowerChecked :
    lowerCheck 24 leaf581Box leaf581Inputs = true := by
  rfl'

private theorem leaf581CoversExact : CoversExact 8
    leaf581Box leaf581Certificate leaf581InnerLog leaf581Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk36RoundedFacts chi72RoundedFacts
    innerPair101RoundedFacts leaf581RoundedFacts (by rfl)

private theorem leaf581FlatSound : Sound leaf581Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf581CertificateValid
    leaf581InnerLogValid leaf581CoversExact leaf581LowerChecked

private noncomputable def leaf582Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/16), kHi := (13/8), chiLo := (19/32), chiHi := (5/8) }

private noncomputable def leaf582Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (33554523/33554432) }, vSqrt := { lower := (16383/16384), upper := (17179377663/17178804224) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (64649275/33554432) }, upper := { exponent := 1, mantissa := (129/128) } }, logOuter := sk36LogOuterCertificate, logK := sk36LogKCertificate, logChi := chi73LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (34358181887/34357608448) } }, logDArg := sk36LogDArgCertificate }

private noncomputable def leaf582InnerLog : WideLogData :=
  innerPair104Data

set_option maxRecDepth 1000000 in
private theorem leaf582LocalValidity :
    LeafFacts leaf582Box leaf582Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf582Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (17179377663/17178804224) }) = true
      norm_num [leaf582Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf582CertificateValid :
    WideCertificateValid leaf582Box leaf582Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk36ValidityFacts chi73ValidityFacts
    leaf582LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf582CoverageChecked :
    coverageCheck (innerAD leaf582Box) leaf582InnerLog = true := by
  rfl'

private theorem leaf582InnerLogValid :
    leaf582InnerLog.Valid 8 (innerAD leaf582Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint72PositiveFacts.valid leaf582CoverageChecked

private noncomputable def leaf582InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629361/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf582InputLogOnePlusV_eq :
    leaf582InputLogOnePlusV = outerEnclosure 24
      (leaf582Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf582RoundedFacts : LeafRoundedFacts 8
    leaf582Certificate.logOnePlusV leaf582InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf582InputLogOnePlusV_eq }

private noncomputable def leaf582Inputs : Inputs :=
  inputsOfCaches globalInput sk36RoundedInputs
    chi73InputQChi innerPair104Input
    leaf582InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf582LowerChecked :
    lowerCheck 24 leaf582Box leaf582Inputs = true := by
  rfl'

private theorem leaf582CoversExact : CoversExact 8
    leaf582Box leaf582Certificate leaf582InnerLog leaf582Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk36RoundedFacts chi73RoundedFacts
    innerPair104RoundedFacts leaf582RoundedFacts (by rfl)

private theorem leaf582FlatSound : Sound leaf582Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf582CertificateValid
    leaf582InnerLogValid leaf582CoversExact leaf582LowerChecked

private noncomputable def leaf583Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (27/16), chiLo := (1/2), chiHi := (17/32) }

private noncomputable def leaf583Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554519/33554432) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34357858304) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (60782891/33554432) }, upper := { exponent := 0, mantissa := (971/512) } }, logOuter := sk33LogOuterCertificate, logK := sk33LogKCertificate, logChi := chi70LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717137919/68715716608) } }, logDArg := sk33LogDArgCertificate }

private noncomputable def leaf583InnerLog : WideLogData :=
  innerPair222Data

set_option maxRecDepth 1000000 in
private theorem leaf583LocalValidity :
    LeafFacts leaf583Box leaf583Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf583Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34357858304) }) = true
      norm_num [leaf583Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf583CertificateValid :
    WideCertificateValid leaf583Box leaf583Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk33ValidityFacts chi70ValidityFacts
    leaf583LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf583CoverageChecked :
    coverageCheck (innerAD leaf583Box) leaf583InnerLog = true := by
  rfl'

private theorem leaf583InnerLogValid :
    leaf583InnerLog.Valid 8 (innerAD leaf583Box) :=
  wideLogDataValid_of_cachedCheck endpoint67PositiveFacts
    endpoint70PositiveFacts.valid leaf583CoverageChecked

private noncomputable def leaf583InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (2907357/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf583InputLogOnePlusV_eq :
    leaf583InputLogOnePlusV = outerEnclosure 24
      (leaf583Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf583RoundedFacts : LeafRoundedFacts 8
    leaf583Certificate.logOnePlusV leaf583InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf583InputLogOnePlusV_eq }

private noncomputable def leaf583Inputs : Inputs :=
  inputsOfCaches globalInput sk33RoundedInputs
    chi70InputQChi innerPair222Input
    leaf583InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf583LowerChecked :
    lowerCheck 24 leaf583Box leaf583Inputs = true := by
  rfl'

private theorem leaf583CoversExact : CoversExact 8
    leaf583Box leaf583Certificate leaf583InnerLog leaf583Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk33RoundedFacts chi70RoundedFacts
    innerPair222RoundedFacts leaf583RoundedFacts (by rfl)

private theorem leaf583FlatSound : Sound leaf583Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf583CertificateValid
    leaf583InnerLogValid leaf583CoversExact leaf583LowerChecked

private noncomputable def leaf584Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (1/2), chiHi := (17/32) }

private noncomputable def leaf584Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554521/33554432) }, vSqrt := { lower := (16383/16384), upper := (11453093205/11452596224) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (61831401/33554432) }, upper := { exponent := 0, mantissa := (247/128) } }, logOuter := sk34LogOuterCertificate, logK := sk34LogKCertificate, logChi := chi70LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (22905689429/22905192448) } }, logDArg := sk34LogDArgCertificate }

private noncomputable def leaf584InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf584LocalValidity :
    LeafFacts leaf584Box leaf584Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf584Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (11453093205/11452596224) }) = true
      norm_num [leaf584Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf584CertificateValid :
    WideCertificateValid leaf584Box leaf584Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk34ValidityFacts chi70ValidityFacts
    leaf584LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf584CoverageChecked :
    coverageCheck (innerAD leaf584Box) leaf584InnerLog = true := by
  rfl'

private theorem leaf584InnerLogValid :
    leaf584InnerLog.Valid 8 (innerAD leaf584Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf584CoverageChecked

private noncomputable def leaf584InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629445/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf584InputLogOnePlusV_eq :
    leaf584InputLogOnePlusV = outerEnclosure 24
      (leaf584Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf584RoundedFacts : LeafRoundedFacts 8
    leaf584Certificate.logOnePlusV leaf584InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf584InputLogOnePlusV_eq }

private noncomputable def leaf584Inputs : Inputs :=
  inputsOfCaches globalInput sk34RoundedInputs
    chi70InputQChi innerPair92Input
    leaf584InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf584LowerChecked :
    lowerCheck 24 leaf584Box leaf584Inputs = true := by
  rfl'

private theorem leaf584CoversExact : CoversExact 8
    leaf584Box leaf584Certificate leaf584InnerLog leaf584Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk34RoundedFacts chi70RoundedFacts
    innerPair92RoundedFacts leaf584RoundedFacts (by rfl)

private theorem leaf584FlatSound : Sound leaf584Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf584CertificateValid
    leaf584InnerLogValid leaf584CoversExact leaf584LowerChecked

private noncomputable def leaf585Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (27/16), chiLo := (17/32), chiHi := (9/16) }

private noncomputable def leaf585Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554521/33554432) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34357747712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (62486721/33554432) }, upper := { exponent := 0, mantissa := (499/256) } }, logOuter := sk33LogOuterCertificate, logK := sk33LogKCertificate, logChi := chi71LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717027327/68715495424) } }, logDArg := sk33LogDArgCertificate }

private noncomputable def leaf585InnerLog : WideLogData :=
  innerPair93Data

set_option maxRecDepth 1000000 in
private theorem leaf585LocalValidity :
    LeafFacts leaf585Box leaf585Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf585Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34357747712) }) = true
      norm_num [leaf585Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf585CertificateValid :
    WideCertificateValid leaf585Box leaf585Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk33ValidityFacts chi71ValidityFacts
    leaf585LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf585CoverageChecked :
    coverageCheck (innerAD leaf585Box) leaf585InnerLog = true := by
  rfl'

private theorem leaf585InnerLogValid :
    leaf585InnerLog.Valid 8 (innerAD leaf585Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint24PositiveFacts.valid leaf585CoverageChecked

private noncomputable def leaf585InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629455/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf585InputLogOnePlusV_eq :
    leaf585InputLogOnePlusV = outerEnclosure 24
      (leaf585Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf585RoundedFacts : LeafRoundedFacts 8
    leaf585Certificate.logOnePlusV leaf585InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf585InputLogOnePlusV_eq }

private noncomputable def leaf585Inputs : Inputs :=
  inputsOfCaches globalInput sk33RoundedInputs
    chi71InputQChi innerPair93Input
    leaf585InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf585LowerChecked :
    lowerCheck 24 leaf585Box leaf585Inputs = true := by
  rfl'

private theorem leaf585CoversExact : CoversExact 8
    leaf585Box leaf585Certificate leaf585InnerLog leaf585Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk33RoundedFacts chi71RoundedFacts
    innerPair93RoundedFacts leaf585RoundedFacts (by rfl)

private theorem leaf585FlatSound : Sound leaf585Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf585CertificateValid
    leaf585InnerLogValid leaf585CoversExact leaf585LowerChecked

private noncomputable def leaf586Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (17/32), chiHi := (9/16) }

private noncomputable def leaf586Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554523/33554432) }, vSqrt := { lower := (16383/16384), upper := (554173473/554156032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (63600763/33554432) }, upper := { exponent := 0, mantissa := (127/64) } }, logOuter := sk34LogOuterCertificate, logK := sk34LogKCertificate, logChi := chi71LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (1108329505/1108312064) } }, logDArg := sk34LogDArgCertificate }

private noncomputable def leaf586InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf586LocalValidity :
    LeafFacts leaf586Box leaf586Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf586Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (554173473/554156032) }) = true
      norm_num [leaf586Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf586CertificateValid :
    WideCertificateValid leaf586Box leaf586Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk34ValidityFacts chi71ValidityFacts
    leaf586LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf586CoverageChecked :
    coverageCheck (innerAD leaf586Box) leaf586InnerLog = true := by
  rfl'

private theorem leaf586InnerLogValid :
    leaf586InnerLog.Valid 8 (innerAD leaf586Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf586CoverageChecked

private noncomputable def leaf586InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629345/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf586InputLogOnePlusV_eq :
    leaf586InputLogOnePlusV = outerEnclosure 24
      (leaf586Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf586RoundedFacts : LeafRoundedFacts 8
    leaf586Certificate.logOnePlusV leaf586InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf586InputLogOnePlusV_eq }

private noncomputable def leaf586Inputs : Inputs :=
  inputsOfCaches globalInput sk34RoundedInputs
    chi71InputQChi innerPair101Input
    leaf586InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf586LowerChecked :
    lowerCheck 24 leaf586Box leaf586Inputs = true := by
  rfl'

private theorem leaf586CoversExact : CoversExact 8
    leaf586Box leaf586Certificate leaf586InnerLog leaf586Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk34RoundedFacts chi71RoundedFacts
    innerPair101RoundedFacts leaf586RoundedFacts (by rfl)

private theorem leaf586FlatSound : Sound leaf586Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf586CertificateValid
    leaf586InnerLogValid leaf586CoversExact leaf586LowerChecked

private noncomputable def leaf587Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (27/16), chiLo := (9/16), chiHi := (19/32) }

private noncomputable def leaf587Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (33554523/33554432) }, vSqrt := { lower := (16383/16384), upper := (17179377663/17178818560) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (64190551/33554432) }, upper := { exponent := 1, mantissa := (1025/1024) } }, logOuter := sk33LogOuterCertificate, logK := sk33LogKCertificate, logChi := chi72LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (34358196223/34357637120) } }, logDArg := sk33LogDArgCertificate }

private noncomputable def leaf587InnerLog : WideLogData :=
  innerPair104Data

set_option maxRecDepth 1000000 in
private theorem leaf587LocalValidity :
    LeafFacts leaf587Box leaf587Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf587Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (17179377663/17178818560) }) = true
      norm_num [leaf587Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf587CertificateValid :
    WideCertificateValid leaf587Box leaf587Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk33ValidityFacts chi72ValidityFacts
    leaf587LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf587CoverageChecked :
    coverageCheck (innerAD leaf587Box) leaf587InnerLog = true := by
  rfl'

private theorem leaf587InnerLogValid :
    leaf587InnerLog.Valid 8 (innerAD leaf587Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint72PositiveFacts.valid leaf587CoverageChecked

private noncomputable def leaf587InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814677/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf587InputLogOnePlusV_eq :
    leaf587InputLogOnePlusV = outerEnclosure 24
      (leaf587Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf587RoundedFacts : LeafRoundedFacts 8
    leaf587Certificate.logOnePlusV leaf587InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf587InputLogOnePlusV_eq }

private noncomputable def leaf587Inputs : Inputs :=
  inputsOfCaches globalInput sk33RoundedInputs
    chi72InputQChi innerPair104Input
    leaf587InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf587LowerChecked :
    lowerCheck 24 leaf587Box leaf587Inputs = true := by
  rfl'

private theorem leaf587CoversExact : CoversExact 8
    leaf587Box leaf587Certificate leaf587InnerLog leaf587Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk33RoundedFacts chi72RoundedFacts
    innerPair104RoundedFacts leaf587RoundedFacts (by rfl)

private theorem leaf587FlatSound : Sound leaf587Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf587CertificateValid
    leaf587InnerLogValid leaf587CoversExact leaf587LowerChecked

private noncomputable def leaf588Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (27/16), chiLo := (19/32), chiHi := (5/8) }

private noncomputable def leaf588Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (33554525/33554432) }, vSqrt := { lower := (16383/16384), upper := (17179377663/17178763264) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (65894381/33554432) }, upper := { exponent := 1, mantissa := (263/256) } }, logOuter := sk33LogOuterCertificate, logK := sk33LogKCertificate, logChi := chi73LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (34358140927/34357526528) } }, logDArg := sk33LogDArgCertificate }

private noncomputable def leaf588InnerLog : WideLogData :=
  innerPair110Data

set_option maxRecDepth 1000000 in
private theorem leaf588LocalValidity :
    LeafFacts leaf588Box leaf588Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf588Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (17179377663/17178763264) }) = true
      norm_num [leaf588Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf588CertificateValid :
    WideCertificateValid leaf588Box leaf588Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk33ValidityFacts chi73ValidityFacts
    leaf588LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf588CoverageChecked :
    coverageCheck (innerAD leaf588Box) leaf588InnerLog = true := by
  rfl'

private theorem leaf588InnerLogValid :
    leaf588InnerLog.Valid 8 (innerAD leaf588Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint72PositiveFacts.valid leaf588CoverageChecked

private noncomputable def leaf588InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629381/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf588InputLogOnePlusV_eq :
    leaf588InputLogOnePlusV = outerEnclosure 24
      (leaf588Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf588RoundedFacts : LeafRoundedFacts 8
    leaf588Certificate.logOnePlusV leaf588InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf588InputLogOnePlusV_eq }

private noncomputable def leaf588Inputs : Inputs :=
  inputsOfCaches globalInput sk33RoundedInputs
    chi73InputQChi innerPair110Input
    leaf588InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf588LowerChecked :
    lowerCheck 24 leaf588Box leaf588Inputs = true := by
  rfl'

private theorem leaf588CoversExact : CoversExact 8
    leaf588Box leaf588Certificate leaf588InnerLog leaf588Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk33RoundedFacts chi73RoundedFacts
    innerPair110RoundedFacts leaf588RoundedFacts (by rfl)

private theorem leaf588FlatSound : Sound leaf588Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf588CertificateValid
    leaf588InnerLogValid leaf588CoversExact leaf588LowerChecked

private noncomputable def leaf589Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (9/16), chiHi := (19/32) }

private noncomputable def leaf589Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (33554525/33554432) }, vSqrt := { lower := (16383/16384), upper := (17179377663/17178779648) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (65370125/33554432) }, upper := { exponent := 1, mantissa := (261/256) } }, logOuter := sk34LogOuterCertificate, logK := sk34LogKCertificate, logChi := chi72LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (34358157311/34357559296) } }, logDArg := sk34LogDArgCertificate }

private noncomputable def leaf589InnerLog : WideLogData :=
  innerPair110Data

set_option maxRecDepth 1000000 in
private theorem leaf589LocalValidity :
    LeafFacts leaf589Box leaf589Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf589Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (17179377663/17178779648) }) = true
      norm_num [leaf589Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf589CertificateValid :
    WideCertificateValid leaf589Box leaf589Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk34ValidityFacts chi72ValidityFacts
    leaf589LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf589CoverageChecked :
    coverageCheck (innerAD leaf589Box) leaf589InnerLog = true := by
  rfl'

private theorem leaf589InnerLogValid :
    leaf589InnerLog.Valid 8 (innerAD leaf589Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint72PositiveFacts.valid leaf589CoverageChecked

private noncomputable def leaf589InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629373/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf589InputLogOnePlusV_eq :
    leaf589InputLogOnePlusV = outerEnclosure 24
      (leaf589Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf589RoundedFacts : LeafRoundedFacts 8
    leaf589Certificate.logOnePlusV leaf589InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf589InputLogOnePlusV_eq }

private noncomputable def leaf589Inputs : Inputs :=
  inputsOfCaches globalInput sk34RoundedInputs
    chi72InputQChi innerPair110Input
    leaf589InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf589LowerChecked :
    lowerCheck 24 leaf589Box leaf589Inputs = true := by
  rfl'

private theorem leaf589CoversExact : CoversExact 8
    leaf589Box leaf589Certificate leaf589InnerLog leaf589Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk34RoundedFacts chi72RoundedFacts
    innerPair110RoundedFacts leaf589RoundedFacts (by rfl)

private theorem leaf589FlatSound : Sound leaf589Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf589CertificateValid
    leaf589InnerLogValid leaf589CoversExact leaf589LowerChecked

private noncomputable def leaf590Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (19/32), chiHi := (5/8) }

private noncomputable def leaf590Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (33554527/33554432) }, vSqrt := { lower := (16383/16384), upper := (5726459221/5726240768) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (67139487/67108864) }, upper := { exponent := 1, mantissa := (67/64) } }, logOuter := sk34LogOuterCertificate, logK := sk34LogKCertificate, logChi := chi73LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (11452699989/11452481536) } }, logDArg := sk34LogDArgCertificate }

private noncomputable def leaf590InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf590LocalValidity :
    LeafFacts leaf590Box leaf590Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf590Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (5726459221/5726240768) }) = true
      norm_num [leaf590Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf590CertificateValid :
    WideCertificateValid leaf590Box leaf590Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk34ValidityFacts chi73ValidityFacts
    leaf590LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf590CoverageChecked :
    coverageCheck (innerAD leaf590Box) leaf590InnerLog = true := by
  rfl'

private theorem leaf590InnerLogValid :
    leaf590InnerLog.Valid 8 (innerAD leaf590Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf590CoverageChecked

private noncomputable def leaf590InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629401/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf590InputLogOnePlusV_eq :
    leaf590InputLogOnePlusV = outerEnclosure 24
      (leaf590Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf590RoundedFacts : LeafRoundedFacts 8
    leaf590Certificate.logOnePlusV leaf590InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf590InputLogOnePlusV_eq }

private noncomputable def leaf590Inputs : Inputs :=
  inputsOfCaches globalInput sk34RoundedInputs
    chi73InputQChi innerPair117Input
    leaf590InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf590LowerChecked :
    lowerCheck 24 leaf590Box leaf590Inputs = true := by
  rfl'

private theorem leaf590CoversExact : CoversExact 8
    leaf590Box leaf590Certificate leaf590InnerLog leaf590Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk34RoundedFacts chi73RoundedFacts
    innerPair117RoundedFacts leaf590RoundedFacts (by rfl)

private theorem leaf590FlatSound : Sound leaf590Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf590CertificateValid
    leaf590InnerLogValid leaf590CoversExact leaf590LowerChecked

private noncomputable def leaf591Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (25/16), chiLo := (5/8), chiHi := (21/32) }

private noncomputable def leaf591Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (33554523/33554432) }, vSqrt := { lower := (16383/16384), upper := (17179377663/17178793984) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (64976935/33554432) }, upper := { exponent := 1, mantissa := (1037/1024) } }, logOuter := sk35LogOuterCertificate, logK := sk35LogKCertificate, logChi := chi74LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (34358171647/34357587968) } }, logDArg := sk35LogDArgCertificate }

private noncomputable def leaf591InnerLog : WideLogData :=
  innerPair104Data

set_option maxRecDepth 1000000 in
private theorem leaf591LocalValidity :
    LeafFacts leaf591Box leaf591Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf591Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (17179377663/17178793984) }) = true
      norm_num [leaf591Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf591CertificateValid :
    WideCertificateValid leaf591Box leaf591Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk35ValidityFacts chi74ValidityFacts
    leaf591LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf591CoverageChecked :
    coverageCheck (innerAD leaf591Box) leaf591InnerLog = true := by
  rfl'

private theorem leaf591InnerLogValid :
    leaf591InnerLog.Valid 8 (innerAD leaf591Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint72PositiveFacts.valid leaf591CoverageChecked

private noncomputable def leaf591InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814683/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf591InputLogOnePlusV_eq :
    leaf591InputLogOnePlusV = outerEnclosure 24
      (leaf591Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf591RoundedFacts : LeafRoundedFacts 8
    leaf591Certificate.logOnePlusV leaf591InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf591InputLogOnePlusV_eq }

private noncomputable def leaf591Inputs : Inputs :=
  inputsOfCaches globalInput sk35RoundedInputs
    chi74InputQChi innerPair104Input
    leaf591InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf591LowerChecked :
    lowerCheck 24 leaf591Box leaf591Inputs = true := by
  rfl'

private theorem leaf591CoversExact : CoversExact 8
    leaf591Box leaf591Certificate leaf591InnerLog leaf591Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk35RoundedFacts chi74RoundedFacts
    innerPair104RoundedFacts leaf591RoundedFacts (by rfl)

private theorem leaf591FlatSound : Sound leaf591Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf591CertificateValid
    leaf591InnerLogValid leaf591CoversExact leaf591LowerChecked

private noncomputable def leaf592Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (25/16), chiLo := (21/32), chiHi := (11/16) }

private noncomputable def leaf592Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (33554525/33554432) }, vSqrt := { lower := (16383/16384), upper := (2454196809/2454106112) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (66549701/33554432) }, upper := { exponent := 1, mantissa := (531/512) } }, logOuter := sk35LogOuterCertificate, logK := sk35LogKCertificate, logChi := chi75LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (4908302921/4908212224) } }, logDArg := sk35LogDArgCertificate }

private noncomputable def leaf592InnerLog : WideLogData :=
  innerPair111Data

set_option maxRecDepth 1000000 in
private theorem leaf592LocalValidity :
    LeafFacts leaf592Box leaf592Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf592Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (2454196809/2454106112) }) = true
      norm_num [leaf592Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf592CertificateValid :
    WideCertificateValid leaf592Box leaf592Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk35ValidityFacts chi75ValidityFacts
    leaf592LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf592CoverageChecked :
    coverageCheck (innerAD leaf592Box) leaf592InnerLog = true := by
  rfl'

private theorem leaf592InnerLogValid :
    leaf592InnerLog.Valid 8 (innerAD leaf592Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint73PositiveFacts.valid leaf592CoverageChecked

private noncomputable def leaf592InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629391/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf592InputLogOnePlusV_eq :
    leaf592InputLogOnePlusV = outerEnclosure 24
      (leaf592Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf592RoundedFacts : LeafRoundedFacts 8
    leaf592Certificate.logOnePlusV leaf592InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf592InputLogOnePlusV_eq }

private noncomputable def leaf592Inputs : Inputs :=
  inputsOfCaches globalInput sk35RoundedInputs
    chi75InputQChi innerPair111Input
    leaf592InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf592LowerChecked :
    lowerCheck 24 leaf592Box leaf592Inputs = true := by
  rfl'

private theorem leaf592CoversExact : CoversExact 8
    leaf592Box leaf592Certificate leaf592InnerLog leaf592Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk35RoundedFacts chi75RoundedFacts
    innerPair111RoundedFacts leaf592RoundedFacts (by rfl)

private theorem leaf592FlatSound : Sound leaf592Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf592CertificateValid
    leaf592InnerLogValid leaf592CoversExact leaf592LowerChecked

private noncomputable def leaf593Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/16), kHi := (13/8), chiLo := (5/8), chiHi := (21/32) }

private noncomputable def leaf593Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (33554525/33554432) }, vSqrt := { lower := (16383/16384), upper := (17179377663/17178750976) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (66287573/33554432) }, upper := { exponent := 1, mantissa := (529/512) } }, logOuter := sk36LogOuterCertificate, logK := sk36LogKCertificate, logChi := chi74LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (34358128639/34357501952) } }, logDArg := sk36LogDArgCertificate }

private noncomputable def leaf593InnerLog : WideLogData :=
  innerPair111Data

set_option maxRecDepth 1000000 in
private theorem leaf593LocalValidity :
    LeafFacts leaf593Box leaf593Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf593Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (17179377663/17178750976) }) = true
      norm_num [leaf593Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf593CertificateValid :
    WideCertificateValid leaf593Box leaf593Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk36ValidityFacts chi74ValidityFacts
    leaf593LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf593CoverageChecked :
    coverageCheck (innerAD leaf593Box) leaf593InnerLog = true := by
  rfl'

private theorem leaf593InnerLogValid :
    leaf593InnerLog.Valid 8 (innerAD leaf593Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint73PositiveFacts.valid leaf593CoverageChecked

private noncomputable def leaf593InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629387/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf593InputLogOnePlusV_eq :
    leaf593InputLogOnePlusV = outerEnclosure 24
      (leaf593Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf593RoundedFacts : LeafRoundedFacts 8
    leaf593Certificate.logOnePlusV leaf593InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf593InputLogOnePlusV_eq }

private noncomputable def leaf593Inputs : Inputs :=
  inputsOfCaches globalInput sk36RoundedInputs
    chi74InputQChi innerPair111Input
    leaf593InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf593LowerChecked :
    lowerCheck 24 leaf593Box leaf593Inputs = true := by
  rfl'

private theorem leaf593CoversExact : CoversExact 8
    leaf593Box leaf593Certificate leaf593InnerLog leaf593Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk36RoundedFacts chi74RoundedFacts
    innerPair111RoundedFacts leaf593RoundedFacts (by rfl)

private theorem leaf593FlatSound : Sound leaf593Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf593CertificateValid
    leaf593InnerLogValid leaf593CoversExact leaf593LowerChecked

private noncomputable def leaf594Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/16), kHi := (13/8), chiLo := (21/32), chiHi := (11/16) }

private noncomputable def leaf594Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (33554527/33554432) }, vSqrt := { lower := (16383/16384), upper := (5726459221/5726232576) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (67925871/67108864) }, upper := { exponent := 1, mantissa := (271/256) } }, logOuter := sk36LogOuterCertificate, logK := sk36LogKCertificate, logChi := chi75LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (11452691797/11452465152) } }, logDArg := sk36LogDArgCertificate }

private noncomputable def leaf594InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf594LocalValidity :
    LeafFacts leaf594Box leaf594Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf594Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (5726459221/5726232576) }) = true
      norm_num [leaf594Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf594CertificateValid :
    WideCertificateValid leaf594Box leaf594Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk36ValidityFacts chi75ValidityFacts
    leaf594LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf594CoverageChecked :
    coverageCheck (innerAD leaf594Box) leaf594InnerLog = true := by
  rfl'

private theorem leaf594InnerLogValid :
    leaf594InnerLog.Valid 8 (innerAD leaf594Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf594CoverageChecked

private noncomputable def leaf594InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629413/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf594InputLogOnePlusV_eq :
    leaf594InputLogOnePlusV = outerEnclosure 24
      (leaf594Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf594RoundedFacts : LeafRoundedFacts 8
    leaf594Certificate.logOnePlusV leaf594InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf594InputLogOnePlusV_eq }

private noncomputable def leaf594Inputs : Inputs :=
  inputsOfCaches globalInput sk36RoundedInputs
    chi75InputQChi innerPair117Input
    leaf594InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf594LowerChecked :
    lowerCheck 24 leaf594Box leaf594Inputs = true := by
  rfl'

private theorem leaf594CoversExact : CoversExact 8
    leaf594Box leaf594Certificate leaf594InnerLog leaf594Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk36RoundedFacts chi75RoundedFacts
    innerPair117RoundedFacts leaf594RoundedFacts (by rfl)

private theorem leaf594FlatSound : Sound leaf594Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf594CertificateValid
    leaf594InnerLogValid leaf594CoversExact leaf594LowerChecked

private noncomputable def leaf595Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (25/16), chiLo := (11/16), chiHi := (3/4) }

private noncomputable def leaf595Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (16777289/16777216) }, vSqrt := { lower := (16383/16384), upper := (17179377663/17178640384) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (34044825/33554432) }, upper := { exponent := 1, mantissa := (139/128) } }, logOuter := sk35LogOuterCertificate, logK := sk35LogKCertificate, logChi := chi24LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (34358018047/34357280768) } }, logDArg := sk35LogDArgCertificate }

private noncomputable def leaf595InnerLog : WideLogData :=
  innerPair118Data

set_option maxRecDepth 1000000 in
private theorem leaf595LocalValidity :
    LeafFacts leaf595Box leaf595Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf595Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (17179377663/17178640384) }) = true
      norm_num [leaf595Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf595CertificateValid :
    WideCertificateValid leaf595Box leaf595Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk35ValidityFacts chi24ValidityFacts
    leaf595LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf595CoverageChecked :
    coverageCheck (innerAD leaf595Box) leaf595InnerLog = true := by
  rfl'

private theorem leaf595InnerLogValid :
    leaf595InnerLog.Valid 8 (innerAD leaf595Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint74PositiveFacts.valid leaf595CoverageChecked

private noncomputable def leaf595InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629441/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf595InputLogOnePlusV_eq :
    leaf595InputLogOnePlusV = outerEnclosure 24
      (leaf595Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf595RoundedFacts : LeafRoundedFacts 8
    leaf595Certificate.logOnePlusV leaf595InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf595InputLogOnePlusV_eq }

private noncomputable def leaf595Inputs : Inputs :=
  inputsOfCaches globalInput sk35RoundedInputs
    chi24InputQChi innerPair118Input
    leaf595InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf595LowerChecked :
    lowerCheck 24 leaf595Box leaf595Inputs = true := by
  rfl'

private theorem leaf595CoversExact : CoversExact 8
    leaf595Box leaf595Certificate leaf595InnerLog leaf595Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk35RoundedFacts chi24RoundedFacts
    innerPair118RoundedFacts leaf595RoundedFacts (by rfl)

private theorem leaf595FlatSound : Sound leaf595Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf595CertificateValid
    leaf595InnerLogValid leaf595CoversExact leaf595LowerChecked

private noncomputable def leaf596Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/16), kHi := (13/8), chiLo := (11/16), chiHi := (3/4) }

private noncomputable def leaf596Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (16777291/16777216) }, vSqrt := { lower := (16383/16384), upper := (17179377663/17178591232) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (34765675/33554432) }, upper := { exponent := 1, mantissa := (71/64) } }, logOuter := sk36LogOuterCertificate, logK := sk36LogKCertificate, logChi := chi24LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (34357968895/34357182464) } }, logDArg := sk36LogDArgCertificate }

private noncomputable def leaf596InnerLog : WideLogData :=
  innerPair246Data

set_option maxRecDepth 1000000 in
private theorem leaf596LocalValidity :
    LeafFacts leaf596Box leaf596Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf596Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (17179377663/17178591232) }) = true
      norm_num [leaf596Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf596CertificateValid :
    WideCertificateValid leaf596Box leaf596Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk36ValidityFacts chi24ValidityFacts
    leaf596LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf596CoverageChecked :
    coverageCheck (innerAD leaf596Box) leaf596InnerLog = true := by
  rfl'

private theorem leaf596InnerLogValid :
    leaf596InnerLog.Valid 8 (innerAD leaf596Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint80PositiveFacts.valid leaf596CoverageChecked

private noncomputable def leaf596InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629465/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf596InputLogOnePlusV_eq :
    leaf596InputLogOnePlusV = outerEnclosure 24
      (leaf596Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf596RoundedFacts : LeafRoundedFacts 8
    leaf596Certificate.logOnePlusV leaf596InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf596InputLogOnePlusV_eq }

private noncomputable def leaf596Inputs : Inputs :=
  inputsOfCaches globalInput sk36RoundedInputs
    chi24InputQChi innerPair246Input
    leaf596InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf596LowerChecked :
    lowerCheck 24 leaf596Box leaf596Inputs = true := by
  rfl'

private theorem leaf596CoversExact : CoversExact 8
    leaf596Box leaf596Certificate leaf596InnerLog leaf596Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk36RoundedFacts chi24RoundedFacts
    innerPair246RoundedFacts leaf596RoundedFacts (by rfl)

private theorem leaf596FlatSound : Sound leaf596Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf596CertificateValid
    leaf596InnerLogValid leaf596CoversExact leaf596LowerChecked

private noncomputable def leaf597Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (27/16), chiLo := (5/8), chiHi := (21/32) }

private noncomputable def leaf597Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (33554527/33554432) }, vSqrt := { lower := (16383/16384), upper := (17179377663/17178707968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (67598211/67108864) }, upper := { exponent := 1, mantissa := (1079/1024) } }, logOuter := sk33LogOuterCertificate, logK := sk33LogKCertificate, logChi := chi74LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (34358085631/34357415936) } }, logDArg := sk33LogDArgCertificate }

private noncomputable def leaf597InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf597LocalValidity :
    LeafFacts leaf597Box leaf597Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf597Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (17179377663/17178707968) }) = true
      norm_num [leaf597Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf597CertificateValid :
    WideCertificateValid leaf597Box leaf597Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk33ValidityFacts chi74ValidityFacts
    leaf597LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf597CoverageChecked :
    coverageCheck (innerAD leaf597Box) leaf597InnerLog = true := by
  rfl'

private theorem leaf597InnerLogValid :
    leaf597InnerLog.Valid 8 (innerAD leaf597Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf597CoverageChecked

private noncomputable def leaf597InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (363419/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf597InputLogOnePlusV_eq :
    leaf597InputLogOnePlusV = outerEnclosure 24
      (leaf597Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf597RoundedFacts : LeafRoundedFacts 8
    leaf597Certificate.logOnePlusV leaf597InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf597InputLogOnePlusV_eq }

private noncomputable def leaf597Inputs : Inputs :=
  inputsOfCaches globalInput sk33RoundedInputs
    chi74InputQChi innerPair117Input
    leaf597InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf597LowerChecked :
    lowerCheck 24 leaf597Box leaf597Inputs = true := by
  rfl'

private theorem leaf597CoversExact : CoversExact 8
    leaf597Box leaf597Certificate leaf597InnerLog leaf597Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk33RoundedFacts chi74RoundedFacts
    innerPair117RoundedFacts leaf597RoundedFacts (by rfl)

private theorem leaf597FlatSound : Sound leaf597Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf597CertificateValid
    leaf597InnerLogValid leaf597CoversExact leaf597LowerChecked

private noncomputable def leaf598Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (27/16), chiLo := (21/32), chiHi := (11/16) }

private noncomputable def leaf598Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (33554529/33554432) }, vSqrt := { lower := (16383/16384), upper := (17179377663/17178652672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (69302041/67108864) }, upper := { exponent := 1, mantissa := (553/512) } }, logOuter := sk33LogOuterCertificate, logK := sk33LogKCertificate, logChi := chi75LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (34358030335/34357305344) } }, logDArg := sk33LogDArgCertificate }

private noncomputable def leaf598InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf598LocalValidity :
    LeafFacts leaf598Box leaf598Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf598Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (17179377663/17178652672) }) = true
      norm_num [leaf598Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf598CertificateValid :
    WideCertificateValid leaf598Box leaf598Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk33ValidityFacts chi75ValidityFacts
    leaf598LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf598CoverageChecked :
    coverageCheck (innerAD leaf598Box) leaf598InnerLog = true := by
  rfl'

private theorem leaf598InnerLogValid :
    leaf598InnerLog.Valid 8 (innerAD leaf598Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf598CoverageChecked

private noncomputable def leaf598InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629435/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf598InputLogOnePlusV_eq :
    leaf598InputLogOnePlusV = outerEnclosure 24
      (leaf598Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf598RoundedFacts : LeafRoundedFacts 8
    leaf598Certificate.logOnePlusV leaf598InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf598InputLogOnePlusV_eq }

private noncomputable def leaf598Inputs : Inputs :=
  inputsOfCaches globalInput sk33RoundedInputs
    chi75InputQChi innerPair243Input
    leaf598InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf598LowerChecked :
    lowerCheck 24 leaf598Box leaf598Inputs = true := by
  rfl'

private theorem leaf598CoversExact : CoversExact 8
    leaf598Box leaf598Certificate leaf598InnerLog leaf598Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk33RoundedFacts chi75RoundedFacts
    innerPair243RoundedFacts leaf598RoundedFacts (by rfl)

private theorem leaf598FlatSound : Sound leaf598Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf598CertificateValid
    leaf598InnerLogValid leaf598CoversExact leaf598LowerChecked

private noncomputable def leaf599Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (5/8), chiHi := (21/32) }

private noncomputable def leaf599Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (33554529/33554432) }, vSqrt := { lower := (16383/16384), upper := (17179377663/17178664960) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (68908849/67108864) }, upper := { exponent := 1, mantissa := (275/256) } }, logOuter := sk34LogOuterCertificate, logK := sk34LogKCertificate, logChi := chi74LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (34358042623/34357329920) } }, logDArg := sk34LogDArgCertificate }

private noncomputable def leaf599InnerLog : WideLogData :=
  innerPair118Data

set_option maxRecDepth 1000000 in
private theorem leaf599LocalValidity :
    LeafFacts leaf599Box leaf599Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf599Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (17179377663/17178664960) }) = true
      norm_num [leaf599Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf599CertificateValid :
    WideCertificateValid leaf599Box leaf599Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk34ValidityFacts chi74ValidityFacts
    leaf599LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf599CoverageChecked :
    coverageCheck (innerAD leaf599Box) leaf599InnerLog = true := by
  rfl'

private theorem leaf599InnerLogValid :
    leaf599InnerLog.Valid 8 (innerAD leaf599Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint74PositiveFacts.valid leaf599CoverageChecked

private noncomputable def leaf599InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629429/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf599InputLogOnePlusV_eq :
    leaf599InputLogOnePlusV = outerEnclosure 24
      (leaf599Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf599RoundedFacts : LeafRoundedFacts 8
    leaf599Certificate.logOnePlusV leaf599InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf599InputLogOnePlusV_eq }

private noncomputable def leaf599Inputs : Inputs :=
  inputsOfCaches globalInput sk34RoundedInputs
    chi74InputQChi innerPair118Input
    leaf599InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf599LowerChecked :
    lowerCheck 24 leaf599Box leaf599Inputs = true := by
  rfl'

private theorem leaf599CoversExact : CoversExact 8
    leaf599Box leaf599Certificate leaf599InnerLog leaf599Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk34RoundedFacts chi74RoundedFacts
    innerPair118RoundedFacts leaf599RoundedFacts (by rfl)

private theorem leaf599FlatSound : Sound leaf599Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf599CertificateValid
    leaf599InnerLogValid leaf599CoversExact leaf599LowerChecked

private noncomputable def leaf600Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (21/32), chiHi := (11/16) }

private noncomputable def leaf600Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (33554531/33554432) }, vSqrt := { lower := (16383/16384), upper := (17179377663/17178607616) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (70678211/67108864) }, upper := { exponent := 1, mantissa := (141/128) } }, logOuter := sk34LogOuterCertificate, logK := sk34LogKCertificate, logChi := chi75LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (34357985279/34357215232) } }, logDArg := sk34LogDArgCertificate }

private noncomputable def leaf600InnerLog : WideLogData :=
  innerPair244Data

set_option maxRecDepth 1000000 in
private theorem leaf600LocalValidity :
    LeafFacts leaf600Box leaf600Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf600Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (17179377663/17178607616) }) = true
      norm_num [leaf600Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf600CertificateValid :
    WideCertificateValid leaf600Box leaf600Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk34ValidityFacts chi75ValidityFacts
    leaf600LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf600CoverageChecked :
    coverageCheck (innerAD leaf600Box) leaf600InnerLog = true := by
  rfl'

private theorem leaf600InnerLogValid :
    leaf600InnerLog.Valid 8 (innerAD leaf600Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint75PositiveFacts.valid leaf600CoverageChecked

private noncomputable def leaf600InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629457/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf600InputLogOnePlusV_eq :
    leaf600InputLogOnePlusV = outerEnclosure 24
      (leaf600Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf600RoundedFacts : LeafRoundedFacts 8
    leaf600Certificate.logOnePlusV leaf600InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf600InputLogOnePlusV_eq }

private noncomputable def leaf600Inputs : Inputs :=
  inputsOfCaches globalInput sk34RoundedInputs
    chi75InputQChi innerPair244Input
    leaf600InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf600LowerChecked :
    lowerCheck 24 leaf600Box leaf600Inputs = true := by
  rfl'

private theorem leaf600CoversExact : CoversExact 8
    leaf600Box leaf600Certificate leaf600InnerLog leaf600Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk34RoundedFacts chi75RoundedFacts
    innerPair244RoundedFacts leaf600RoundedFacts (by rfl)

private theorem leaf600FlatSound : Sound leaf600Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf600CertificateValid
    leaf600InnerLogValid leaf600CoversExact leaf600LowerChecked

private noncomputable def leaf601Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (27/16), chiLo := (11/16), chiHi := (23/32) }

private noncomputable def leaf601Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (33554531/33554432) }, vSqrt := { lower := (16383/16384), upper := (17179377663/17178597376) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (71005871/67108864) }, upper := { exponent := 1, mantissa := (1133/1024) } }, logOuter := sk33LogOuterCertificate, logK := sk33LogKCertificate, logChi := chi80LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (34357975039/34357194752) } }, logDArg := sk33LogDArgCertificate }

private noncomputable def leaf601InnerLog : WideLogData :=
  innerPair244Data

set_option maxRecDepth 1000000 in
private theorem leaf601LocalValidity :
    LeafFacts leaf601Box leaf601Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf601Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (17179377663/17178597376) }) = true
      norm_num [leaf601Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf601CertificateValid :
    WideCertificateValid leaf601Box leaf601Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk33ValidityFacts chi80ValidityFacts
    leaf601LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf601CoverageChecked :
    coverageCheck (innerAD leaf601Box) leaf601InnerLog = true := by
  rfl'

private theorem leaf601InnerLogValid :
    leaf601InnerLog.Valid 8 (innerAD leaf601Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint75PositiveFacts.valid leaf601CoverageChecked

private noncomputable def leaf601InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814731/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf601InputLogOnePlusV_eq :
    leaf601InputLogOnePlusV = outerEnclosure 24
      (leaf601Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf601RoundedFacts : LeafRoundedFacts 8
    leaf601Certificate.logOnePlusV leaf601InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf601InputLogOnePlusV_eq }

private noncomputable def leaf601Inputs : Inputs :=
  inputsOfCaches globalInput sk33RoundedInputs
    chi80InputQChi innerPair244Input
    leaf601InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf601LowerChecked :
    lowerCheck 24 leaf601Box leaf601Inputs = true := by
  rfl'

private theorem leaf601CoversExact : CoversExact 8
    leaf601Box leaf601Certificate leaf601InnerLog leaf601Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk33RoundedFacts chi80RoundedFacts
    innerPair244RoundedFacts leaf601RoundedFacts (by rfl)

private theorem leaf601FlatSound : Sound leaf601Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf601CertificateValid
    leaf601InnerLogValid leaf601CoversExact leaf601LowerChecked

private noncomputable def leaf602Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (27/16), chiLo := (23/32), chiHi := (3/4) }

private noncomputable def leaf602Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (33554533/33554432) }, vSqrt := { lower := (16383/16384), upper := (2454196809/2454077440) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (72709701/67108864) }, upper := { exponent := 1, mantissa := (145/128) } }, logOuter := sk33LogOuterCertificate, logK := sk33LogKCertificate, logChi := chi81LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (4908274249/4908154880) } }, logDArg := sk33LogDArgCertificate }

private noncomputable def leaf602InnerLog : WideLogData :=
  innerPair251Data

set_option maxRecDepth 1000000 in
private theorem leaf602LocalValidity :
    LeafFacts leaf602Box leaf602Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf602Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (2454196809/2454077440) }) = true
      norm_num [leaf602Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf602CertificateValid :
    WideCertificateValid leaf602Box leaf602Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk33ValidityFacts chi81ValidityFacts
    leaf602LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf602CoverageChecked :
    coverageCheck (innerAD leaf602Box) leaf602InnerLog = true := by
  rfl'

private theorem leaf602InnerLogValid :
    leaf602InnerLog.Valid 8 (innerAD leaf602Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint76PositiveFacts.valid leaf602CoverageChecked

private noncomputable def leaf602InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629489/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf602InputLogOnePlusV_eq :
    leaf602InputLogOnePlusV = outerEnclosure 24
      (leaf602Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf602RoundedFacts : LeafRoundedFacts 8
    leaf602Certificate.logOnePlusV leaf602InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf602InputLogOnePlusV_eq }

private noncomputable def leaf602Inputs : Inputs :=
  inputsOfCaches globalInput sk33RoundedInputs
    chi81InputQChi innerPair251Input
    leaf602InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf602LowerChecked :
    lowerCheck 24 leaf602Box leaf602Inputs = true := by
  rfl'

private theorem leaf602CoversExact : CoversExact 8
    leaf602Box leaf602Certificate leaf602InnerLog leaf602Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk33RoundedFacts chi81RoundedFacts
    innerPair251RoundedFacts leaf602RoundedFacts (by rfl)

private theorem leaf602FlatSound : Sound leaf602Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf602CertificateValid
    leaf602InnerLogValid leaf602CoversExact leaf602LowerChecked

private noncomputable def leaf603Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (11/16), chiHi := (23/32) }

private noncomputable def leaf603Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (33554533/33554432) }, vSqrt := { lower := (16383/16384), upper := (5726459221/5726183424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (72447573/67108864) }, upper := { exponent := 1, mantissa := (289/256) } }, logOuter := sk34LogOuterCertificate, logK := sk34LogKCertificate, logChi := chi80LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (11452642645/11452366848) } }, logDArg := sk34LogDArgCertificate }

private noncomputable def leaf603InnerLog : WideLogData :=
  innerPair251Data

set_option maxRecDepth 1000000 in
private theorem leaf603LocalValidity :
    LeafFacts leaf603Box leaf603Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf603Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (5726459221/5726183424) }) = true
      norm_num [leaf603Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf603CertificateValid :
    WideCertificateValid leaf603Box leaf603Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk34ValidityFacts chi80ValidityFacts
    leaf603LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf603CoverageChecked :
    coverageCheck (innerAD leaf603Box) leaf603InnerLog = true := by
  rfl'

private theorem leaf603InnerLogValid :
    leaf603InnerLog.Valid 8 (innerAD leaf603Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint76PositiveFacts.valid leaf603CoverageChecked

private noncomputable def leaf603InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629485/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf603InputLogOnePlusV_eq :
    leaf603InputLogOnePlusV = outerEnclosure 24
      (leaf603Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf603RoundedFacts : LeafRoundedFacts 8
    leaf603Certificate.logOnePlusV leaf603InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf603InputLogOnePlusV_eq }

private noncomputable def leaf603Inputs : Inputs :=
  inputsOfCaches globalInput sk34RoundedInputs
    chi80InputQChi innerPair251Input
    leaf603InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf603LowerChecked :
    lowerCheck 24 leaf603Box leaf603Inputs = true := by
  rfl'

private theorem leaf603CoversExact : CoversExact 8
    leaf603Box leaf603Certificate leaf603InnerLog leaf603Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk34RoundedFacts chi80RoundedFacts
    innerPair251RoundedFacts leaf603RoundedFacts (by rfl)

private theorem leaf603FlatSound : Sound leaf603Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf603CertificateValid
    leaf603InnerLogValid leaf603CoversExact leaf603LowerChecked

private noncomputable def leaf604Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (23/32), chiHi := (3/4) }

private noncomputable def leaf604Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (33554535/33554432) }, vSqrt := { lower := (16383/16384), upper := (17179377663/17178492928) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (74216935/67108864) }, upper := { exponent := 1, mantissa := (37/32) } }, logOuter := sk34LogOuterCertificate, logK := sk34LogKCertificate, logChi := chi81LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (34357870591/34356985856) } }, logDArg := sk34LogDArgCertificate }

private noncomputable def leaf604InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf604LocalValidity :
    LeafFacts leaf604Box leaf604Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf604Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (17179377663/17178492928) }) = true
      norm_num [leaf604Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf604CertificateValid :
    WideCertificateValid leaf604Box leaf604Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk34ValidityFacts chi81ValidityFacts
    leaf604LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf604CoverageChecked :
    coverageCheck (innerAD leaf604Box) leaf604InnerLog = true := by
  rfl'

private theorem leaf604InnerLogValid :
    leaf604InnerLog.Valid 8 (innerAD leaf604Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf604CoverageChecked

private noncomputable def leaf604InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629513/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf604InputLogOnePlusV_eq :
    leaf604InputLogOnePlusV = outerEnclosure 24
      (leaf604Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf604RoundedFacts : LeafRoundedFacts 8
    leaf604Certificate.logOnePlusV leaf604InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf604InputLogOnePlusV_eq }

private noncomputable def leaf604Inputs : Inputs :=
  inputsOfCaches globalInput sk34RoundedInputs
    chi81InputQChi innerPair257Input
    leaf604InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf604LowerChecked :
    lowerCheck 24 leaf604Box leaf604Inputs = true := by
  rfl'

private theorem leaf604CoversExact : CoversExact 8
    leaf604Box leaf604Certificate leaf604InnerLog leaf604Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk34RoundedFacts chi81RoundedFacts
    innerPair257RoundedFacts leaf604RoundedFacts (by rfl)

private theorem leaf604FlatSound : Sound leaf604Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf604CertificateValid
    leaf604InnerLogValid leaf604CoversExact leaf604LowerChecked

private noncomputable def component14Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (25/16), chiLo := (1/2), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component14Node0_sound : Sound component14Node0Box :=
  sound_of_literal_split component14Node0Box leaf575Box leaf576Box
    .chi (17/32) (by rfl) (by rfl)
    leaf575FlatSound leaf576FlatSound

private noncomputable def component14Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/16), kHi := (13/8), chiLo := (1/2), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component14Node1_sound : Sound component14Node1Box :=
  sound_of_literal_split component14Node1Box leaf577Box leaf578Box
    .chi (17/32) (by rfl) (by rfl)
    leaf577FlatSound leaf578FlatSound

private noncomputable def component14Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (13/8), chiLo := (1/2), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component14Node2_sound : Sound component14Node2Box :=
  sound_of_literal_split component14Node2Box component14Node0Box component14Node1Box
    .k (25/16) (by rfl) (by rfl)
    component14Node0_sound component14Node1_sound

private noncomputable def component14Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (25/16), chiLo := (9/16), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component14Node3_sound : Sound component14Node3Box :=
  sound_of_literal_split component14Node3Box leaf579Box leaf580Box
    .chi (19/32) (by rfl) (by rfl)
    leaf579FlatSound leaf580FlatSound

private noncomputable def component14Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/16), kHi := (13/8), chiLo := (9/16), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component14Node4_sound : Sound component14Node4Box :=
  sound_of_literal_split component14Node4Box leaf581Box leaf582Box
    .chi (19/32) (by rfl) (by rfl)
    leaf581FlatSound leaf582FlatSound

private noncomputable def component14Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (13/8), chiLo := (9/16), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component14Node5_sound : Sound component14Node5Box :=
  sound_of_literal_split component14Node5Box component14Node3Box component14Node4Box
    .k (25/16) (by rfl) (by rfl)
    component14Node3_sound component14Node4_sound

private noncomputable def component14Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (13/8), chiLo := (1/2), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component14Node6_sound : Sound component14Node6Box :=
  sound_of_literal_split component14Node6Box component14Node2Box component14Node5Box
    .chi (9/16) (by rfl) (by rfl)
    component14Node2_sound component14Node5_sound

private noncomputable def component14Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (7/4), chiLo := (1/2), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component14Node7_sound : Sound component14Node7Box :=
  sound_of_literal_split component14Node7Box leaf583Box leaf584Box
    .k (27/16) (by rfl) (by rfl)
    leaf583FlatSound leaf584FlatSound

private noncomputable def component14Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (7/4), chiLo := (17/32), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component14Node8_sound : Sound component14Node8Box :=
  sound_of_literal_split component14Node8Box leaf585Box leaf586Box
    .k (27/16) (by rfl) (by rfl)
    leaf585FlatSound leaf586FlatSound

private noncomputable def component14Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (7/4), chiLo := (1/2), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component14Node9_sound : Sound component14Node9Box :=
  sound_of_literal_split component14Node9Box component14Node7Box component14Node8Box
    .chi (17/32) (by rfl) (by rfl)
    component14Node7_sound component14Node8_sound

private noncomputable def component14Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (27/16), chiLo := (9/16), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component14Node10_sound : Sound component14Node10Box :=
  sound_of_literal_split component14Node10Box leaf587Box leaf588Box
    .chi (19/32) (by rfl) (by rfl)
    leaf587FlatSound leaf588FlatSound

private noncomputable def component14Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (9/16), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component14Node11_sound : Sound component14Node11Box :=
  sound_of_literal_split component14Node11Box leaf589Box leaf590Box
    .chi (19/32) (by rfl) (by rfl)
    leaf589FlatSound leaf590FlatSound

private noncomputable def component14Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (7/4), chiLo := (9/16), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component14Node12_sound : Sound component14Node12Box :=
  sound_of_literal_split component14Node12Box component14Node10Box component14Node11Box
    .k (27/16) (by rfl) (by rfl)
    component14Node10_sound component14Node11_sound

private noncomputable def component14Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (7/4), chiLo := (1/2), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component14Node13_sound : Sound component14Node13Box :=
  sound_of_literal_split component14Node13Box component14Node9Box component14Node12Box
    .chi (9/16) (by rfl) (by rfl)
    component14Node9_sound component14Node12_sound

private noncomputable def component14Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (7/4), chiLo := (1/2), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component14Node14_sound : Sound component14Node14Box :=
  sound_of_literal_split component14Node14Box component14Node6Box component14Node13Box
    .k (13/8) (by rfl) (by rfl)
    component14Node6_sound component14Node13_sound

private noncomputable def component14Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (25/16), chiLo := (5/8), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component14Node15_sound : Sound component14Node15Box :=
  sound_of_literal_split component14Node15Box leaf591Box leaf592Box
    .chi (21/32) (by rfl) (by rfl)
    leaf591FlatSound leaf592FlatSound

private noncomputable def component14Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/16), kHi := (13/8), chiLo := (5/8), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component14Node16_sound : Sound component14Node16Box :=
  sound_of_literal_split component14Node16Box leaf593Box leaf594Box
    .chi (21/32) (by rfl) (by rfl)
    leaf593FlatSound leaf594FlatSound

private noncomputable def component14Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (13/8), chiLo := (5/8), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component14Node17_sound : Sound component14Node17Box :=
  sound_of_literal_split component14Node17Box component14Node15Box component14Node16Box
    .k (25/16) (by rfl) (by rfl)
    component14Node15_sound component14Node16_sound

private noncomputable def component14Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (13/8), chiLo := (11/16), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component14Node18_sound : Sound component14Node18Box :=
  sound_of_literal_split component14Node18Box leaf595Box leaf596Box
    .k (25/16) (by rfl) (by rfl)
    leaf595FlatSound leaf596FlatSound

private noncomputable def component14Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (13/8), chiLo := (5/8), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component14Node19_sound : Sound component14Node19Box :=
  sound_of_literal_split component14Node19Box component14Node17Box component14Node18Box
    .chi (11/16) (by rfl) (by rfl)
    component14Node17_sound component14Node18_sound

private noncomputable def component14Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (27/16), chiLo := (5/8), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component14Node20_sound : Sound component14Node20Box :=
  sound_of_literal_split component14Node20Box leaf597Box leaf598Box
    .chi (21/32) (by rfl) (by rfl)
    leaf597FlatSound leaf598FlatSound

private noncomputable def component14Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (5/8), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component14Node21_sound : Sound component14Node21Box :=
  sound_of_literal_split component14Node21Box leaf599Box leaf600Box
    .chi (21/32) (by rfl) (by rfl)
    leaf599FlatSound leaf600FlatSound

private noncomputable def component14Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (7/4), chiLo := (5/8), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component14Node22_sound : Sound component14Node22Box :=
  sound_of_literal_split component14Node22Box component14Node20Box component14Node21Box
    .k (27/16) (by rfl) (by rfl)
    component14Node20_sound component14Node21_sound

private noncomputable def component14Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (27/16), chiLo := (11/16), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component14Node23_sound : Sound component14Node23Box :=
  sound_of_literal_split component14Node23Box leaf601Box leaf602Box
    .chi (23/32) (by rfl) (by rfl)
    leaf601FlatSound leaf602FlatSound

private noncomputable def component14Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (11/16), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component14Node24_sound : Sound component14Node24Box :=
  sound_of_literal_split component14Node24Box leaf603Box leaf604Box
    .chi (23/32) (by rfl) (by rfl)
    leaf603FlatSound leaf604FlatSound

private noncomputable def component14Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (7/4), chiLo := (11/16), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component14Node25_sound : Sound component14Node25Box :=
  sound_of_literal_split component14Node25Box component14Node23Box component14Node24Box
    .k (27/16) (by rfl) (by rfl)
    component14Node23_sound component14Node24_sound

private noncomputable def component14Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (7/4), chiLo := (5/8), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component14Node26_sound : Sound component14Node26Box :=
  sound_of_literal_split component14Node26Box component14Node22Box component14Node25Box
    .chi (11/16) (by rfl) (by rfl)
    component14Node22_sound component14Node25_sound

private noncomputable def component14Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (7/4), chiLo := (5/8), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component14Node27_sound : Sound component14Node27Box :=
  sound_of_literal_split component14Node27Box component14Node19Box component14Node26Box
    .k (13/8) (by rfl) (by rfl)
    component14Node19_sound component14Node26_sound

noncomputable def component14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (7/4), chiLo := (1/2), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
theorem component14_sound : Sound component14Box :=
  sound_of_literal_split component14Box component14Node14Box component14Node27Box
    .chi (5/8) (by rfl) (by rfl)
    component14Node14_sound component14Node27_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
