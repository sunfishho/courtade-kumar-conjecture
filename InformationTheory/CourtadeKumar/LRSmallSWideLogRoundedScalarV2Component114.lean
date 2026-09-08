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

private noncomputable def leaf5633Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (7/16), chiHi := (57/128) }

private noncomputable def leaf5633Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435763/268435456) }, vSqrt := { lower := (65529/65536), upper := (2021101327/2020994560) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (620702415/536870912) }, upper := { exponent := 1, mantissa := (9625/8192) } }, logOuter := sk133LogOuterCertificate, logK := sk133LogKCertificate, logChi := chi267LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (4042095887/4041989120) } }, logDArg := sk133LogDArgCertificate }

private noncomputable def leaf5633InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf5633LocalValidity :
    LeafFacts leaf5633Box leaf5633Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5633Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (2021101327/2020994560) }) = true
      norm_num [leaf5633Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5633CertificateValid :
    WideCertificateValid leaf5633Box leaf5633Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk133ValidityFacts chi267ValidityFacts
    leaf5633LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5633CoverageChecked :
    coverageCheck (innerAD leaf5633Box) leaf5633InnerLog = true := by
  rfl'

private theorem leaf5633InnerLogValid :
    leaf5633InnerLog.Valid 8 (innerAD leaf5633Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf5633CoverageChecked

private noncomputable def leaf5633InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907381/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5633InputLogOnePlusV_eq :
    leaf5633InputLogOnePlusV = outerEnclosure 24
      (leaf5633Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5633RoundedFacts : LeafRoundedFacts 8
    leaf5633Certificate.logOnePlusV leaf5633InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5633InputLogOnePlusV_eq }

private noncomputable def leaf5633Inputs : Inputs :=
  inputsOfCaches globalInput sk133RoundedInputs
    chi267InputQChi innerPair265Input
    leaf5633InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5633LowerChecked :
    lowerCheck 24 leaf5633Box leaf5633Inputs = true := by
  rfl'

private theorem leaf5633CoversExact : CoversExact 8
    leaf5633Box leaf5633Certificate leaf5633InnerLog leaf5633Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk133RoundedFacts chi267RoundedFacts
    innerPair265RoundedFacts leaf5633RoundedFacts (by rfl)

private theorem leaf5633FlatSound : Sound leaf5633Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5633CertificateValid
    leaf5633InnerLogValid leaf5633CoversExact leaf5633LowerChecked

private noncomputable def leaf5634Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (7/16), chiHi := (57/128) }

private noncomputable def leaf5634Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435765/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356878336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (624372205/536870912) }, upper := { exponent := 1, mantissa := (4841/4096) } }, logOuter := sk134LogOuterCertificate, logK := sk134LogKCertificate, logChi := chi267LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715600895/68713756672) } }, logDArg := sk134LogDArgCertificate }

private noncomputable def leaf5634InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf5634LocalValidity :
    LeafFacts leaf5634Box leaf5634Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5634Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356878336) }) = true
      norm_num [leaf5634Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5634CertificateValid :
    WideCertificateValid leaf5634Box leaf5634Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk134ValidityFacts chi267ValidityFacts
    leaf5634LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5634CoverageChecked :
    coverageCheck (innerAD leaf5634Box) leaf5634InnerLog = true := by
  rfl'

private theorem leaf5634InnerLogValid :
    leaf5634InnerLog.Valid 8 (innerAD leaf5634Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf5634CoverageChecked

private noncomputable def leaf5634InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629531/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5634InputLogOnePlusV_eq :
    leaf5634InputLogOnePlusV = outerEnclosure 24
      (leaf5634Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5634RoundedFacts : LeafRoundedFacts 8
    leaf5634Certificate.logOnePlusV leaf5634InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5634InputLogOnePlusV_eq }

private noncomputable def leaf5634Inputs : Inputs :=
  inputsOfCaches globalInput sk134RoundedInputs
    chi267InputQChi innerPair272Input
    leaf5634InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5634LowerChecked :
    lowerCheck 24 leaf5634Box leaf5634Inputs = true := by
  rfl'

private theorem leaf5634CoversExact : CoversExact 8
    leaf5634Box leaf5634Certificate leaf5634InnerLog leaf5634Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk134RoundedFacts chi267RoundedFacts
    innerPair272RoundedFacts leaf5634RoundedFacts (by rfl)

private theorem leaf5634FlatSound : Sound leaf5634Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5634CertificateValid
    leaf5634InnerLogValid leaf5634CoversExact leaf5634LowerChecked

private noncomputable def leaf5635Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (57/128), chiHi := (29/64) }

private noncomputable def leaf5635Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435765/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356857856) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (626993485/536870912) }, upper := { exponent := 1, mantissa := (4861/4096) } }, logOuter := sk133LogOuterCertificate, logK := sk133LogKCertificate, logChi := chi268LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715580415/68713715712) } }, logDArg := sk133LogDArgCertificate }

private noncomputable def leaf5635InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf5635LocalValidity :
    LeafFacts leaf5635Box leaf5635Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5635Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356857856) }) = true
      norm_num [leaf5635Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5635CertificateValid :
    WideCertificateValid leaf5635Box leaf5635Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk133ValidityFacts chi268ValidityFacts
    leaf5635LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5635CoverageChecked :
    coverageCheck (innerAD leaf5635Box) leaf5635InnerLog = true := by
  rfl'

private theorem leaf5635InnerLogValid :
    leaf5635InnerLog.Valid 8 (innerAD leaf5635Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf5635CoverageChecked

private noncomputable def leaf5635InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (363423/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf5635InputLogOnePlusV_eq :
    leaf5635InputLogOnePlusV = outerEnclosure 24
      (leaf5635Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5635RoundedFacts : LeafRoundedFacts 8
    leaf5635Certificate.logOnePlusV leaf5635InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5635InputLogOnePlusV_eq }

private noncomputable def leaf5635Inputs : Inputs :=
  inputsOfCaches globalInput sk133RoundedInputs
    chi268InputQChi innerPair272Input
    leaf5635InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5635LowerChecked :
    lowerCheck 24 leaf5635Box leaf5635Inputs = true := by
  rfl'

private theorem leaf5635CoversExact : CoversExact 8
    leaf5635Box leaf5635Certificate leaf5635InnerLog leaf5635Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk133RoundedFacts chi268RoundedFacts
    innerPair272RoundedFacts leaf5635RoundedFacts (by rfl)

private theorem leaf5635FlatSound : Sound leaf5635Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5635CertificateValid
    leaf5635InnerLogValid leaf5635CoversExact leaf5635LowerChecked

private noncomputable def leaf5636Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (57/128), chiHi := (29/64) }

private noncomputable def leaf5636Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435767/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356828160) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (630728807/536870912) }, upper := { exponent := 1, mantissa := (2445/2048) } }, logOuter := sk134LogOuterCertificate, logK := sk134LogKCertificate, logChi := chi268LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715550719/68713656320) } }, logDArg := sk134LogDArgCertificate }

private noncomputable def leaf5636InnerLog : WideLogData :=
  innerPair273Data

set_option maxRecDepth 1000000 in
private theorem leaf5636LocalValidity :
    LeafFacts leaf5636Box leaf5636Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5636Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356828160) }) = true
      norm_num [leaf5636Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5636CertificateValid :
    WideCertificateValid leaf5636Box leaf5636Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk134ValidityFacts chi268ValidityFacts
    leaf5636LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5636CoverageChecked :
    coverageCheck (innerAD leaf5636Box) leaf5636InnerLog = true := by
  rfl'

private theorem leaf5636InnerLogValid :
    leaf5636InnerLog.Valid 8 (innerAD leaf5636Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint78PositiveFacts.valid leaf5636CoverageChecked

private noncomputable def leaf5636InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629543/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5636InputLogOnePlusV_eq :
    leaf5636InputLogOnePlusV = outerEnclosure 24
      (leaf5636Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5636RoundedFacts : LeafRoundedFacts 8
    leaf5636Certificate.logOnePlusV leaf5636InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5636InputLogOnePlusV_eq }

private noncomputable def leaf5636Inputs : Inputs :=
  inputsOfCaches globalInput sk134RoundedInputs
    chi268InputQChi innerPair273Input
    leaf5636InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5636LowerChecked :
    lowerCheck 24 leaf5636Box leaf5636Inputs = true := by
  rfl'

private theorem leaf5636CoversExact : CoversExact 8
    leaf5636Box leaf5636Certificate leaf5636InnerLog leaf5636Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk134RoundedFacts chi268RoundedFacts
    innerPair273RoundedFacts leaf5636RoundedFacts (by rfl)

private theorem leaf5636FlatSound : Sound leaf5636Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5636CertificateValid
    leaf5636InnerLogValid leaf5636CoversExact leaf5636LowerChecked

private noncomputable def leaf5637Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (7/16), chiHi := (57/128) }

private noncomputable def leaf5637Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435767/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356849152) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (628041995/536870912) }, upper := { exponent := 1, mantissa := (9739/8192) } }, logOuter := sk135LogOuterCertificate, logK := sk135LogKCertificate, logChi := chi267LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715571711/68713698304) } }, logDArg := sk135LogDArgCertificate }

private noncomputable def leaf5637InnerLog : WideLogData :=
  innerPair273Data

set_option maxRecDepth 1000000 in
private theorem leaf5637LocalValidity :
    LeafFacts leaf5637Box leaf5637Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5637Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356849152) }) = true
      norm_num [leaf5637Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5637CertificateValid :
    WideCertificateValid leaf5637Box leaf5637Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk135ValidityFacts chi267ValidityFacts
    leaf5637LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5637CoverageChecked :
    coverageCheck (innerAD leaf5637Box) leaf5637InnerLog = true := by
  rfl'

private theorem leaf5637InnerLogValid :
    leaf5637InnerLog.Valid 8 (innerAD leaf5637Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint78PositiveFacts.valid leaf5637CoverageChecked

private noncomputable def leaf5637InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814769/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5637InputLogOnePlusV_eq :
    leaf5637InputLogOnePlusV = outerEnclosure 24
      (leaf5637Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5637RoundedFacts : LeafRoundedFacts 8
    leaf5637Certificate.logOnePlusV leaf5637InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5637InputLogOnePlusV_eq }

private noncomputable def leaf5637Inputs : Inputs :=
  inputsOfCaches globalInput sk135RoundedInputs
    chi267InputQChi innerPair273Input
    leaf5637InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5637LowerChecked :
    lowerCheck 24 leaf5637Box leaf5637Inputs = true := by
  rfl'

private theorem leaf5637CoversExact : CoversExact 8
    leaf5637Box leaf5637Certificate leaf5637InnerLog leaf5637Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk135RoundedFacts chi267RoundedFacts
    innerPair273RoundedFacts leaf5637RoundedFacts (by rfl)

private theorem leaf5637FlatSound : Sound leaf5637Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5637CertificateValid
    leaf5637InnerLogValid leaf5637CoversExact leaf5637LowerChecked

private noncomputable def leaf5638Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (7/16), chiHi := (57/128) }

private noncomputable def leaf5638Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435769/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356819968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (631711785/536870912) }, upper := { exponent := 1, mantissa := (2449/2048) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi267LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715542527/68713639936) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf5638InnerLog : WideLogData :=
  innerPair273Data

set_option maxRecDepth 1000000 in
private theorem leaf5638LocalValidity :
    LeafFacts leaf5638Box leaf5638Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5638Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356819968) }) = true
      norm_num [leaf5638Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5638CertificateValid :
    WideCertificateValid leaf5638Box leaf5638Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi267ValidityFacts
    leaf5638LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5638CoverageChecked :
    coverageCheck (innerAD leaf5638Box) leaf5638InnerLog = true := by
  rfl'

private theorem leaf5638InnerLogValid :
    leaf5638InnerLog.Valid 8 (innerAD leaf5638Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint78PositiveFacts.valid leaf5638CoverageChecked

private noncomputable def leaf5638InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629545/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5638InputLogOnePlusV_eq :
    leaf5638InputLogOnePlusV = outerEnclosure 24
      (leaf5638Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5638RoundedFacts : LeafRoundedFacts 8
    leaf5638Certificate.logOnePlusV leaf5638InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5638InputLogOnePlusV_eq }

private noncomputable def leaf5638Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi267InputQChi innerPair273Input
    leaf5638InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5638LowerChecked :
    lowerCheck 24 leaf5638Box leaf5638Inputs = true := by
  rfl'

private theorem leaf5638CoversExact : CoversExact 8
    leaf5638Box leaf5638Certificate leaf5638InnerLog leaf5638Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi267RoundedFacts
    innerPair273RoundedFacts leaf5638RoundedFacts (by rfl)

private theorem leaf5638FlatSound : Sound leaf5638Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5638CertificateValid
    leaf5638InnerLogValid leaf5638CoversExact leaf5638LowerChecked

private noncomputable def leaf5639Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (57/128), chiHi := (29/64) }

private noncomputable def leaf5639Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435769/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356798464) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (634464129/536870912) }, upper := { exponent := 1, mantissa := (4919/4096) } }, logOuter := sk135LogOuterCertificate, logK := sk135LogKCertificate, logChi := chi268LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715521023/68713596928) } }, logDArg := sk135LogDArgCertificate }

private noncomputable def leaf5639InnerLog : WideLogData :=
  innerPair273Data

set_option maxRecDepth 1000000 in
private theorem leaf5639LocalValidity :
    LeafFacts leaf5639Box leaf5639Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5639Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356798464) }) = true
      norm_num [leaf5639Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5639CertificateValid :
    WideCertificateValid leaf5639Box leaf5639Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk135ValidityFacts chi268ValidityFacts
    leaf5639LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5639CoverageChecked :
    coverageCheck (innerAD leaf5639Box) leaf5639InnerLog = true := by
  rfl'

private theorem leaf5639InnerLogValid :
    leaf5639InnerLog.Valid 8 (innerAD leaf5639Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint78PositiveFacts.valid leaf5639CoverageChecked

private noncomputable def leaf5639InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629551/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5639InputLogOnePlusV_eq :
    leaf5639InputLogOnePlusV = outerEnclosure 24
      (leaf5639Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5639RoundedFacts : LeafRoundedFacts 8
    leaf5639Certificate.logOnePlusV leaf5639InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5639InputLogOnePlusV_eq }

private noncomputable def leaf5639Inputs : Inputs :=
  inputsOfCaches globalInput sk135RoundedInputs
    chi268InputQChi innerPair273Input
    leaf5639InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5639LowerChecked :
    lowerCheck 24 leaf5639Box leaf5639Inputs = true := by
  rfl'

private theorem leaf5639CoversExact : CoversExact 8
    leaf5639Box leaf5639Certificate leaf5639InnerLog leaf5639Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk135RoundedFacts chi268RoundedFacts
    innerPair273RoundedFacts leaf5639RoundedFacts (by rfl)

private theorem leaf5639FlatSound : Sound leaf5639Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5639CertificateValid
    leaf5639InnerLogValid leaf5639CoversExact leaf5639LowerChecked

private noncomputable def leaf5640Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (57/128), chiHi := (29/64) }

private noncomputable def leaf5640Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435771/268435456) }, vSqrt := { lower := (65529/65536), upper := (4908388937/4908109824) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (638199451/536870912) }, upper := { exponent := 1, mantissa := (1237/1024) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi268LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9816498761/9816219648) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf5640InnerLog : WideLogData :=
  innerPair278Data

set_option maxRecDepth 1000000 in
private theorem leaf5640LocalValidity :
    LeafFacts leaf5640Box leaf5640Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5640Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4908388937/4908109824) }) = true
      norm_num [leaf5640Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5640CertificateValid :
    WideCertificateValid leaf5640Box leaf5640Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi268ValidityFacts
    leaf5640LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5640CoverageChecked :
    coverageCheck (innerAD leaf5640Box) leaf5640InnerLog = true := by
  rfl'

private theorem leaf5640InnerLogValid :
    leaf5640InnerLog.Valid 8 (innerAD leaf5640Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint78PositiveFacts.valid leaf5640CoverageChecked

private noncomputable def leaf5640InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814779/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5640InputLogOnePlusV_eq :
    leaf5640InputLogOnePlusV = outerEnclosure 24
      (leaf5640Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5640RoundedFacts : LeafRoundedFacts 8
    leaf5640Certificate.logOnePlusV leaf5640InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5640InputLogOnePlusV_eq }

private noncomputable def leaf5640Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi268InputQChi innerPair278Input
    leaf5640InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5640LowerChecked :
    lowerCheck 24 leaf5640Box leaf5640Inputs = true := by
  rfl'

private theorem leaf5640CoversExact : CoversExact 8
    leaf5640Box leaf5640Certificate leaf5640InnerLog leaf5640Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi268RoundedFacts
    innerPair278RoundedFacts leaf5640RoundedFacts (by rfl)

private theorem leaf5640FlatSound : Sound leaf5640Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5640CertificateValid
    leaf5640InnerLogValid leaf5640CoversExact leaf5640LowerChecked

private noncomputable def leaf5641Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (29/64), chiHi := (59/128) }

private noncomputable def leaf5641Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435767/268435456) }, vSqrt := { lower := (65529/65536), upper := (4908388937/4908115456) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (633284555/536870912) }, upper := { exponent := 1, mantissa := (9819/8192) } }, logOuter := sk133LogOuterCertificate, logK := sk133LogKCertificate, logChi := chi269LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9816504393/9816230912) } }, logDArg := sk133LogDArgCertificate }

private noncomputable def leaf5641InnerLog : WideLogData :=
  innerPair273Data

set_option maxRecDepth 1000000 in
private theorem leaf5641LocalValidity :
    LeafFacts leaf5641Box leaf5641Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5641Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4908388937/4908115456) }) = true
      norm_num [leaf5641Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5641CertificateValid :
    WideCertificateValid leaf5641Box leaf5641Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk133ValidityFacts chi269ValidityFacts
    leaf5641LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5641CoverageChecked :
    coverageCheck (innerAD leaf5641Box) leaf5641InnerLog = true := by
  rfl'

private theorem leaf5641InnerLogValid :
    leaf5641InnerLog.Valid 8 (innerAD leaf5641Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint78PositiveFacts.valid leaf5641CoverageChecked

private noncomputable def leaf5641InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907387/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5641InputLogOnePlusV_eq :
    leaf5641InputLogOnePlusV = outerEnclosure 24
      (leaf5641Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5641RoundedFacts : LeafRoundedFacts 8
    leaf5641Certificate.logOnePlusV leaf5641InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5641InputLogOnePlusV_eq }

private noncomputable def leaf5641Inputs : Inputs :=
  inputsOfCaches globalInput sk133RoundedInputs
    chi269InputQChi innerPair273Input
    leaf5641InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5641LowerChecked :
    lowerCheck 24 leaf5641Box leaf5641Inputs = true := by
  rfl'

private theorem leaf5641CoversExact : CoversExact 8
    leaf5641Box leaf5641Certificate leaf5641InnerLog leaf5641Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk133RoundedFacts chi269RoundedFacts
    innerPair273RoundedFacts leaf5641RoundedFacts (by rfl)

private theorem leaf5641FlatSound : Sound leaf5641Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5641CertificateValid
    leaf5641InnerLogValid leaf5641CoversExact leaf5641LowerChecked

private noncomputable def leaf5642Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (29/64), chiHi := (59/128) }

private noncomputable def leaf5642Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435769/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356777984) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (637085409/536870912) }, upper := { exponent := 1, mantissa := (4939/4096) } }, logOuter := sk134LogOuterCertificate, logK := sk134LogKCertificate, logChi := chi269LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715500543/68713555968) } }, logDArg := sk134LogDArgCertificate }

private noncomputable def leaf5642InnerLog : WideLogData :=
  innerPair273Data

set_option maxRecDepth 1000000 in
private theorem leaf5642LocalValidity :
    LeafFacts leaf5642Box leaf5642Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5642Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356777984) }) = true
      norm_num [leaf5642Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5642CertificateValid :
    WideCertificateValid leaf5642Box leaf5642Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk134ValidityFacts chi269ValidityFacts
    leaf5642LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5642CoverageChecked :
    coverageCheck (innerAD leaf5642Box) leaf5642InnerLog = true := by
  rfl'

private theorem leaf5642InnerLogValid :
    leaf5642InnerLog.Valid 8 (innerAD leaf5642Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint78PositiveFacts.valid leaf5642CoverageChecked

private noncomputable def leaf5642InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907389/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5642InputLogOnePlusV_eq :
    leaf5642InputLogOnePlusV = outerEnclosure 24
      (leaf5642Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5642RoundedFacts : LeafRoundedFacts 8
    leaf5642Certificate.logOnePlusV leaf5642InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5642InputLogOnePlusV_eq }

private noncomputable def leaf5642Inputs : Inputs :=
  inputsOfCaches globalInput sk134RoundedInputs
    chi269InputQChi innerPair273Input
    leaf5642InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5642LowerChecked :
    lowerCheck 24 leaf5642Box leaf5642Inputs = true := by
  rfl'

private theorem leaf5642CoversExact : CoversExact 8
    leaf5642Box leaf5642Certificate leaf5642InnerLog leaf5642Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk134RoundedFacts chi269RoundedFacts
    innerPair273RoundedFacts leaf5642RoundedFacts (by rfl)

private theorem leaf5642FlatSound : Sound leaf5642Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5642CertificateValid
    leaf5642InnerLogValid leaf5642CoversExact leaf5642LowerChecked

private noncomputable def leaf5643Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (59/128), chiHi := (15/32) }

private noncomputable def leaf5643Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435769/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356758528) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (639575625/536870912) }, upper := { exponent := 1, mantissa := (2479/2048) } }, logOuter := sk133LogOuterCertificate, logK := sk133LogKCertificate, logChi := chi270LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715481087/68713517056) } }, logDArg := sk133LogDArgCertificate }

private noncomputable def leaf5643InnerLog : WideLogData :=
  innerPair278Data

set_option maxRecDepth 1000000 in
private theorem leaf5643LocalValidity :
    LeafFacts leaf5643Box leaf5643Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5643Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356758528) }) = true
      norm_num [leaf5643Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5643CertificateValid :
    WideCertificateValid leaf5643Box leaf5643Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk133ValidityFacts chi270ValidityFacts
    leaf5643LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5643CoverageChecked :
    coverageCheck (innerAD leaf5643Box) leaf5643InnerLog = true := by
  rfl'

private theorem leaf5643InnerLogValid :
    leaf5643InnerLog.Valid 8 (innerAD leaf5643Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint78PositiveFacts.valid leaf5643CoverageChecked

private noncomputable def leaf5643InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453695/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5643InputLogOnePlusV_eq :
    leaf5643InputLogOnePlusV = outerEnclosure 24
      (leaf5643Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5643RoundedFacts : LeafRoundedFacts 8
    leaf5643Certificate.logOnePlusV leaf5643InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5643InputLogOnePlusV_eq }

private noncomputable def leaf5643Inputs : Inputs :=
  inputsOfCaches globalInput sk133RoundedInputs
    chi270InputQChi innerPair278Input
    leaf5643InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5643LowerChecked :
    lowerCheck 24 leaf5643Box leaf5643Inputs = true := by
  rfl'

private theorem leaf5643CoversExact : CoversExact 8
    leaf5643Box leaf5643Certificate leaf5643InnerLog leaf5643Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk133RoundedFacts chi270RoundedFacts
    innerPair278RoundedFacts leaf5643RoundedFacts (by rfl)

private theorem leaf5643FlatSound : Sound leaf5643Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5643CertificateValid
    leaf5643InnerLogValid leaf5643CoversExact leaf5643LowerChecked

private noncomputable def leaf5644Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (59/128), chiHi := (15/32) }

private noncomputable def leaf5644Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435771/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356727808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (643442011/536870912) }, upper := { exponent := 1, mantissa := (1247/1024) } }, logOuter := sk134LogOuterCertificate, logK := sk134LogKCertificate, logChi := chi270LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715450367/68713455616) } }, logDArg := sk134LogDArgCertificate }

private noncomputable def leaf5644InnerLog : WideLogData :=
  innerPair278Data

set_option maxRecDepth 1000000 in
private theorem leaf5644LocalValidity :
    LeafFacts leaf5644Box leaf5644Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5644Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356727808) }) = true
      norm_num [leaf5644Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5644CertificateValid :
    WideCertificateValid leaf5644Box leaf5644Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk134ValidityFacts chi270ValidityFacts
    leaf5644LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5644CoverageChecked :
    coverageCheck (innerAD leaf5644Box) leaf5644InnerLog = true := by
  rfl'

private theorem leaf5644InnerLogValid :
    leaf5644InnerLog.Valid 8 (innerAD leaf5644Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint78PositiveFacts.valid leaf5644CoverageChecked

private noncomputable def leaf5644InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11357/16384) }

set_option maxRecDepth 1000000 in
private theorem leaf5644InputLogOnePlusV_eq :
    leaf5644InputLogOnePlusV = outerEnclosure 24
      (leaf5644Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5644RoundedFacts : LeafRoundedFacts 8
    leaf5644Certificate.logOnePlusV leaf5644InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5644InputLogOnePlusV_eq }

private noncomputable def leaf5644Inputs : Inputs :=
  inputsOfCaches globalInput sk134RoundedInputs
    chi270InputQChi innerPair278Input
    leaf5644InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5644LowerChecked :
    lowerCheck 24 leaf5644Box leaf5644Inputs = true := by
  rfl'

private theorem leaf5644CoversExact : CoversExact 8
    leaf5644Box leaf5644Certificate leaf5644InnerLog leaf5644Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk134RoundedFacts chi270RoundedFacts
    innerPair278RoundedFacts leaf5644RoundedFacts (by rfl)

private theorem leaf5644FlatSound : Sound leaf5644Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5644CertificateValid
    leaf5644InnerLogValid leaf5644CoversExact leaf5644LowerChecked

private noncomputable def leaf5645Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (29/64), chiHi := (59/128) }

private noncomputable def leaf5645Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435771/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356747776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (640886263/536870912) }, upper := { exponent := 1, mantissa := (9937/8192) } }, logOuter := sk135LogOuterCertificate, logK := sk135LogKCertificate, logChi := chi269LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715470335/68713495552) } }, logDArg := sk135LogDArgCertificate }

private noncomputable def leaf5645InnerLog : WideLogData :=
  innerPair278Data

set_option maxRecDepth 1000000 in
private theorem leaf5645LocalValidity :
    LeafFacts leaf5645Box leaf5645Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5645Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356747776) }) = true
      norm_num [leaf5645Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5645CertificateValid :
    WideCertificateValid leaf5645Box leaf5645Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk135ValidityFacts chi269ValidityFacts
    leaf5645LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5645CoverageChecked :
    coverageCheck (innerAD leaf5645Box) leaf5645InnerLog = true := by
  rfl'

private theorem leaf5645InnerLogValid :
    leaf5645InnerLog.Valid 8 (innerAD leaf5645Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint78PositiveFacts.valid leaf5645CoverageChecked

private noncomputable def leaf5645InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629563/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5645InputLogOnePlusV_eq :
    leaf5645InputLogOnePlusV = outerEnclosure 24
      (leaf5645Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5645RoundedFacts : LeafRoundedFacts 8
    leaf5645Certificate.logOnePlusV leaf5645InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5645InputLogOnePlusV_eq }

private noncomputable def leaf5645Inputs : Inputs :=
  inputsOfCaches globalInput sk135RoundedInputs
    chi269InputQChi innerPair278Input
    leaf5645InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5645LowerChecked :
    lowerCheck 24 leaf5645Box leaf5645Inputs = true := by
  rfl'

private theorem leaf5645CoversExact : CoversExact 8
    leaf5645Box leaf5645Certificate leaf5645InnerLog leaf5645Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk135RoundedFacts chi269RoundedFacts
    innerPair278RoundedFacts leaf5645RoundedFacts (by rfl)

private theorem leaf5645FlatSound : Sound leaf5645Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5645CertificateValid
    leaf5645InnerLogValid leaf5645CoversExact leaf5645LowerChecked

private noncomputable def leaf5646Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (29/64), chiHi := (59/128) }

private noncomputable def leaf5646Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435773/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356717568) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (644687117/536870912) }, upper := { exponent := 1, mantissa := (2499/2048) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi269LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715440127/68713435136) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf5646InnerLog : WideLogData :=
  innerPair279Data

set_option maxRecDepth 1000000 in
private theorem leaf5646LocalValidity :
    LeafFacts leaf5646Box leaf5646Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5646Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356717568) }) = true
      norm_num [leaf5646Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5646CertificateValid :
    WideCertificateValid leaf5646Box leaf5646Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi269ValidityFacts
    leaf5646LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5646CoverageChecked :
    coverageCheck (innerAD leaf5646Box) leaf5646InnerLog = true := by
  rfl'

private theorem leaf5646InnerLogValid :
    leaf5646InnerLog.Valid 8 (innerAD leaf5646Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint79PositiveFacts.valid leaf5646CoverageChecked

private noncomputable def leaf5646InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814785/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5646InputLogOnePlusV_eq :
    leaf5646InputLogOnePlusV = outerEnclosure 24
      (leaf5646Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5646RoundedFacts : LeafRoundedFacts 8
    leaf5646Certificate.logOnePlusV leaf5646InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5646InputLogOnePlusV_eq }

private noncomputable def leaf5646Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi269InputQChi innerPair279Input
    leaf5646InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5646LowerChecked :
    lowerCheck 24 leaf5646Box leaf5646Inputs = true := by
  rfl'

private theorem leaf5646CoversExact : CoversExact 8
    leaf5646Box leaf5646Certificate leaf5646InnerLog leaf5646Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi269RoundedFacts
    innerPair279RoundedFacts leaf5646RoundedFacts (by rfl)

private theorem leaf5646FlatSound : Sound leaf5646Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5646CertificateValid
    leaf5646InnerLogValid leaf5646CoversExact leaf5646LowerChecked

private noncomputable def leaf5647Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (59/128), chiHi := (15/32) }

private noncomputable def leaf5647Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435773/268435456) }, vSqrt := { lower := (65529/65536), upper := (4908388937/4908099584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (647308397/536870912) }, upper := { exponent := 1, mantissa := (2509/2048) } }, logOuter := sk135LogOuterCertificate, logK := sk135LogKCertificate, logChi := chi270LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9816488521/9816199168) } }, logDArg := sk135LogDArgCertificate }

private noncomputable def leaf5647InnerLog : WideLogData :=
  innerPair279Data

set_option maxRecDepth 1000000 in
private theorem leaf5647LocalValidity :
    LeafFacts leaf5647Box leaf5647Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5647Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4908388937/4908099584) }) = true
      norm_num [leaf5647Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5647CertificateValid :
    WideCertificateValid leaf5647Box leaf5647Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk135ValidityFacts chi270ValidityFacts
    leaf5647LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5647CoverageChecked :
    coverageCheck (innerAD leaf5647Box) leaf5647InnerLog = true := by
  rfl'

private theorem leaf5647InnerLogValid :
    leaf5647InnerLog.Valid 8 (innerAD leaf5647Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint79PositiveFacts.valid leaf5647CoverageChecked

private noncomputable def leaf5647InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629575/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5647InputLogOnePlusV_eq :
    leaf5647InputLogOnePlusV = outerEnclosure 24
      (leaf5647Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5647RoundedFacts : LeafRoundedFacts 8
    leaf5647Certificate.logOnePlusV leaf5647InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5647InputLogOnePlusV_eq }

private noncomputable def leaf5647Inputs : Inputs :=
  inputsOfCaches globalInput sk135RoundedInputs
    chi270InputQChi innerPair279Input
    leaf5647InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5647LowerChecked :
    lowerCheck 24 leaf5647Box leaf5647Inputs = true := by
  rfl'

private theorem leaf5647CoversExact : CoversExact 8
    leaf5647Box leaf5647Certificate leaf5647InnerLog leaf5647Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk135RoundedFacts chi270RoundedFacts
    innerPair279RoundedFacts leaf5647RoundedFacts (by rfl)

private theorem leaf5647FlatSound : Sound leaf5647Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5647CertificateValid
    leaf5647InnerLogValid leaf5647CoversExact leaf5647LowerChecked

private noncomputable def leaf5648Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (59/128), chiHi := (15/32) }

private noncomputable def leaf5648Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435775/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356666368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (651174783/536870912) }, upper := { exponent := 1, mantissa := (631/512) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi270LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715388927/68713332736) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf5648InnerLog : WideLogData :=
  innerPair279Data

set_option maxRecDepth 1000000 in
private theorem leaf5648LocalValidity :
    LeafFacts leaf5648Box leaf5648Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5648Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356666368) }) = true
      norm_num [leaf5648Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5648CertificateValid :
    WideCertificateValid leaf5648Box leaf5648Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi270ValidityFacts
    leaf5648LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5648CoverageChecked :
    coverageCheck (innerAD leaf5648Box) leaf5648InnerLog = true := by
  rfl'

private theorem leaf5648InnerLogValid :
    leaf5648InnerLog.Valid 8 (innerAD leaf5648Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint79PositiveFacts.valid leaf5648CoverageChecked

private noncomputable def leaf5648InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629583/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5648InputLogOnePlusV_eq :
    leaf5648InputLogOnePlusV = outerEnclosure 24
      (leaf5648Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5648RoundedFacts : LeafRoundedFacts 8
    leaf5648Certificate.logOnePlusV leaf5648InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5648InputLogOnePlusV_eq }

private noncomputable def leaf5648Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi270InputQChi innerPair279Input
    leaf5648InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5648LowerChecked :
    lowerCheck 24 leaf5648Box leaf5648Inputs = true := by
  rfl'

private theorem leaf5648CoversExact : CoversExact 8
    leaf5648Box leaf5648Certificate leaf5648InnerLog leaf5648Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi270RoundedFacts
    innerPair279RoundedFacts leaf5648RoundedFacts (by rfl)

private theorem leaf5648FlatSound : Sound leaf5648Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5648CertificateValid
    leaf5648InnerLogValid leaf5648CoversExact leaf5648LowerChecked

private noncomputable def leaf5649Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (15/32), chiHi := (61/128) }

private noncomputable def leaf5649Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435771/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356708864) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (645866695/536870912) }, upper := { exponent := 1, mantissa := (10013/8192) } }, logOuter := sk133LogOuterCertificate, logK := sk133LogKCertificate, logChi := chi271LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715431423/68713417728) } }, logDArg := sk133LogDArgCertificate }

private noncomputable def leaf5649InnerLog : WideLogData :=
  innerPair279Data

set_option maxRecDepth 1000000 in
private theorem leaf5649LocalValidity :
    LeafFacts leaf5649Box leaf5649Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5649Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356708864) }) = true
      norm_num [leaf5649Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5649CertificateValid :
    WideCertificateValid leaf5649Box leaf5649Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk133ValidityFacts chi271ValidityFacts
    leaf5649LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5649CoverageChecked :
    coverageCheck (innerAD leaf5649Box) leaf5649InnerLog = true := by
  rfl'

private theorem leaf5649InnerLogValid :
    leaf5649InnerLog.Valid 8 (innerAD leaf5649Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint79PositiveFacts.valid leaf5649CoverageChecked

private noncomputable def leaf5649InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907393/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5649InputLogOnePlusV_eq :
    leaf5649InputLogOnePlusV = outerEnclosure 24
      (leaf5649Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5649RoundedFacts : LeafRoundedFacts 8
    leaf5649Certificate.logOnePlusV leaf5649InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5649InputLogOnePlusV_eq }

private noncomputable def leaf5649Inputs : Inputs :=
  inputsOfCaches globalInput sk133RoundedInputs
    chi271InputQChi innerPair279Input
    leaf5649InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5649LowerChecked :
    lowerCheck 24 leaf5649Box leaf5649Inputs = true := by
  rfl'

private theorem leaf5649CoversExact : CoversExact 8
    leaf5649Box leaf5649Certificate leaf5649InnerLog leaf5649Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk133RoundedFacts chi271RoundedFacts
    innerPair279RoundedFacts leaf5649RoundedFacts (by rfl)

private theorem leaf5649FlatSound : Sound leaf5649Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5649CertificateValid
    leaf5649InnerLogValid leaf5649CoversExact leaf5649LowerChecked

private noncomputable def leaf5650Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (15/32), chiHi := (61/128) }

private noncomputable def leaf5650Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435773/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356677632) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (649798613/536870912) }, upper := { exponent := 1, mantissa := (5037/4096) } }, logOuter := sk134LogOuterCertificate, logK := sk134LogKCertificate, logChi := chi271LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715400191/68713355264) } }, logDArg := sk134LogDArgCertificate }

private noncomputable def leaf5650InnerLog : WideLogData :=
  innerPair279Data

set_option maxRecDepth 1000000 in
private theorem leaf5650LocalValidity :
    LeafFacts leaf5650Box leaf5650Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5650Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356677632) }) = true
      norm_num [leaf5650Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5650CertificateValid :
    WideCertificateValid leaf5650Box leaf5650Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk134ValidityFacts chi271ValidityFacts
    leaf5650LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5650CoverageChecked :
    coverageCheck (innerAD leaf5650Box) leaf5650InnerLog = true := by
  rfl'

private theorem leaf5650InnerLogValid :
    leaf5650InnerLog.Valid 8 (innerAD leaf5650Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint79PositiveFacts.valid leaf5650CoverageChecked

private noncomputable def leaf5650InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907395/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5650InputLogOnePlusV_eq :
    leaf5650InputLogOnePlusV = outerEnclosure 24
      (leaf5650Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5650RoundedFacts : LeafRoundedFacts 8
    leaf5650Certificate.logOnePlusV leaf5650InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5650InputLogOnePlusV_eq }

private noncomputable def leaf5650Inputs : Inputs :=
  inputsOfCaches globalInput sk134RoundedInputs
    chi271InputQChi innerPair279Input
    leaf5650InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5650LowerChecked :
    lowerCheck 24 leaf5650Box leaf5650Inputs = true := by
  rfl'

private theorem leaf5650CoversExact : CoversExact 8
    leaf5650Box leaf5650Certificate leaf5650InnerLog leaf5650Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk134RoundedFacts chi271RoundedFacts
    innerPair279RoundedFacts leaf5650RoundedFacts (by rfl)

private theorem leaf5650FlatSound : Sound leaf5650Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5650CertificateValid
    leaf5650InnerLogValid leaf5650CoversExact leaf5650LowerChecked

private noncomputable def leaf5651Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (61/128), chiHi := (31/64) }

private noncomputable def leaf5651Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435773/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356659200) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (652157765/536870912) }, upper := { exponent := 1, mantissa := (5055/4096) } }, logOuter := sk133LogOuterCertificate, logK := sk133LogKCertificate, logChi := chi272LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715381759/68713318400) } }, logDArg := sk133LogDArgCertificate }

private noncomputable def leaf5651InnerLog : WideLogData :=
  innerPair279Data

set_option maxRecDepth 1000000 in
private theorem leaf5651LocalValidity :
    LeafFacts leaf5651Box leaf5651Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5651Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356659200) }) = true
      norm_num [leaf5651Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5651CertificateValid :
    WideCertificateValid leaf5651Box leaf5651Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk133ValidityFacts chi272ValidityFacts
    leaf5651LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5651CoverageChecked :
    coverageCheck (innerAD leaf5651Box) leaf5651InnerLog = true := by
  rfl'

private theorem leaf5651InnerLogValid :
    leaf5651InnerLog.Valid 8 (innerAD leaf5651Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint79PositiveFacts.valid leaf5651CoverageChecked

private noncomputable def leaf5651InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629585/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5651InputLogOnePlusV_eq :
    leaf5651InputLogOnePlusV = outerEnclosure 24
      (leaf5651Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5651RoundedFacts : LeafRoundedFacts 8
    leaf5651Certificate.logOnePlusV leaf5651InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5651InputLogOnePlusV_eq }

private noncomputable def leaf5651Inputs : Inputs :=
  inputsOfCaches globalInput sk133RoundedInputs
    chi272InputQChi innerPair279Input
    leaf5651InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5651LowerChecked :
    lowerCheck 24 leaf5651Box leaf5651Inputs = true := by
  rfl'

private theorem leaf5651CoversExact : CoversExact 8
    leaf5651Box leaf5651Certificate leaf5651InnerLog leaf5651Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk133RoundedFacts chi272RoundedFacts
    innerPair279RoundedFacts leaf5651RoundedFacts (by rfl)

private theorem leaf5651FlatSound : Sound leaf5651Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5651CertificateValid
    leaf5651InnerLogValid leaf5651CoversExact leaf5651LowerChecked

private noncomputable def leaf5652Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (61/128), chiHi := (31/64) }

private noncomputable def leaf5652Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435775/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356627456) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (656155215/536870912) }, upper := { exponent := 1, mantissa := (2543/2048) } }, logOuter := sk134LogOuterCertificate, logK := sk134LogKCertificate, logChi := chi272LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715350015/68713254912) } }, logDArg := sk134LogDArgCertificate }

private noncomputable def leaf5652InnerLog : WideLogData :=
  innerPair285Data

set_option maxRecDepth 1000000 in
private theorem leaf5652LocalValidity :
    LeafFacts leaf5652Box leaf5652Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5652Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356627456) }) = true
      norm_num [leaf5652Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5652CertificateValid :
    WideCertificateValid leaf5652Box leaf5652Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk134ValidityFacts chi272ValidityFacts
    leaf5652LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5652CoverageChecked :
    coverageCheck (innerAD leaf5652Box) leaf5652InnerLog = true := by
  rfl'

private theorem leaf5652InnerLogValid :
    leaf5652InnerLog.Valid 8 (innerAD leaf5652Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint79PositiveFacts.valid leaf5652CoverageChecked

private noncomputable def leaf5652InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453699/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5652InputLogOnePlusV_eq :
    leaf5652InputLogOnePlusV = outerEnclosure 24
      (leaf5652Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5652RoundedFacts : LeafRoundedFacts 8
    leaf5652Certificate.logOnePlusV leaf5652InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5652InputLogOnePlusV_eq }

private noncomputable def leaf5652Inputs : Inputs :=
  inputsOfCaches globalInput sk134RoundedInputs
    chi272InputQChi innerPair285Input
    leaf5652InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5652LowerChecked :
    lowerCheck 24 leaf5652Box leaf5652Inputs = true := by
  rfl'

private theorem leaf5652CoversExact : CoversExact 8
    leaf5652Box leaf5652Certificate leaf5652InnerLog leaf5652Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk134RoundedFacts chi272RoundedFacts
    innerPair285RoundedFacts leaf5652RoundedFacts (by rfl)

private theorem leaf5652FlatSound : Sound leaf5652Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5652CertificateValid
    leaf5652InnerLogValid leaf5652CoversExact leaf5652LowerChecked

private noncomputable def leaf5653Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (15/32), chiHi := (61/128) }

private noncomputable def leaf5653Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435775/268435456) }, vSqrt := { lower := (65529/65536), upper := (2021101327/2020979200) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (653730531/536870912) }, upper := { exponent := 1, mantissa := (10135/8192) } }, logOuter := sk135LogOuterCertificate, logK := sk135LogKCertificate, logChi := chi271LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (4042080527/4041958400) } }, logDArg := sk135LogDArgCertificate }

private noncomputable def leaf5653InnerLog : WideLogData :=
  innerPair279Data

set_option maxRecDepth 1000000 in
private theorem leaf5653LocalValidity :
    LeafFacts leaf5653Box leaf5653Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5653Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (2021101327/2020979200) }) = true
      norm_num [leaf5653Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5653CertificateValid :
    WideCertificateValid leaf5653Box leaf5653Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk135ValidityFacts chi271ValidityFacts
    leaf5653LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5653CoverageChecked :
    coverageCheck (innerAD leaf5653Box) leaf5653InnerLog = true := by
  rfl'

private theorem leaf5653InnerLogValid :
    leaf5653InnerLog.Valid 8 (innerAD leaf5653Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint79PositiveFacts.valid leaf5653CoverageChecked

private noncomputable def leaf5653InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907397/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5653InputLogOnePlusV_eq :
    leaf5653InputLogOnePlusV = outerEnclosure 24
      (leaf5653Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5653RoundedFacts : LeafRoundedFacts 8
    leaf5653Certificate.logOnePlusV leaf5653InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5653InputLogOnePlusV_eq }

private noncomputable def leaf5653Inputs : Inputs :=
  inputsOfCaches globalInput sk135RoundedInputs
    chi271InputQChi innerPair279Input
    leaf5653InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5653LowerChecked :
    lowerCheck 24 leaf5653Box leaf5653Inputs = true := by
  rfl'

private theorem leaf5653CoversExact : CoversExact 8
    leaf5653Box leaf5653Certificate leaf5653InnerLog leaf5653Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk135RoundedFacts chi271RoundedFacts
    innerPair279RoundedFacts leaf5653RoundedFacts (by rfl)

private theorem leaf5653FlatSound : Sound leaf5653Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5653CertificateValid
    leaf5653InnerLogValid leaf5653CoversExact leaf5653LowerChecked

private noncomputable def leaf5654Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (15/32), chiHi := (61/128) }

private noncomputable def leaf5654Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435777/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68713230336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (657662449/536870912) }, upper := { exponent := 1, mantissa := (2549/2048) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi271LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429626877/137426460672) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf5654InnerLog : WideLogData :=
  innerPair285Data

set_option maxRecDepth 1000000 in
private theorem leaf5654LocalValidity :
    LeafFacts leaf5654Box leaf5654Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5654Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68713230336) }) = true
      norm_num [leaf5654Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5654CertificateValid :
    WideCertificateValid leaf5654Box leaf5654Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi271ValidityFacts
    leaf5654LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5654CoverageChecked :
    coverageCheck (innerAD leaf5654Box) leaf5654InnerLog = true := by
  rfl'

private theorem leaf5654InnerLogValid :
    leaf5654InnerLog.Valid 8 (innerAD leaf5654Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint79PositiveFacts.valid leaf5654CoverageChecked

private noncomputable def leaf5654InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629467/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5654InputLogOnePlusV_eq :
    leaf5654InputLogOnePlusV = outerEnclosure 24
      (leaf5654Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5654RoundedFacts : LeafRoundedFacts 8
    leaf5654Certificate.logOnePlusV leaf5654InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5654InputLogOnePlusV_eq }

private noncomputable def leaf5654Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi271InputQChi innerPair285Input
    leaf5654InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5654LowerChecked :
    lowerCheck 24 leaf5654Box leaf5654Inputs = true := by
  rfl'

private theorem leaf5654CoversExact : CoversExact 8
    leaf5654Box leaf5654Certificate leaf5654InnerLog leaf5654Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi271RoundedFacts
    innerPair285RoundedFacts leaf5654RoundedFacts (by rfl)

private theorem leaf5654FlatSound : Sound leaf5654Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5654CertificateValid
    leaf5654InnerLogValid leaf5654CoversExact leaf5654LowerChecked

private noncomputable def leaf5655Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (61/128), chiHi := (31/64) }

private noncomputable def leaf5655Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435777/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68713191424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (660152665/536870912) }, upper := { exponent := 1, mantissa := (5117/4096) } }, logOuter := sk135LogOuterCertificate, logK := sk135LogKCertificate, logChi := chi272LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429587965/137426382848) } }, logDArg := sk135LogDArgCertificate }

private noncomputable def leaf5655InnerLog : WideLogData :=
  innerPair285Data

set_option maxRecDepth 1000000 in
private theorem leaf5655LocalValidity :
    LeafFacts leaf5655Box leaf5655Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5655Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68713191424) }) = true
      norm_num [leaf5655Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5655CertificateValid :
    WideCertificateValid leaf5655Box leaf5655Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk135ValidityFacts chi272ValidityFacts
    leaf5655LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5655CoverageChecked :
    coverageCheck (innerAD leaf5655Box) leaf5655InnerLog = true := by
  rfl'

private theorem leaf5655InnerLogValid :
    leaf5655InnerLog.Valid 8 (innerAD leaf5655Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint79PositiveFacts.valid leaf5655CoverageChecked

private noncomputable def leaf5655InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (363421/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf5655InputLogOnePlusV_eq :
    leaf5655InputLogOnePlusV = outerEnclosure 24
      (leaf5655Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5655RoundedFacts : LeafRoundedFacts 8
    leaf5655Certificate.logOnePlusV leaf5655InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5655InputLogOnePlusV_eq }

private noncomputable def leaf5655Inputs : Inputs :=
  inputsOfCaches globalInput sk135RoundedInputs
    chi272InputQChi innerPair285Input
    leaf5655InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5655LowerChecked :
    lowerCheck 24 leaf5655Box leaf5655Inputs = true := by
  rfl'

private theorem leaf5655CoversExact : CoversExact 8
    leaf5655Box leaf5655Certificate leaf5655InnerLog leaf5655Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk135RoundedFacts chi272RoundedFacts
    innerPair285RoundedFacts leaf5655RoundedFacts (by rfl)

private theorem leaf5655FlatSound : Sound leaf5655Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5655CertificateValid
    leaf5655InnerLogValid leaf5655CoversExact leaf5655LowerChecked

private noncomputable def leaf5656Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (61/128), chiHi := (31/64) }

private noncomputable def leaf5656Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435779/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68713127936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (664150115/536870912) }, upper := { exponent := 1, mantissa := (1287/1024) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi272LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429524477/137426255872) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf5656InnerLog : WideLogData :=
  innerPair286Data

set_option maxRecDepth 1000000 in
private theorem leaf5656LocalValidity :
    LeafFacts leaf5656Box leaf5656Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5656Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68713127936) }) = true
      norm_num [leaf5656Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5656CertificateValid :
    WideCertificateValid leaf5656Box leaf5656Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi272ValidityFacts
    leaf5656LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5656CoverageChecked :
    coverageCheck (innerAD leaf5656Box) leaf5656InnerLog = true := by
  rfl'

private theorem leaf5656InnerLogValid :
    leaf5656InnerLog.Valid 8 (innerAD leaf5656Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint90PositiveFacts.valid leaf5656CoverageChecked

private noncomputable def leaf5656InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453685/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5656InputLogOnePlusV_eq :
    leaf5656InputLogOnePlusV = outerEnclosure 24
      (leaf5656Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5656RoundedFacts : LeafRoundedFacts 8
    leaf5656Certificate.logOnePlusV leaf5656InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5656InputLogOnePlusV_eq }

private noncomputable def leaf5656Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi272InputQChi innerPair286Input
    leaf5656InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5656LowerChecked :
    lowerCheck 24 leaf5656Box leaf5656Inputs = true := by
  rfl'

private theorem leaf5656CoversExact : CoversExact 8
    leaf5656Box leaf5656Certificate leaf5656InnerLog leaf5656Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi272RoundedFacts
    innerPair286RoundedFacts leaf5656RoundedFacts (by rfl)

private theorem leaf5656FlatSound : Sound leaf5656Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5656CertificateValid
    leaf5656InnerLogValid leaf5656CoversExact leaf5656LowerChecked

private noncomputable def leaf5657Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (31/64), chiHi := (63/128) }

private noncomputable def leaf5657Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435775/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68713219072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (658448835/536870912) }, upper := { exponent := 1, mantissa := (10207/8192) } }, logOuter := sk133LogOuterCertificate, logK := sk133LogKCertificate, logChi := chi273LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429615613/137426438144) } }, logDArg := sk133LogDArgCertificate }

private noncomputable def leaf5657InnerLog : WideLogData :=
  innerPair285Data

set_option maxRecDepth 1000000 in
private theorem leaf5657LocalValidity :
    LeafFacts leaf5657Box leaf5657Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5657Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68713219072) }) = true
      norm_num [leaf5657Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5657CertificateValid :
    WideCertificateValid leaf5657Box leaf5657Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk133ValidityFacts chi273ValidityFacts
    leaf5657LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5657CoverageChecked :
    coverageCheck (innerAD leaf5657Box) leaf5657InnerLog = true := by
  rfl'

private theorem leaf5657InnerLogValid :
    leaf5657InnerLog.Valid 8 (innerAD leaf5657Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint79PositiveFacts.valid leaf5657CoverageChecked

private noncomputable def leaf5657InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629469/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5657InputLogOnePlusV_eq :
    leaf5657InputLogOnePlusV = outerEnclosure 24
      (leaf5657Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5657RoundedFacts : LeafRoundedFacts 8
    leaf5657Certificate.logOnePlusV leaf5657InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5657InputLogOnePlusV_eq }

private noncomputable def leaf5657Inputs : Inputs :=
  inputsOfCaches globalInput sk133RoundedInputs
    chi273InputQChi innerPair285Input
    leaf5657InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5657LowerChecked :
    lowerCheck 24 leaf5657Box leaf5657Inputs = true := by
  rfl'

private theorem leaf5657CoversExact : CoversExact 8
    leaf5657Box leaf5657Certificate leaf5657InnerLog leaf5657Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk133RoundedFacts chi273RoundedFacts
    innerPair285RoundedFacts leaf5657RoundedFacts (by rfl)

private theorem leaf5657FlatSound : Sound leaf5657Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5657CertificateValid
    leaf5657InnerLogValid leaf5657CoversExact leaf5657LowerChecked

private noncomputable def leaf5658Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (31/64), chiHi := (63/128) }

private noncomputable def leaf5658Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435777/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68713154560) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (662511817/536870912) }, upper := { exponent := 1, mantissa := (5135/4096) } }, logOuter := sk134LogOuterCertificate, logK := sk134LogKCertificate, logChi := chi273LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429551101/137426309120) } }, logDArg := sk134LogDArgCertificate }

private noncomputable def leaf5658InnerLog : WideLogData :=
  innerPair286Data

set_option maxRecDepth 1000000 in
private theorem leaf5658LocalValidity :
    LeafFacts leaf5658Box leaf5658Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5658Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68713154560) }) = true
      norm_num [leaf5658Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5658CertificateValid :
    WideCertificateValid leaf5658Box leaf5658Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk134ValidityFacts chi273ValidityFacts
    leaf5658LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5658CoverageChecked :
    coverageCheck (innerAD leaf5658Box) leaf5658InnerLog = true := by
  rfl'

private theorem leaf5658InnerLogValid :
    leaf5658InnerLog.Valid 8 (innerAD leaf5658Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint90PositiveFacts.valid leaf5658CoverageChecked

private noncomputable def leaf5658InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629477/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5658InputLogOnePlusV_eq :
    leaf5658InputLogOnePlusV = outerEnclosure 24
      (leaf5658Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5658RoundedFacts : LeafRoundedFacts 8
    leaf5658Certificate.logOnePlusV leaf5658InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5658InputLogOnePlusV_eq }

private noncomputable def leaf5658Inputs : Inputs :=
  inputsOfCaches globalInput sk134RoundedInputs
    chi273InputQChi innerPair286Input
    leaf5658InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5658LowerChecked :
    lowerCheck 24 leaf5658Box leaf5658Inputs = true := by
  rfl'

private theorem leaf5658CoversExact : CoversExact 8
    leaf5658Box leaf5658Certificate leaf5658InnerLog leaf5658Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk134RoundedFacts chi273RoundedFacts
    innerPair286RoundedFacts leaf5658RoundedFacts (by rfl)

private theorem leaf5658FlatSound : Sound leaf5658Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5658CertificateValid
    leaf5658InnerLogValid leaf5658CoversExact leaf5658LowerChecked

private noncomputable def leaf5659Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (63/128), chiHi := (1/2) }

private noncomputable def leaf5659Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435777/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68713119744) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (664739905/536870912) }, upper := { exponent := 1, mantissa := (161/128) } }, logOuter := sk133LogOuterCertificate, logK := sk133LogKCertificate, logChi := chi274LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429516285/137426239488) } }, logDArg := sk133LogDArgCertificate }

private noncomputable def leaf5659InnerLog : WideLogData :=
  innerPair286Data

set_option maxRecDepth 1000000 in
private theorem leaf5659LocalValidity :
    LeafFacts leaf5659Box leaf5659Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5659Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68713119744) }) = true
      norm_num [leaf5659Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5659CertificateValid :
    WideCertificateValid leaf5659Box leaf5659Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk133ValidityFacts chi274ValidityFacts
    leaf5659LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5659CoverageChecked :
    coverageCheck (innerAD leaf5659Box) leaf5659InnerLog = true := by
  rfl'

private theorem leaf5659InnerLogValid :
    leaf5659InnerLog.Valid 8 (innerAD leaf5659Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint90PositiveFacts.valid leaf5659CoverageChecked

private noncomputable def leaf5659InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629481/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5659InputLogOnePlusV_eq :
    leaf5659InputLogOnePlusV = outerEnclosure 24
      (leaf5659Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5659RoundedFacts : LeafRoundedFacts 8
    leaf5659Certificate.logOnePlusV leaf5659InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5659InputLogOnePlusV_eq }

private noncomputable def leaf5659Inputs : Inputs :=
  inputsOfCaches globalInput sk133RoundedInputs
    chi274InputQChi innerPair286Input
    leaf5659InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5659LowerChecked :
    lowerCheck 24 leaf5659Box leaf5659Inputs = true := by
  rfl'

private theorem leaf5659CoversExact : CoversExact 8
    leaf5659Box leaf5659Certificate leaf5659InnerLog leaf5659Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk133RoundedFacts chi274RoundedFacts
    innerPair286RoundedFacts leaf5659RoundedFacts (by rfl)

private theorem leaf5659FlatSound : Sound leaf5659Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5659CertificateValid
    leaf5659InnerLogValid leaf5659CoversExact leaf5659LowerChecked

private noncomputable def leaf5660Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (63/128), chiHi := (1/2) }

private noncomputable def leaf5660Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435779/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68713054208) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (668868419/536870912) }, upper := { exponent := 1, mantissa := (81/64) } }, logOuter := sk134LogOuterCertificate, logK := sk134LogKCertificate, logChi := chi274LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429450749/137426108416) } }, logDArg := sk134LogDArgCertificate }

private noncomputable def leaf5660InnerLog : WideLogData :=
  innerPair286Data

set_option maxRecDepth 1000000 in
private theorem leaf5660LocalValidity :
    LeafFacts leaf5660Box leaf5660Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5660Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68713054208) }) = true
      norm_num [leaf5660Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5660CertificateValid :
    WideCertificateValid leaf5660Box leaf5660Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk134ValidityFacts chi274ValidityFacts
    leaf5660LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5660CoverageChecked :
    coverageCheck (innerAD leaf5660Box) leaf5660InnerLog = true := by
  rfl'

private theorem leaf5660InnerLogValid :
    leaf5660InnerLog.Valid 8 (innerAD leaf5660Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint90PositiveFacts.valid leaf5660CoverageChecked

private noncomputable def leaf5660InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629489/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5660InputLogOnePlusV_eq :
    leaf5660InputLogOnePlusV = outerEnclosure 24
      (leaf5660Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5660RoundedFacts : LeafRoundedFacts 8
    leaf5660Certificate.logOnePlusV leaf5660InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5660InputLogOnePlusV_eq }

private noncomputable def leaf5660Inputs : Inputs :=
  inputsOfCaches globalInput sk134RoundedInputs
    chi274InputQChi innerPair286Input
    leaf5660InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5660LowerChecked :
    lowerCheck 24 leaf5660Box leaf5660Inputs = true := by
  rfl'

private theorem leaf5660CoversExact : CoversExact 8
    leaf5660Box leaf5660Certificate leaf5660InnerLog leaf5660Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk134RoundedFacts chi274RoundedFacts
    innerPair286RoundedFacts leaf5660RoundedFacts (by rfl)

private theorem leaf5660FlatSound : Sound leaf5660Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5660CertificateValid
    leaf5660InnerLogValid leaf5660CoversExact leaf5660LowerChecked

private noncomputable def leaf5661Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (31/64), chiHi := (63/128) }

private noncomputable def leaf5661Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435779/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68713090048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (666574799/536870912) }, upper := { exponent := 1, mantissa := (10333/8192) } }, logOuter := sk135LogOuterCertificate, logK := sk135LogKCertificate, logChi := chi273LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429486589/137426180096) } }, logDArg := sk135LogDArgCertificate }

private noncomputable def leaf5661InnerLog : WideLogData :=
  innerPair286Data

set_option maxRecDepth 1000000 in
private theorem leaf5661LocalValidity :
    LeafFacts leaf5661Box leaf5661Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5661Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68713090048) }) = true
      norm_num [leaf5661Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5661CertificateValid :
    WideCertificateValid leaf5661Box leaf5661Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk135ValidityFacts chi273ValidityFacts
    leaf5661LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5661CoverageChecked :
    coverageCheck (innerAD leaf5661Box) leaf5661InnerLog = true := by
  rfl'

private theorem leaf5661InnerLogValid :
    leaf5661InnerLog.Valid 8 (innerAD leaf5661Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint90PositiveFacts.valid leaf5661CoverageChecked

private noncomputable def leaf5661InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907371/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5661InputLogOnePlusV_eq :
    leaf5661InputLogOnePlusV = outerEnclosure 24
      (leaf5661Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5661RoundedFacts : LeafRoundedFacts 8
    leaf5661Certificate.logOnePlusV leaf5661InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5661InputLogOnePlusV_eq }

private noncomputable def leaf5661Inputs : Inputs :=
  inputsOfCaches globalInput sk135RoundedInputs
    chi273InputQChi innerPair286Input
    leaf5661InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5661LowerChecked :
    lowerCheck 24 leaf5661Box leaf5661Inputs = true := by
  rfl'

private theorem leaf5661CoversExact : CoversExact 8
    leaf5661Box leaf5661Certificate leaf5661InnerLog leaf5661Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk135RoundedFacts chi273RoundedFacts
    innerPair286RoundedFacts leaf5661RoundedFacts (by rfl)

private theorem leaf5661FlatSound : Sound leaf5661Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5661CertificateValid
    leaf5661InnerLogValid leaf5661CoversExact leaf5661LowerChecked

private noncomputable def leaf5662Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (31/64), chiHi := (63/128) }

private noncomputable def leaf5662Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435781/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68713025536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (670637781/536870912) }, upper := { exponent := 1, mantissa := (2599/2048) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi273LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429422077/137426051072) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf5662InnerLog : WideLogData :=
  innerPair286Data

set_option maxRecDepth 1000000 in
private theorem leaf5662LocalValidity :
    LeafFacts leaf5662Box leaf5662Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5662Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68713025536) }) = true
      norm_num [leaf5662Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5662CertificateValid :
    WideCertificateValid leaf5662Box leaf5662Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi273ValidityFacts
    leaf5662LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5662CoverageChecked :
    coverageCheck (innerAD leaf5662Box) leaf5662InnerLog = true := by
  rfl'

private theorem leaf5662InnerLogValid :
    leaf5662InnerLog.Valid 8 (innerAD leaf5662Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint90PositiveFacts.valid leaf5662CoverageChecked

private noncomputable def leaf5662InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907373/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5662InputLogOnePlusV_eq :
    leaf5662InputLogOnePlusV = outerEnclosure 24
      (leaf5662Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5662RoundedFacts : LeafRoundedFacts 8
    leaf5662Certificate.logOnePlusV leaf5662InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5662InputLogOnePlusV_eq }

private noncomputable def leaf5662Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi273InputQChi innerPair286Input
    leaf5662InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5662LowerChecked :
    lowerCheck 24 leaf5662Box leaf5662Inputs = true := by
  rfl'

private theorem leaf5662CoversExact : CoversExact 8
    leaf5662Box leaf5662Certificate leaf5662InnerLog leaf5662Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi273RoundedFacts
    innerPair286RoundedFacts leaf5662RoundedFacts (by rfl)

private theorem leaf5662FlatSound : Sound leaf5662Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5662CertificateValid
    leaf5662InnerLogValid leaf5662CoversExact leaf5662LowerChecked

private noncomputable def leaf5663Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (63/128), chiHi := (1/2) }

private noncomputable def leaf5663Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435781/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712988672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (672996933/536870912) }, upper := { exponent := 1, mantissa := (163/128) } }, logOuter := sk135LogOuterCertificate, logK := sk135LogKCertificate, logChi := chi274LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429385213/137425977344) } }, logDArg := sk135LogDArgCertificate }

private noncomputable def leaf5663InnerLog : WideLogData :=
  innerPair293Data

set_option maxRecDepth 1000000 in
private theorem leaf5663LocalValidity :
    LeafFacts leaf5663Box leaf5663Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5663Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712988672) }) = true
      norm_num [leaf5663Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5663CertificateValid :
    WideCertificateValid leaf5663Box leaf5663Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk135ValidityFacts chi274ValidityFacts
    leaf5663LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5663CoverageChecked :
    coverageCheck (innerAD leaf5663Box) leaf5663InnerLog = true := by
  rfl'

private theorem leaf5663InnerLogValid :
    leaf5663InnerLog.Valid 8 (innerAD leaf5663Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint90PositiveFacts.valid leaf5663CoverageChecked

private noncomputable def leaf5663InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629497/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5663InputLogOnePlusV_eq :
    leaf5663InputLogOnePlusV = outerEnclosure 24
      (leaf5663Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5663RoundedFacts : LeafRoundedFacts 8
    leaf5663Certificate.logOnePlusV leaf5663InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5663InputLogOnePlusV_eq }

private noncomputable def leaf5663Inputs : Inputs :=
  inputsOfCaches globalInput sk135RoundedInputs
    chi274InputQChi innerPair293Input
    leaf5663InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5663LowerChecked :
    lowerCheck 24 leaf5663Box leaf5663Inputs = true := by
  rfl'

private theorem leaf5663CoversExact : CoversExact 8
    leaf5663Box leaf5663Certificate leaf5663InnerLog leaf5663Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk135RoundedFacts chi274RoundedFacts
    innerPair293RoundedFacts leaf5663RoundedFacts (by rfl)

private theorem leaf5663FlatSound : Sound leaf5663Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5663CertificateValid
    leaf5663InnerLogValid leaf5663CoversExact leaf5663LowerChecked

private noncomputable def leaf5664Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (63/128), chiHi := (1/2) }

private noncomputable def leaf5664Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435783/268435456) }, vSqrt := { lower := (65529/65536), upper := (5285876657/5285609472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (677125447/536870912) }, upper := { exponent := 1, mantissa := (41/32) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi274LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (10571486129/10571218944) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf5664InnerLog : WideLogData :=
  innerPair293Data

set_option maxRecDepth 1000000 in
private theorem leaf5664LocalValidity :
    LeafFacts leaf5664Box leaf5664Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5664Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (5285876657/5285609472) }) = true
      norm_num [leaf5664Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5664CertificateValid :
    WideCertificateValid leaf5664Box leaf5664Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi274ValidityFacts
    leaf5664LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5664CoverageChecked :
    coverageCheck (innerAD leaf5664Box) leaf5664InnerLog = true := by
  rfl'

private theorem leaf5664InnerLogValid :
    leaf5664InnerLog.Valid 8 (innerAD leaf5664Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint90PositiveFacts.valid leaf5664CoverageChecked

private noncomputable def leaf5664InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629505/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5664InputLogOnePlusV_eq :
    leaf5664InputLogOnePlusV = outerEnclosure 24
      (leaf5664Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5664RoundedFacts : LeafRoundedFacts 8
    leaf5664Certificate.logOnePlusV leaf5664InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5664InputLogOnePlusV_eq }

private noncomputable def leaf5664Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi274InputQChi innerPair293Input
    leaf5664InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5664LowerChecked :
    lowerCheck 24 leaf5664Box leaf5664Inputs = true := by
  rfl'

private theorem leaf5664CoversExact : CoversExact 8
    leaf5664Box leaf5664Certificate leaf5664InnerLog leaf5664Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi274RoundedFacts
    innerPair293RoundedFacts leaf5664RoundedFacts (by rfl)

private theorem leaf5664FlatSound : Sound leaf5664Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5664CertificateValid
    leaf5664InnerLogValid leaf5664CoversExact leaf5664LowerChecked

private noncomputable def leaf5665Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (7/16), chiHi := (57/128) }

private noncomputable def leaf5665Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435771/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356790784) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (635381575/536870912) }, upper := { exponent := 1, mantissa := (9853/8192) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi267LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715513343/68713581568) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf5665InnerLog : WideLogData :=
  innerPair273Data

set_option maxRecDepth 1000000 in
private theorem leaf5665LocalValidity :
    LeafFacts leaf5665Box leaf5665Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5665Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356790784) }) = true
      norm_num [leaf5665Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5665CertificateValid :
    WideCertificateValid leaf5665Box leaf5665Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi267ValidityFacts
    leaf5665LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5665CoverageChecked :
    coverageCheck (innerAD leaf5665Box) leaf5665InnerLog = true := by
  rfl'

private theorem leaf5665InnerLogValid :
    leaf5665InnerLog.Valid 8 (innerAD leaf5665Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint78PositiveFacts.valid leaf5665CoverageChecked

private noncomputable def leaf5665InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (726847/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf5665InputLogOnePlusV_eq :
    leaf5665InputLogOnePlusV = outerEnclosure 24
      (leaf5665Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5665RoundedFacts : LeafRoundedFacts 8
    leaf5665Certificate.logOnePlusV leaf5665InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5665InputLogOnePlusV_eq }

private noncomputable def leaf5665Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi267InputQChi innerPair273Input
    leaf5665InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5665LowerChecked :
    lowerCheck 24 leaf5665Box leaf5665Inputs = true := by
  rfl'

private theorem leaf5665CoversExact : CoversExact 8
    leaf5665Box leaf5665Certificate leaf5665InnerLog leaf5665Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi267RoundedFacts
    innerPair273RoundedFacts leaf5665RoundedFacts (by rfl)

private theorem leaf5665FlatSound : Sound leaf5665Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5665CertificateValid
    leaf5665InnerLogValid leaf5665CoversExact leaf5665LowerChecked

private noncomputable def leaf5666Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (7/16), chiHi := (57/128) }

private noncomputable def leaf5666Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435773/268435456) }, vSqrt := { lower := (65529/65536), upper := (4908388937/4908108800) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (639051365/536870912) }, upper := { exponent := 1, mantissa := (4955/4096) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi267LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9816497737/9816217600) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf5666InnerLog : WideLogData :=
  innerPair278Data

set_option maxRecDepth 1000000 in
private theorem leaf5666LocalValidity :
    LeafFacts leaf5666Box leaf5666Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5666Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4908388937/4908108800) }) = true
      norm_num [leaf5666Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5666CertificateValid :
    WideCertificateValid leaf5666Box leaf5666Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi267ValidityFacts
    leaf5666LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5666CoverageChecked :
    coverageCheck (innerAD leaf5666Box) leaf5666InnerLog = true := by
  rfl'

private theorem leaf5666InnerLogValid :
    leaf5666InnerLog.Valid 8 (innerAD leaf5666Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint78PositiveFacts.valid leaf5666CoverageChecked

private noncomputable def leaf5666InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453695/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5666InputLogOnePlusV_eq :
    leaf5666InputLogOnePlusV = outerEnclosure 24
      (leaf5666Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5666RoundedFacts : LeafRoundedFacts 8
    leaf5666Certificate.logOnePlusV leaf5666InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5666InputLogOnePlusV_eq }

private noncomputable def leaf5666Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi267InputQChi innerPair278Input
    leaf5666InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5666LowerChecked :
    lowerCheck 24 leaf5666Box leaf5666Inputs = true := by
  rfl'

private theorem leaf5666CoversExact : CoversExact 8
    leaf5666Box leaf5666Certificate leaf5666InnerLog leaf5666Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi267RoundedFacts
    innerPair278RoundedFacts leaf5666RoundedFacts (by rfl)

private theorem leaf5666FlatSound : Sound leaf5666Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5666CertificateValid
    leaf5666InnerLogValid leaf5666CoversExact leaf5666LowerChecked

private noncomputable def leaf5667Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (57/128), chiHi := (29/64) }

private noncomputable def leaf5667Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435773/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356739072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (641934773/536870912) }, upper := { exponent := 1, mantissa := (4977/4096) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi268LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715461631/68713478144) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf5667InnerLog : WideLogData :=
  innerPair278Data

set_option maxRecDepth 1000000 in
private theorem leaf5667LocalValidity :
    LeafFacts leaf5667Box leaf5667Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5667Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356739072) }) = true
      norm_num [leaf5667Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5667CertificateValid :
    WideCertificateValid leaf5667Box leaf5667Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi268ValidityFacts
    leaf5667LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5667CoverageChecked :
    coverageCheck (innerAD leaf5667Box) leaf5667InnerLog = true := by
  rfl'

private theorem leaf5667InnerLogValid :
    leaf5667InnerLog.Valid 8 (innerAD leaf5667Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint78PositiveFacts.valid leaf5667CoverageChecked

private noncomputable def leaf5667InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629565/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5667InputLogOnePlusV_eq :
    leaf5667InputLogOnePlusV = outerEnclosure 24
      (leaf5667Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5667RoundedFacts : LeafRoundedFacts 8
    leaf5667Certificate.logOnePlusV leaf5667InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5667InputLogOnePlusV_eq }

private noncomputable def leaf5667Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi268InputQChi innerPair278Input
    leaf5667InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5667LowerChecked :
    lowerCheck 24 leaf5667Box leaf5667Inputs = true := by
  rfl'

private theorem leaf5667CoversExact : CoversExact 8
    leaf5667Box leaf5667Certificate leaf5667InnerLog leaf5667Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi268RoundedFacts
    innerPair278RoundedFacts leaf5667RoundedFacts (by rfl)

private theorem leaf5667FlatSound : Sound leaf5667Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5667CertificateValid
    leaf5667InnerLogValid leaf5667CoversExact leaf5667LowerChecked

private noncomputable def leaf5668Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (57/128), chiHi := (29/64) }

private noncomputable def leaf5668Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435775/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356709376) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (645670095/536870912) }, upper := { exponent := 1, mantissa := (2503/2048) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi268LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715431935/68713418752) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf5668InnerLog : WideLogData :=
  innerPair279Data

set_option maxRecDepth 1000000 in
private theorem leaf5668LocalValidity :
    LeafFacts leaf5668Box leaf5668Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5668Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356709376) }) = true
      norm_num [leaf5668Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5668CertificateValid :
    WideCertificateValid leaf5668Box leaf5668Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi268ValidityFacts
    leaf5668LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5668CoverageChecked :
    coverageCheck (innerAD leaf5668Box) leaf5668InnerLog = true := by
  rfl'

private theorem leaf5668InnerLogValid :
    leaf5668InnerLog.Valid 8 (innerAD leaf5668Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint79PositiveFacts.valid leaf5668CoverageChecked

private noncomputable def leaf5668InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907393/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5668InputLogOnePlusV_eq :
    leaf5668InputLogOnePlusV = outerEnclosure 24
      (leaf5668Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5668RoundedFacts : LeafRoundedFacts 8
    leaf5668Certificate.logOnePlusV leaf5668InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5668InputLogOnePlusV_eq }

private noncomputable def leaf5668Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi268InputQChi innerPair279Input
    leaf5668InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5668LowerChecked :
    lowerCheck 24 leaf5668Box leaf5668Inputs = true := by
  rfl'

private theorem leaf5668CoversExact : CoversExact 8
    leaf5668Box leaf5668Certificate leaf5668InnerLog leaf5668Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi268RoundedFacts
    innerPair279RoundedFacts leaf5668RoundedFacts (by rfl)

private theorem leaf5668FlatSound : Sound leaf5668Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5668CertificateValid
    leaf5668InnerLogValid leaf5668CoversExact leaf5668LowerChecked

private noncomputable def leaf5669Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (7/16), chiHi := (57/128) }

private noncomputable def leaf5669Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435775/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356732416) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (642721155/536870912) }, upper := { exponent := 1, mantissa := (9967/8192) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi267LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715454975/68713464832) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf5669InnerLog : WideLogData :=
  innerPair278Data

set_option maxRecDepth 1000000 in
private theorem leaf5669LocalValidity :
    LeafFacts leaf5669Box leaf5669Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5669Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356732416) }) = true
      norm_num [leaf5669Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5669CertificateValid :
    WideCertificateValid leaf5669Box leaf5669Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi267ValidityFacts
    leaf5669LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5669CoverageChecked :
    coverageCheck (innerAD leaf5669Box) leaf5669InnerLog = true := by
  rfl'

private theorem leaf5669InnerLogValid :
    leaf5669InnerLog.Valid 8 (innerAD leaf5669Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint78PositiveFacts.valid leaf5669CoverageChecked

private noncomputable def leaf5669InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629567/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5669InputLogOnePlusV_eq :
    leaf5669InputLogOnePlusV = outerEnclosure 24
      (leaf5669Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5669RoundedFacts : LeafRoundedFacts 8
    leaf5669Certificate.logOnePlusV leaf5669InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5669InputLogOnePlusV_eq }

private noncomputable def leaf5669Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi267InputQChi innerPair278Input
    leaf5669InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5669LowerChecked :
    lowerCheck 24 leaf5669Box leaf5669Inputs = true := by
  rfl'

private theorem leaf5669CoversExact : CoversExact 8
    leaf5669Box leaf5669Certificate leaf5669InnerLog leaf5669Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi267RoundedFacts
    innerPair278RoundedFacts leaf5669RoundedFacts (by rfl)

private theorem leaf5669FlatSound : Sound leaf5669Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5669CertificateValid
    leaf5669InnerLogValid leaf5669CoversExact leaf5669LowerChecked

private noncomputable def leaf5670Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (7/16), chiHi := (57/128) }

private noncomputable def leaf5670Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435777/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356703232) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (646390945/536870912) }, upper := { exponent := 1, mantissa := (1253/1024) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi267LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715425791/68713406464) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf5670InnerLog : WideLogData :=
  innerPair279Data

set_option maxRecDepth 1000000 in
private theorem leaf5670LocalValidity :
    LeafFacts leaf5670Box leaf5670Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5670Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356703232) }) = true
      norm_num [leaf5670Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5670CertificateValid :
    WideCertificateValid leaf5670Box leaf5670Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi267ValidityFacts
    leaf5670LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5670CoverageChecked :
    coverageCheck (innerAD leaf5670Box) leaf5670InnerLog = true := by
  rfl'

private theorem leaf5670InnerLogValid :
    leaf5670InnerLog.Valid 8 (innerAD leaf5670Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint79PositiveFacts.valid leaf5670CoverageChecked

private noncomputable def leaf5670InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814787/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5670InputLogOnePlusV_eq :
    leaf5670InputLogOnePlusV = outerEnclosure 24
      (leaf5670Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5670RoundedFacts : LeafRoundedFacts 8
    leaf5670Certificate.logOnePlusV leaf5670InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5670InputLogOnePlusV_eq }

private noncomputable def leaf5670Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi267InputQChi innerPair279Input
    leaf5670InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5670LowerChecked :
    lowerCheck 24 leaf5670Box leaf5670Inputs = true := by
  rfl'

private theorem leaf5670CoversExact : CoversExact 8
    leaf5670Box leaf5670Certificate leaf5670InnerLog leaf5670Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi267RoundedFacts
    innerPair279RoundedFacts leaf5670RoundedFacts (by rfl)

private theorem leaf5670FlatSound : Sound leaf5670Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5670CertificateValid
    leaf5670InnerLogValid leaf5670CoversExact leaf5670LowerChecked

private noncomputable def leaf5671Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (57/128), chiHi := (29/64) }

private noncomputable def leaf5671Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435777/268435456) }, vSqrt := { lower := (65529/65536), upper := (227541209/227527680) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (649405417/536870912) }, upper := { exponent := 1, mantissa := (5035/4096) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi268LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (455068889/455055360) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf5671InnerLog : WideLogData :=
  innerPair279Data

set_option maxRecDepth 1000000 in
private theorem leaf5671LocalValidity :
    LeafFacts leaf5671Box leaf5671Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5671Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (227541209/227527680) }) = true
      norm_num [leaf5671Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5671CertificateValid :
    WideCertificateValid leaf5671Box leaf5671Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi268ValidityFacts
    leaf5671LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5671CoverageChecked :
    coverageCheck (innerAD leaf5671Box) leaf5671InnerLog = true := by
  rfl'

private theorem leaf5671InnerLogValid :
    leaf5671InnerLog.Valid 8 (innerAD leaf5671Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint79PositiveFacts.valid leaf5671CoverageChecked

private noncomputable def leaf5671InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907395/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5671InputLogOnePlusV_eq :
    leaf5671InputLogOnePlusV = outerEnclosure 24
      (leaf5671Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5671RoundedFacts : LeafRoundedFacts 8
    leaf5671Certificate.logOnePlusV leaf5671InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5671InputLogOnePlusV_eq }

private noncomputable def leaf5671Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi268InputQChi innerPair279Input
    leaf5671InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5671LowerChecked :
    lowerCheck 24 leaf5671Box leaf5671Inputs = true := by
  rfl'

private theorem leaf5671CoversExact : CoversExact 8
    leaf5671Box leaf5671Certificate leaf5671InnerLog leaf5671Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi268RoundedFacts
    innerPair279RoundedFacts leaf5671RoundedFacts (by rfl)

private theorem leaf5671FlatSound : Sound leaf5671Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5671CertificateValid
    leaf5671InnerLogValid leaf5671CoversExact leaf5671LowerChecked

private noncomputable def leaf5672Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (57/128), chiHi := (29/64) }

private noncomputable def leaf5672Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435779/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356649984) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (653140739/536870912) }, upper := { exponent := 1, mantissa := (633/512) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi268LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715372543/68713299968) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf5672InnerLog : WideLogData :=
  innerPair279Data

set_option maxRecDepth 1000000 in
private theorem leaf5672LocalValidity :
    LeafFacts leaf5672Box leaf5672Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5672Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356649984) }) = true
      norm_num [leaf5672Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5672CertificateValid :
    WideCertificateValid leaf5672Box leaf5672Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi268ValidityFacts
    leaf5672LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5672CoverageChecked :
    coverageCheck (innerAD leaf5672Box) leaf5672InnerLog = true := by
  rfl'

private theorem leaf5672InnerLogValid :
    leaf5672InnerLog.Valid 8 (innerAD leaf5672Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint79PositiveFacts.valid leaf5672CoverageChecked

private noncomputable def leaf5672InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629587/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5672InputLogOnePlusV_eq :
    leaf5672InputLogOnePlusV = outerEnclosure 24
      (leaf5672Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5672RoundedFacts : LeafRoundedFacts 8
    leaf5672Certificate.logOnePlusV leaf5672InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5672InputLogOnePlusV_eq }

private noncomputable def leaf5672Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi268InputQChi innerPair279Input
    leaf5672InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5672LowerChecked :
    lowerCheck 24 leaf5672Box leaf5672Inputs = true := by
  rfl'

private theorem leaf5672CoversExact : CoversExact 8
    leaf5672Box leaf5672Certificate leaf5672InnerLog leaf5672Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi268RoundedFacts
    innerPair279RoundedFacts leaf5672RoundedFacts (by rfl)

private theorem leaf5672FlatSound : Sound leaf5672Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5672CertificateValid
    leaf5672InnerLogValid leaf5672CoversExact leaf5672LowerChecked

private noncomputable def leaf5673Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (29/64), chiHi := (59/128) }

private noncomputable def leaf5673Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435775/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356687360) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (648487971/536870912) }, upper := { exponent := 1, mantissa := (10055/8192) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi269LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715409919/68713374720) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf5673InnerLog : WideLogData :=
  innerPair279Data

set_option maxRecDepth 1000000 in
private theorem leaf5673LocalValidity :
    LeafFacts leaf5673Box leaf5673Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5673Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356687360) }) = true
      norm_num [leaf5673Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5673CertificateValid :
    WideCertificateValid leaf5673Box leaf5673Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi269ValidityFacts
    leaf5673LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5673CoverageChecked :
    coverageCheck (innerAD leaf5673Box) leaf5673InnerLog = true := by
  rfl'

private theorem leaf5673InnerLogValid :
    leaf5673InnerLog.Valid 8 (innerAD leaf5673Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint79PositiveFacts.valid leaf5673CoverageChecked

private noncomputable def leaf5673InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814789/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5673InputLogOnePlusV_eq :
    leaf5673InputLogOnePlusV = outerEnclosure 24
      (leaf5673Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5673RoundedFacts : LeafRoundedFacts 8
    leaf5673Certificate.logOnePlusV leaf5673InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5673InputLogOnePlusV_eq }

private noncomputable def leaf5673Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi269InputQChi innerPair279Input
    leaf5673InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5673LowerChecked :
    lowerCheck 24 leaf5673Box leaf5673Inputs = true := by
  rfl'

private theorem leaf5673CoversExact : CoversExact 8
    leaf5673Box leaf5673Certificate leaf5673InnerLog leaf5673Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi269RoundedFacts
    innerPair279RoundedFacts leaf5673RoundedFacts (by rfl)

private theorem leaf5673FlatSound : Sound leaf5673Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5673CertificateValid
    leaf5673InnerLogValid leaf5673CoversExact leaf5673LowerChecked

private noncomputable def leaf5674Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (29/64), chiHi := (59/128) }

private noncomputable def leaf5674Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435777/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356657152) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (652288825/536870912) }, upper := { exponent := 1, mantissa := (5057/4096) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi269LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715379711/68713314304) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf5674InnerLog : WideLogData :=
  innerPair279Data

set_option maxRecDepth 1000000 in
private theorem leaf5674LocalValidity :
    LeafFacts leaf5674Box leaf5674Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5674Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356657152) }) = true
      norm_num [leaf5674Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5674CertificateValid :
    WideCertificateValid leaf5674Box leaf5674Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi269ValidityFacts
    leaf5674LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5674CoverageChecked :
    coverageCheck (innerAD leaf5674Box) leaf5674InnerLog = true := by
  rfl'

private theorem leaf5674InnerLogValid :
    leaf5674InnerLog.Valid 8 (innerAD leaf5674Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint79PositiveFacts.valid leaf5674CoverageChecked

private noncomputable def leaf5674InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629585/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5674InputLogOnePlusV_eq :
    leaf5674InputLogOnePlusV = outerEnclosure 24
      (leaf5674Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5674RoundedFacts : LeafRoundedFacts 8
    leaf5674Certificate.logOnePlusV leaf5674InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5674InputLogOnePlusV_eq }

private noncomputable def leaf5674Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi269InputQChi innerPair279Input
    leaf5674InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5674LowerChecked :
    lowerCheck 24 leaf5674Box leaf5674Inputs = true := by
  rfl'

private theorem leaf5674CoversExact : CoversExact 8
    leaf5674Box leaf5674Certificate leaf5674InnerLog leaf5674Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi269RoundedFacts
    innerPair279RoundedFacts leaf5674RoundedFacts (by rfl)

private theorem leaf5674FlatSound : Sound leaf5674Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5674CertificateValid
    leaf5674InnerLogValid leaf5674CoversExact leaf5674LowerChecked

private noncomputable def leaf5675Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (59/128), chiHi := (15/32) }

private noncomputable def leaf5675Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435777/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356635648) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (655041169/536870912) }, upper := { exponent := 1, mantissa := (2539/2048) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi270LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715358207/68713271296) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf5675InnerLog : WideLogData :=
  innerPair285Data

set_option maxRecDepth 1000000 in
private theorem leaf5675LocalValidity :
    LeafFacts leaf5675Box leaf5675Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5675Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356635648) }) = true
      norm_num [leaf5675Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5675CertificateValid :
    WideCertificateValid leaf5675Box leaf5675Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi270ValidityFacts
    leaf5675LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5675CoverageChecked :
    coverageCheck (innerAD leaf5675Box) leaf5675InnerLog = true := by
  rfl'

private theorem leaf5675InnerLogValid :
    leaf5675InnerLog.Valid 8 (innerAD leaf5675Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint79PositiveFacts.valid leaf5675CoverageChecked

private noncomputable def leaf5675InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814795/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5675InputLogOnePlusV_eq :
    leaf5675InputLogOnePlusV = outerEnclosure 24
      (leaf5675Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5675RoundedFacts : LeafRoundedFacts 8
    leaf5675Certificate.logOnePlusV leaf5675InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5675InputLogOnePlusV_eq }

private noncomputable def leaf5675Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi270InputQChi innerPair285Input
    leaf5675InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5675LowerChecked :
    lowerCheck 24 leaf5675Box leaf5675Inputs = true := by
  rfl'

private theorem leaf5675CoversExact : CoversExact 8
    leaf5675Box leaf5675Certificate leaf5675InnerLog leaf5675Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi270RoundedFacts
    innerPair285RoundedFacts leaf5675RoundedFacts (by rfl)

private theorem leaf5675FlatSound : Sound leaf5675Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5675CertificateValid
    leaf5675InnerLogValid leaf5675CoversExact leaf5675LowerChecked

private noncomputable def leaf5676Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (59/128), chiHi := (15/32) }

private noncomputable def leaf5676Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435779/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68713209856) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (658907555/536870912) }, upper := { exponent := 1, mantissa := (1277/1024) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi270LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429606397/137426419712) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf5676InnerLog : WideLogData :=
  innerPair285Data

set_option maxRecDepth 1000000 in
private theorem leaf5676LocalValidity :
    LeafFacts leaf5676Box leaf5676Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5676Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68713209856) }) = true
      norm_num [leaf5676Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5676CertificateValid :
    WideCertificateValid leaf5676Box leaf5676Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi270ValidityFacts
    leaf5676LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5676CoverageChecked :
    coverageCheck (innerAD leaf5676Box) leaf5676InnerLog = true := by
  rfl'

private theorem leaf5676InnerLogValid :
    leaf5676InnerLog.Valid 8 (innerAD leaf5676Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint79PositiveFacts.valid leaf5676CoverageChecked

private noncomputable def leaf5676InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814735/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5676InputLogOnePlusV_eq :
    leaf5676InputLogOnePlusV = outerEnclosure 24
      (leaf5676Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5676RoundedFacts : LeafRoundedFacts 8
    leaf5676Certificate.logOnePlusV leaf5676InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5676InputLogOnePlusV_eq }

private noncomputable def leaf5676Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi270InputQChi innerPair285Input
    leaf5676InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5676LowerChecked :
    lowerCheck 24 leaf5676Box leaf5676Inputs = true := by
  rfl'

private theorem leaf5676CoversExact : CoversExact 8
    leaf5676Box leaf5676Certificate leaf5676InnerLog leaf5676Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi270RoundedFacts
    innerPair285RoundedFacts leaf5676RoundedFacts (by rfl)

private theorem leaf5676FlatSound : Sound leaf5676Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5676CertificateValid
    leaf5676InnerLogValid leaf5676CoversExact leaf5676LowerChecked

private noncomputable def leaf5677Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (29/64), chiHi := (59/128) }

private noncomputable def leaf5677Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435779/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356626944) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (656089679/536870912) }, upper := { exponent := 1, mantissa := (10173/8192) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi269LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715349503/68713253888) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf5677InnerLog : WideLogData :=
  innerPair285Data

set_option maxRecDepth 1000000 in
private theorem leaf5677LocalValidity :
    LeafFacts leaf5677Box leaf5677Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5677Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356626944) }) = true
      norm_num [leaf5677Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5677CertificateValid :
    WideCertificateValid leaf5677Box leaf5677Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi269ValidityFacts
    leaf5677LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5677CoverageChecked :
    coverageCheck (innerAD leaf5677Box) leaf5677InnerLog = true := by
  rfl'

private theorem leaf5677InnerLogValid :
    leaf5677InnerLog.Valid 8 (innerAD leaf5677Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint79PositiveFacts.valid leaf5677CoverageChecked

private noncomputable def leaf5677InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453699/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5677InputLogOnePlusV_eq :
    leaf5677InputLogOnePlusV = outerEnclosure 24
      (leaf5677Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5677RoundedFacts : LeafRoundedFacts 8
    leaf5677Certificate.logOnePlusV leaf5677InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5677InputLogOnePlusV_eq }

private noncomputable def leaf5677Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi269InputQChi innerPair285Input
    leaf5677InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5677LowerChecked :
    lowerCheck 24 leaf5677Box leaf5677Inputs = true := by
  rfl'

private theorem leaf5677CoversExact : CoversExact 8
    leaf5677Box leaf5677Certificate leaf5677InnerLog leaf5677Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi269RoundedFacts
    innerPair285RoundedFacts leaf5677RoundedFacts (by rfl)

private theorem leaf5677FlatSound : Sound leaf5677Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5677CertificateValid
    leaf5677InnerLogValid leaf5677CoversExact leaf5677LowerChecked

private noncomputable def leaf5678Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (29/64), chiHi := (59/128) }

private noncomputable def leaf5678Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435781/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68713193472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (659890533/536870912) }, upper := { exponent := 1, mantissa := (1279/1024) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi269LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429590013/137426386944) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf5678InnerLog : WideLogData :=
  innerPair285Data

set_option maxRecDepth 1000000 in
private theorem leaf5678LocalValidity :
    LeafFacts leaf5678Box leaf5678Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5678Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68713193472) }) = true
      norm_num [leaf5678Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5678CertificateValid :
    WideCertificateValid leaf5678Box leaf5678Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi269ValidityFacts
    leaf5678LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5678CoverageChecked :
    coverageCheck (innerAD leaf5678Box) leaf5678InnerLog = true := by
  rfl'

private theorem leaf5678InnerLogValid :
    leaf5678InnerLog.Valid 8 (innerAD leaf5678Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint79PositiveFacts.valid leaf5678CoverageChecked

private noncomputable def leaf5678InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (363421/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf5678InputLogOnePlusV_eq :
    leaf5678InputLogOnePlusV = outerEnclosure 24
      (leaf5678Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5678RoundedFacts : LeafRoundedFacts 8
    leaf5678Certificate.logOnePlusV leaf5678InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5678InputLogOnePlusV_eq }

private noncomputable def leaf5678Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi269InputQChi innerPair285Input
    leaf5678InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5678LowerChecked :
    lowerCheck 24 leaf5678Box leaf5678Inputs = true := by
  rfl'

private theorem leaf5678CoversExact : CoversExact 8
    leaf5678Box leaf5678Certificate leaf5678InnerLog leaf5678Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi269RoundedFacts
    innerPair285RoundedFacts leaf5678RoundedFacts (by rfl)

private theorem leaf5678FlatSound : Sound leaf5678Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5678CertificateValid
    leaf5678InnerLogValid leaf5678CoversExact leaf5678LowerChecked

private noncomputable def leaf5679Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (59/128), chiHi := (15/32) }

private noncomputable def leaf5679Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435781/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68713148416) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (662773941/536870912) }, upper := { exponent := 1, mantissa := (2569/2048) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi270LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429544957/137426296832) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf5679InnerLog : WideLogData :=
  innerPair286Data

set_option maxRecDepth 1000000 in
private theorem leaf5679LocalValidity :
    LeafFacts leaf5679Box leaf5679Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5679Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68713148416) }) = true
      norm_num [leaf5679Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5679CertificateValid :
    WideCertificateValid leaf5679Box leaf5679Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi270ValidityFacts
    leaf5679LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5679CoverageChecked :
    coverageCheck (innerAD leaf5679Box) leaf5679InnerLog = true := by
  rfl'

private theorem leaf5679InnerLogValid :
    leaf5679InnerLog.Valid 8 (innerAD leaf5679Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint90PositiveFacts.valid leaf5679CoverageChecked

private noncomputable def leaf5679InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629477/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5679InputLogOnePlusV_eq :
    leaf5679InputLogOnePlusV = outerEnclosure 24
      (leaf5679Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5679RoundedFacts : LeafRoundedFacts 8
    leaf5679Certificate.logOnePlusV leaf5679InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5679InputLogOnePlusV_eq }

private noncomputable def leaf5679Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi270InputQChi innerPair286Input
    leaf5679InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5679LowerChecked :
    lowerCheck 24 leaf5679Box leaf5679Inputs = true := by
  rfl'

private theorem leaf5679CoversExact : CoversExact 8
    leaf5679Box leaf5679Certificate leaf5679InnerLog leaf5679Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi270RoundedFacts
    innerPair286RoundedFacts leaf5679RoundedFacts (by rfl)

private theorem leaf5679FlatSound : Sound leaf5679Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5679CertificateValid
    leaf5679InnerLogValid leaf5679CoversExact leaf5679LowerChecked

private noncomputable def leaf5680Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (59/128), chiHi := (15/32) }

private noncomputable def leaf5680Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435783/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68713086976) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (666640327/536870912) }, upper := { exponent := 1, mantissa := (323/256) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi270LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429483517/137426173952) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf5680InnerLog : WideLogData :=
  innerPair286Data

set_option maxRecDepth 1000000 in
private theorem leaf5680LocalValidity :
    LeafFacts leaf5680Box leaf5680Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5680Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68713086976) }) = true
      norm_num [leaf5680Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5680CertificateValid :
    WideCertificateValid leaf5680Box leaf5680Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi270ValidityFacts
    leaf5680LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5680CoverageChecked :
    coverageCheck (innerAD leaf5680Box) leaf5680InnerLog = true := by
  rfl'

private theorem leaf5680InnerLogValid :
    leaf5680InnerLog.Valid 8 (innerAD leaf5680Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint90PositiveFacts.valid leaf5680CoverageChecked

private noncomputable def leaf5680InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629485/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5680InputLogOnePlusV_eq :
    leaf5680InputLogOnePlusV = outerEnclosure 24
      (leaf5680Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5680RoundedFacts : LeafRoundedFacts 8
    leaf5680Certificate.logOnePlusV leaf5680InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5680InputLogOnePlusV_eq }

private noncomputable def leaf5680Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi270InputQChi innerPair286Input
    leaf5680InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5680LowerChecked :
    lowerCheck 24 leaf5680Box leaf5680Inputs = true := by
  rfl'

private theorem leaf5680CoversExact : CoversExact 8
    leaf5680Box leaf5680Certificate leaf5680InnerLog leaf5680Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi270RoundedFacts
    innerPair286RoundedFacts leaf5680RoundedFacts (by rfl)

private theorem leaf5680FlatSound : Sound leaf5680Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5680CertificateValid
    leaf5680InnerLogValid leaf5680CoversExact leaf5680LowerChecked

private noncomputable def leaf5681Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (15/32), chiHi := (61/128) }

private noncomputable def leaf5681Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435779/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68713167872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (661594367/536870912) }, upper := { exponent := 1, mantissa := (10257/8192) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi271LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429564413/137426335744) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf5681InnerLog : WideLogData :=
  innerPair286Data

set_option maxRecDepth 1000000 in
private theorem leaf5681LocalValidity :
    LeafFacts leaf5681Box leaf5681Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5681Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68713167872) }) = true
      norm_num [leaf5681Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5681CertificateValid :
    WideCertificateValid leaf5681Box leaf5681Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi271ValidityFacts
    leaf5681LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5681CoverageChecked :
    coverageCheck (innerAD leaf5681Box) leaf5681InnerLog = true := by
  rfl'

private theorem leaf5681InnerLogValid :
    leaf5681InnerLog.Valid 8 (innerAD leaf5681Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint90PositiveFacts.valid leaf5681CoverageChecked

private noncomputable def leaf5681InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629475/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5681InputLogOnePlusV_eq :
    leaf5681InputLogOnePlusV = outerEnclosure 24
      (leaf5681Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5681RoundedFacts : LeafRoundedFacts 8
    leaf5681Certificate.logOnePlusV leaf5681InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5681InputLogOnePlusV_eq }

private noncomputable def leaf5681Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi271InputQChi innerPair286Input
    leaf5681InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5681LowerChecked :
    lowerCheck 24 leaf5681Box leaf5681Inputs = true := by
  rfl'

private theorem leaf5681CoversExact : CoversExact 8
    leaf5681Box leaf5681Certificate leaf5681InnerLog leaf5681Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi271RoundedFacts
    innerPair286RoundedFacts leaf5681RoundedFacts (by rfl)

private theorem leaf5681FlatSound : Sound leaf5681Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5681CertificateValid
    leaf5681InnerLogValid leaf5681CoversExact leaf5681LowerChecked

private noncomputable def leaf5682Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (15/32), chiHi := (61/128) }

private noncomputable def leaf5682Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435781/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68713105408) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (665526285/536870912) }, upper := { exponent := 1, mantissa := (5159/4096) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi271LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429501949/137426210816) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf5682InnerLog : WideLogData :=
  innerPair286Data

set_option maxRecDepth 1000000 in
private theorem leaf5682LocalValidity :
    LeafFacts leaf5682Box leaf5682Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5682Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68713105408) }) = true
      norm_num [leaf5682Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5682CertificateValid :
    WideCertificateValid leaf5682Box leaf5682Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi271ValidityFacts
    leaf5682LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5682CoverageChecked :
    coverageCheck (innerAD leaf5682Box) leaf5682InnerLog = true := by
  rfl'

private theorem leaf5682InnerLogValid :
    leaf5682InnerLog.Valid 8 (innerAD leaf5682Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint90PositiveFacts.valid leaf5682CoverageChecked

private noncomputable def leaf5682InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629483/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5682InputLogOnePlusV_eq :
    leaf5682InputLogOnePlusV = outerEnclosure 24
      (leaf5682Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5682RoundedFacts : LeafRoundedFacts 8
    leaf5682Certificate.logOnePlusV leaf5682InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5682InputLogOnePlusV_eq }

private noncomputable def leaf5682Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi271InputQChi innerPair286Input
    leaf5682InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5682LowerChecked :
    lowerCheck 24 leaf5682Box leaf5682Inputs = true := by
  rfl'

private theorem leaf5682CoversExact : CoversExact 8
    leaf5682Box leaf5682Certificate leaf5682InnerLog leaf5682Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi271RoundedFacts
    innerPair286RoundedFacts leaf5682RoundedFacts (by rfl)

private theorem leaf5682FlatSound : Sound leaf5682Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5682CertificateValid
    leaf5682InnerLogValid leaf5682CoversExact leaf5682LowerChecked

private noncomputable def leaf5683Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (61/128), chiHi := (31/64) }

private noncomputable def leaf5683Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435781/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68713064448) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (668147565/536870912) }, upper := { exponent := 1, mantissa := (5179/4096) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi272LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429460989/137426128896) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf5683InnerLog : WideLogData :=
  innerPair286Data

set_option maxRecDepth 1000000 in
private theorem leaf5683LocalValidity :
    LeafFacts leaf5683Box leaf5683Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5683Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68713064448) }) = true
      norm_num [leaf5683Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5683CertificateValid :
    WideCertificateValid leaf5683Box leaf5683Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi272ValidityFacts
    leaf5683LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5683CoverageChecked :
    coverageCheck (innerAD leaf5683Box) leaf5683InnerLog = true := by
  rfl'

private theorem leaf5683InnerLogValid :
    leaf5683InnerLog.Valid 8 (innerAD leaf5683Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint90PositiveFacts.valid leaf5683CoverageChecked

private noncomputable def leaf5683InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (726843/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf5683InputLogOnePlusV_eq :
    leaf5683InputLogOnePlusV = outerEnclosure 24
      (leaf5683Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5683RoundedFacts : LeafRoundedFacts 8
    leaf5683Certificate.logOnePlusV leaf5683InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5683InputLogOnePlusV_eq }

private noncomputable def leaf5683Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi272InputQChi innerPair286Input
    leaf5683InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5683LowerChecked :
    lowerCheck 24 leaf5683Box leaf5683Inputs = true := by
  rfl'

private theorem leaf5683CoversExact : CoversExact 8
    leaf5683Box leaf5683Certificate leaf5683InnerLog leaf5683Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi272RoundedFacts
    innerPair286RoundedFacts leaf5683RoundedFacts (by rfl)

private theorem leaf5683FlatSound : Sound leaf5683Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5683CertificateValid
    leaf5683InnerLogValid leaf5683CoversExact leaf5683LowerChecked

private noncomputable def leaf5684Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (61/128), chiHi := (31/64) }

private noncomputable def leaf5684Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435783/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68713000960) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (672145015/536870912) }, upper := { exponent := 1, mantissa := (2605/2048) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi272LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429397501/137426001920) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf5684InnerLog : WideLogData :=
  innerPair293Data

set_option maxRecDepth 1000000 in
private theorem leaf5684LocalValidity :
    LeafFacts leaf5684Box leaf5684Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5684Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68713000960) }) = true
      norm_num [leaf5684Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5684CertificateValid :
    WideCertificateValid leaf5684Box leaf5684Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi272ValidityFacts
    leaf5684LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5684CoverageChecked :
    coverageCheck (innerAD leaf5684Box) leaf5684InnerLog = true := by
  rfl'

private theorem leaf5684InnerLogValid :
    leaf5684InnerLog.Valid 8 (innerAD leaf5684Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint90PositiveFacts.valid leaf5684CoverageChecked

private noncomputable def leaf5684InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629495/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5684InputLogOnePlusV_eq :
    leaf5684InputLogOnePlusV = outerEnclosure 24
      (leaf5684Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5684RoundedFacts : LeafRoundedFacts 8
    leaf5684Certificate.logOnePlusV leaf5684InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5684InputLogOnePlusV_eq }

private noncomputable def leaf5684Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi272InputQChi innerPair293Input
    leaf5684InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5684LowerChecked :
    lowerCheck 24 leaf5684Box leaf5684Inputs = true := by
  rfl'

private theorem leaf5684CoversExact : CoversExact 8
    leaf5684Box leaf5684Certificate leaf5684InnerLog leaf5684Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi272RoundedFacts
    innerPair293RoundedFacts leaf5684RoundedFacts (by rfl)

private theorem leaf5684FlatSound : Sound leaf5684Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5684CertificateValid
    leaf5684InnerLogValid leaf5684CoversExact leaf5684LowerChecked

private noncomputable def leaf5685Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (15/32), chiHi := (61/128) }

private noncomputable def leaf5685Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435783/268435456) }, vSqrt := { lower := (65529/65536), upper := (5285876657/5285618688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (669458203/536870912) }, upper := { exponent := 1, mantissa := (10379/8192) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi271LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (10571495345/10571237376) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf5685InnerLog : WideLogData :=
  innerPair286Data

set_option maxRecDepth 1000000 in
private theorem leaf5685LocalValidity :
    LeafFacts leaf5685Box leaf5685Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5685Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (5285876657/5285618688) }) = true
      norm_num [leaf5685Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5685CertificateValid :
    WideCertificateValid leaf5685Box leaf5685Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi271ValidityFacts
    leaf5685LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5685CoverageChecked :
    coverageCheck (innerAD leaf5685Box) leaf5685InnerLog = true := by
  rfl'

private theorem leaf5685InnerLogValid :
    leaf5685InnerLog.Valid 8 (innerAD leaf5685Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint90PositiveFacts.valid leaf5685CoverageChecked

private noncomputable def leaf5685InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814745/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5685InputLogOnePlusV_eq :
    leaf5685InputLogOnePlusV = outerEnclosure 24
      (leaf5685Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5685RoundedFacts : LeafRoundedFacts 8
    leaf5685Certificate.logOnePlusV leaf5685InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5685InputLogOnePlusV_eq }

private noncomputable def leaf5685Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi271InputQChi innerPair286Input
    leaf5685InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5685LowerChecked :
    lowerCheck 24 leaf5685Box leaf5685Inputs = true := by
  rfl'

private theorem leaf5685CoversExact : CoversExact 8
    leaf5685Box leaf5685Certificate leaf5685InnerLog leaf5685Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi271RoundedFacts
    innerPair286RoundedFacts leaf5685RoundedFacts (by rfl)

private theorem leaf5685FlatSound : Sound leaf5685Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5685CertificateValid
    leaf5685InnerLogValid leaf5685CoversExact leaf5685LowerChecked

private noncomputable def leaf5686Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (15/32), chiHi := (61/128) }

private noncomputable def leaf5686Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435785/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712980480) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (673390121/536870912) }, upper := { exponent := 1, mantissa := (1305/1024) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi271LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429377021/137425960960) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf5686InnerLog : WideLogData :=
  innerPair293Data

set_option maxRecDepth 1000000 in
private theorem leaf5686LocalValidity :
    LeafFacts leaf5686Box leaf5686Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5686Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712980480) }) = true
      norm_num [leaf5686Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5686CertificateValid :
    WideCertificateValid leaf5686Box leaf5686Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi271ValidityFacts
    leaf5686LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5686CoverageChecked :
    coverageCheck (innerAD leaf5686Box) leaf5686InnerLog = true := by
  rfl'

private theorem leaf5686InnerLogValid :
    leaf5686InnerLog.Valid 8 (innerAD leaf5686Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint90PositiveFacts.valid leaf5686CoverageChecked

private noncomputable def leaf5686InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814749/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5686InputLogOnePlusV_eq :
    leaf5686InputLogOnePlusV = outerEnclosure 24
      (leaf5686Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5686RoundedFacts : LeafRoundedFacts 8
    leaf5686Certificate.logOnePlusV leaf5686InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5686InputLogOnePlusV_eq }

private noncomputable def leaf5686Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi271InputQChi innerPair293Input
    leaf5686InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5686LowerChecked :
    lowerCheck 24 leaf5686Box leaf5686Inputs = true := by
  rfl'

private theorem leaf5686CoversExact : CoversExact 8
    leaf5686Box leaf5686Certificate leaf5686InnerLog leaf5686Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi271RoundedFacts
    innerPair293RoundedFacts leaf5686RoundedFacts (by rfl)

private theorem leaf5686FlatSound : Sound leaf5686Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5686CertificateValid
    leaf5686InnerLogValid leaf5686CoversExact leaf5686LowerChecked

private noncomputable def leaf5687Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (61/128), chiHi := (31/64) }

private noncomputable def leaf5687Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435785/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712937472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (676142465/536870912) }, upper := { exponent := 1, mantissa := (5241/4096) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi272LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429334013/137425874944) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf5687InnerLog : WideLogData :=
  innerPair293Data

set_option maxRecDepth 1000000 in
private theorem leaf5687LocalValidity :
    LeafFacts leaf5687Box leaf5687Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5687Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712937472) }) = true
      norm_num [leaf5687Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5687CertificateValid :
    WideCertificateValid leaf5687Box leaf5687Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi272ValidityFacts
    leaf5687LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5687CoverageChecked :
    coverageCheck (innerAD leaf5687Box) leaf5687InnerLog = true := by
  rfl'

private theorem leaf5687InnerLogValid :
    leaf5687InnerLog.Valid 8 (innerAD leaf5687Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint90PositiveFacts.valid leaf5687CoverageChecked

private noncomputable def leaf5687InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629503/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5687InputLogOnePlusV_eq :
    leaf5687InputLogOnePlusV = outerEnclosure 24
      (leaf5687Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5687RoundedFacts : LeafRoundedFacts 8
    leaf5687Certificate.logOnePlusV leaf5687InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5687InputLogOnePlusV_eq }

private noncomputable def leaf5687Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi272InputQChi innerPair293Input
    leaf5687InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5687LowerChecked :
    lowerCheck 24 leaf5687Box leaf5687Inputs = true := by
  rfl'

private theorem leaf5687CoversExact : CoversExact 8
    leaf5687Box leaf5687Certificate leaf5687InnerLog leaf5687Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi272RoundedFacts
    innerPair293RoundedFacts leaf5687RoundedFacts (by rfl)

private theorem leaf5687FlatSound : Sound leaf5687Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5687CertificateValid
    leaf5687InnerLogValid leaf5687CoversExact leaf5687LowerChecked

private noncomputable def leaf5688Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (61/128), chiHi := (31/64) }

private noncomputable def leaf5688Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435787/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712873984) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (680139915/536870912) }, upper := { exponent := 1, mantissa := (659/512) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi272LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429270525/137425747968) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf5688InnerLog : WideLogData :=
  innerPair294Data

set_option maxRecDepth 1000000 in
private theorem leaf5688LocalValidity :
    LeafFacts leaf5688Box leaf5688Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5688Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712873984) }) = true
      norm_num [leaf5688Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5688CertificateValid :
    WideCertificateValid leaf5688Box leaf5688Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi272ValidityFacts
    leaf5688LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5688CoverageChecked :
    coverageCheck (innerAD leaf5688Box) leaf5688InnerLog = true := by
  rfl'

private theorem leaf5688InnerLogValid :
    leaf5688InnerLog.Valid 8 (innerAD leaf5688Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint91PositiveFacts.valid leaf5688CoverageChecked

private noncomputable def leaf5688InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629511/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5688InputLogOnePlusV_eq :
    leaf5688InputLogOnePlusV = outerEnclosure 24
      (leaf5688Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5688RoundedFacts : LeafRoundedFacts 8
    leaf5688Certificate.logOnePlusV leaf5688InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5688InputLogOnePlusV_eq }

private noncomputable def leaf5688Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi272InputQChi innerPair294Input
    leaf5688InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5688LowerChecked :
    lowerCheck 24 leaf5688Box leaf5688Inputs = true := by
  rfl'

private theorem leaf5688CoversExact : CoversExact 8
    leaf5688Box leaf5688Certificate leaf5688InnerLog leaf5688Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi272RoundedFacts
    innerPair294RoundedFacts leaf5688RoundedFacts (by rfl)

private theorem leaf5688FlatSound : Sound leaf5688Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5688CertificateValid
    leaf5688InnerLogValid leaf5688CoversExact leaf5688LowerChecked

private noncomputable def leaf5689Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (31/64), chiHi := (63/128) }

private noncomputable def leaf5689Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435783/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712961024) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (674700763/536870912) }, upper := { exponent := 1, mantissa := (10459/8192) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi273LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429357565/137425922048) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf5689InnerLog : WideLogData :=
  innerPair293Data

set_option maxRecDepth 1000000 in
private theorem leaf5689LocalValidity :
    LeafFacts leaf5689Box leaf5689Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5689Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712961024) }) = true
      norm_num [leaf5689Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5689CertificateValid :
    WideCertificateValid leaf5689Box leaf5689Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi273ValidityFacts
    leaf5689LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5689CoverageChecked :
    coverageCheck (innerAD leaf5689Box) leaf5689InnerLog = true := by
  rfl'

private theorem leaf5689InnerLogValid :
    leaf5689InnerLog.Valid 8 (innerAD leaf5689Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint90PositiveFacts.valid leaf5689CoverageChecked

private noncomputable def leaf5689InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907375/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5689InputLogOnePlusV_eq :
    leaf5689InputLogOnePlusV = outerEnclosure 24
      (leaf5689Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5689RoundedFacts : LeafRoundedFacts 8
    leaf5689Certificate.logOnePlusV leaf5689InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5689InputLogOnePlusV_eq }

private noncomputable def leaf5689Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi273InputQChi innerPair293Input
    leaf5689InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5689LowerChecked :
    lowerCheck 24 leaf5689Box leaf5689Inputs = true := by
  rfl'

private theorem leaf5689CoversExact : CoversExact 8
    leaf5689Box leaf5689Certificate leaf5689InnerLog leaf5689Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi273RoundedFacts
    innerPair293RoundedFacts leaf5689RoundedFacts (by rfl)

private theorem leaf5689FlatSound : Sound leaf5689Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5689CertificateValid
    leaf5689InnerLogValid leaf5689CoversExact leaf5689LowerChecked

private noncomputable def leaf5690Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (31/64), chiHi := (63/128) }

private noncomputable def leaf5690Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435785/268435456) }, vSqrt := { lower := (65529/65536), upper := (5285876657/5285607424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (678763745/536870912) }, upper := { exponent := 1, mantissa := (5261/4096) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi273LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (10571484081/10571214848) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf5690InnerLog : WideLogData :=
  innerPair294Data

set_option maxRecDepth 1000000 in
private theorem leaf5690LocalValidity :
    LeafFacts leaf5690Box leaf5690Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5690Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (5285876657/5285607424) }) = true
      norm_num [leaf5690Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5690CertificateValid :
    WideCertificateValid leaf5690Box leaf5690Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi273ValidityFacts
    leaf5690LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5690CoverageChecked :
    coverageCheck (innerAD leaf5690Box) leaf5690InnerLog = true := by
  rfl'

private theorem leaf5690InnerLogValid :
    leaf5690InnerLog.Valid 8 (innerAD leaf5690Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint91PositiveFacts.valid leaf5690CoverageChecked

private noncomputable def leaf5690InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907377/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5690InputLogOnePlusV_eq :
    leaf5690InputLogOnePlusV = outerEnclosure 24
      (leaf5690Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5690RoundedFacts : LeafRoundedFacts 8
    leaf5690Certificate.logOnePlusV leaf5690InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5690InputLogOnePlusV_eq }

private noncomputable def leaf5690Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi273InputQChi innerPair294Input
    leaf5690InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5690LowerChecked :
    lowerCheck 24 leaf5690Box leaf5690Inputs = true := by
  rfl'

private theorem leaf5690CoversExact : CoversExact 8
    leaf5690Box leaf5690Certificate leaf5690InnerLog leaf5690Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi273RoundedFacts
    innerPair294RoundedFacts leaf5690RoundedFacts (by rfl)

private theorem leaf5690FlatSound : Sound leaf5690Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5690CertificateValid
    leaf5690InnerLogValid leaf5690CoversExact leaf5690LowerChecked

private noncomputable def leaf5691Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (63/128), chiHi := (1/2) }

private noncomputable def leaf5691Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435785/268435456) }, vSqrt := { lower := (65529/65536), upper := (4042140973/4041932800) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (681253961/536870912) }, upper := { exponent := 1, mantissa := (165/128) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi274LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (8084073773/8083865600) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf5691InnerLog : WideLogData :=
  innerPair294Data

set_option maxRecDepth 1000000 in
private theorem leaf5691LocalValidity :
    LeafFacts leaf5691Box leaf5691Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5691Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4042140973/4041932800) }) = true
      norm_num [leaf5691Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5691CertificateValid :
    WideCertificateValid leaf5691Box leaf5691Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi274ValidityFacts
    leaf5691LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5691CoverageChecked :
    coverageCheck (innerAD leaf5691Box) leaf5691InnerLog = true := by
  rfl'

private theorem leaf5691InnerLogValid :
    leaf5691InnerLog.Valid 8 (innerAD leaf5691Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint91PositiveFacts.valid leaf5691CoverageChecked

private noncomputable def leaf5691InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629513/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5691InputLogOnePlusV_eq :
    leaf5691InputLogOnePlusV = outerEnclosure 24
      (leaf5691Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5691RoundedFacts : LeafRoundedFacts 8
    leaf5691Certificate.logOnePlusV leaf5691InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5691InputLogOnePlusV_eq }

private noncomputable def leaf5691Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi274InputQChi innerPair294Input
    leaf5691InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5691LowerChecked :
    lowerCheck 24 leaf5691Box leaf5691Inputs = true := by
  rfl'

private theorem leaf5691CoversExact : CoversExact 8
    leaf5691Box leaf5691Certificate leaf5691InnerLog leaf5691Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi274RoundedFacts
    innerPair294RoundedFacts leaf5691RoundedFacts (by rfl)

private theorem leaf5691FlatSound : Sound leaf5691Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5691CertificateValid
    leaf5691InnerLogValid leaf5691CoversExact leaf5691LowerChecked

private noncomputable def leaf5692Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (63/128), chiHi := (1/2) }

private noncomputable def leaf5692Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435787/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712792064) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (685382475/536870912) }, upper := { exponent := 1, mantissa := (83/64) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi274LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429188605/137425584128) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf5692InnerLog : WideLogData :=
  innerPair294Data

set_option maxRecDepth 1000000 in
private theorem leaf5692LocalValidity :
    LeafFacts leaf5692Box leaf5692Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5692Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712792064) }) = true
      norm_num [leaf5692Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5692CertificateValid :
    WideCertificateValid leaf5692Box leaf5692Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi274ValidityFacts
    leaf5692LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5692CoverageChecked :
    coverageCheck (innerAD leaf5692Box) leaf5692InnerLog = true := by
  rfl'

private theorem leaf5692InnerLogValid :
    leaf5692InnerLog.Valid 8 (innerAD leaf5692Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint91PositiveFacts.valid leaf5692CoverageChecked

private noncomputable def leaf5692InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629521/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5692InputLogOnePlusV_eq :
    leaf5692InputLogOnePlusV = outerEnclosure 24
      (leaf5692Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5692RoundedFacts : LeafRoundedFacts 8
    leaf5692Certificate.logOnePlusV leaf5692InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5692InputLogOnePlusV_eq }

private noncomputable def leaf5692Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi274InputQChi innerPair294Input
    leaf5692InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5692LowerChecked :
    lowerCheck 24 leaf5692Box leaf5692Inputs = true := by
  rfl'

private theorem leaf5692CoversExact : CoversExact 8
    leaf5692Box leaf5692Certificate leaf5692InnerLog leaf5692Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi274RoundedFacts
    innerPair294RoundedFacts leaf5692RoundedFacts (by rfl)

private theorem leaf5692FlatSound : Sound leaf5692Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5692CertificateValid
    leaf5692InnerLogValid leaf5692CoversExact leaf5692LowerChecked

private noncomputable def leaf5693Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (31/64), chiHi := (63/128) }

private noncomputable def leaf5693Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435787/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712832000) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (682826727/536870912) }, upper := { exponent := 1, mantissa := (10585/8192) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi273LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429228541/137425664000) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf5693InnerLog : WideLogData :=
  innerPair294Data

set_option maxRecDepth 1000000 in
private theorem leaf5693LocalValidity :
    LeafFacts leaf5693Box leaf5693Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5693Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712832000) }) = true
      norm_num [leaf5693Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5693CertificateValid :
    WideCertificateValid leaf5693Box leaf5693Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi273ValidityFacts
    leaf5693LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5693CoverageChecked :
    coverageCheck (innerAD leaf5693Box) leaf5693InnerLog = true := by
  rfl'

private theorem leaf5693InnerLogValid :
    leaf5693InnerLog.Valid 8 (innerAD leaf5693Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint91PositiveFacts.valid leaf5693CoverageChecked

private noncomputable def leaf5693InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907379/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5693InputLogOnePlusV_eq :
    leaf5693InputLogOnePlusV = outerEnclosure 24
      (leaf5693Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5693RoundedFacts : LeafRoundedFacts 8
    leaf5693Certificate.logOnePlusV leaf5693InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5693InputLogOnePlusV_eq }

private noncomputable def leaf5693Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi273InputQChi innerPair294Input
    leaf5693InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5693LowerChecked :
    lowerCheck 24 leaf5693Box leaf5693Inputs = true := by
  rfl'

private theorem leaf5693CoversExact : CoversExact 8
    leaf5693Box leaf5693Certificate leaf5693InnerLog leaf5693Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi273RoundedFacts
    innerPair294RoundedFacts leaf5693RoundedFacts (by rfl)

private theorem leaf5693FlatSound : Sound leaf5693Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5693CertificateValid
    leaf5693InnerLogValid leaf5693CoversExact leaf5693LowerChecked

private noncomputable def leaf5694Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (31/64), chiHi := (63/128) }

private noncomputable def leaf5694Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435789/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712767488) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (686889709/536870912) }, upper := { exponent := 1, mantissa := (1331/1024) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi273LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429164029/137425534976) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf5694InnerLog : WideLogData :=
  innerPair294Data

set_option maxRecDepth 1000000 in
private theorem leaf5694LocalValidity :
    LeafFacts leaf5694Box leaf5694Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5694Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712767488) }) = true
      norm_num [leaf5694Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5694CertificateValid :
    WideCertificateValid leaf5694Box leaf5694Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi273ValidityFacts
    leaf5694LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5694CoverageChecked :
    coverageCheck (innerAD leaf5694Box) leaf5694InnerLog = true := by
  rfl'

private theorem leaf5694InnerLogValid :
    leaf5694InnerLog.Valid 8 (innerAD leaf5694Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint91PositiveFacts.valid leaf5694CoverageChecked

private noncomputable def leaf5694InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907381/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5694InputLogOnePlusV_eq :
    leaf5694InputLogOnePlusV = outerEnclosure 24
      (leaf5694Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5694RoundedFacts : LeafRoundedFacts 8
    leaf5694Certificate.logOnePlusV leaf5694InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5694InputLogOnePlusV_eq }

private noncomputable def leaf5694Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi273InputQChi innerPair294Input
    leaf5694InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5694LowerChecked :
    lowerCheck 24 leaf5694Box leaf5694Inputs = true := by
  rfl'

private theorem leaf5694CoversExact : CoversExact 8
    leaf5694Box leaf5694Certificate leaf5694InnerLog leaf5694Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi273RoundedFacts
    innerPair294RoundedFacts leaf5694RoundedFacts (by rfl)

private theorem leaf5694FlatSound : Sound leaf5694Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5694CertificateValid
    leaf5694InnerLogValid leaf5694CoversExact leaf5694LowerChecked

private noncomputable def leaf5695Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (63/128), chiHi := (1/2) }

private noncomputable def leaf5695Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435789/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712726528) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (689510989/536870912) }, upper := { exponent := 1, mantissa := (167/128) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi274LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429123069/137425453056) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf5695InnerLog : WideLogData :=
  innerPair339Data

set_option maxRecDepth 1000000 in
private theorem leaf5695LocalValidity :
    LeafFacts leaf5695Box leaf5695Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5695Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712726528) }) = true
      norm_num [leaf5695Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5695CertificateValid :
    WideCertificateValid leaf5695Box leaf5695Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi274ValidityFacts
    leaf5695LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5695CoverageChecked :
    coverageCheck (innerAD leaf5695Box) leaf5695InnerLog = true := by
  rfl'

private theorem leaf5695InnerLogValid :
    leaf5695InnerLog.Valid 8 (innerAD leaf5695Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint91PositiveFacts.valid leaf5695CoverageChecked

private noncomputable def leaf5695InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629529/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5695InputLogOnePlusV_eq :
    leaf5695InputLogOnePlusV = outerEnclosure 24
      (leaf5695Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5695RoundedFacts : LeafRoundedFacts 8
    leaf5695Certificate.logOnePlusV leaf5695InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5695InputLogOnePlusV_eq }

private noncomputable def leaf5695Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi274InputQChi innerPair339Input
    leaf5695InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5695LowerChecked :
    lowerCheck 24 leaf5695Box leaf5695Inputs = true := by
  rfl'

private theorem leaf5695CoversExact : CoversExact 8
    leaf5695Box leaf5695Certificate leaf5695InnerLog leaf5695Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi274RoundedFacts
    innerPair339RoundedFacts leaf5695RoundedFacts (by rfl)

private theorem leaf5695FlatSound : Sound leaf5695Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5695CertificateValid
    leaf5695InnerLogValid leaf5695CoversExact leaf5695LowerChecked

private noncomputable def leaf5696Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (63/128), chiHi := (1/2) }

private noncomputable def leaf5696Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435791/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712660992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (693639503/536870912) }, upper := { exponent := 1, mantissa := (21/16) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi274LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429057533/137425321984) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf5696InnerLog : WideLogData :=
  innerPair339Data

set_option maxRecDepth 1000000 in
private theorem leaf5696LocalValidity :
    LeafFacts leaf5696Box leaf5696Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5696Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712660992) }) = true
      norm_num [leaf5696Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5696CertificateValid :
    WideCertificateValid leaf5696Box leaf5696Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi274ValidityFacts
    leaf5696LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5696CoverageChecked :
    coverageCheck (innerAD leaf5696Box) leaf5696InnerLog = true := by
  rfl'

private theorem leaf5696InnerLogValid :
    leaf5696InnerLog.Valid 8 (innerAD leaf5696Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint91PositiveFacts.valid leaf5696CoverageChecked

private noncomputable def leaf5696InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629537/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5696InputLogOnePlusV_eq :
    leaf5696InputLogOnePlusV = outerEnclosure 24
      (leaf5696Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5696RoundedFacts : LeafRoundedFacts 8
    leaf5696Certificate.logOnePlusV leaf5696InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5696InputLogOnePlusV_eq }

private noncomputable def leaf5696Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi274InputQChi innerPair339Input
    leaf5696InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5696LowerChecked :
    lowerCheck 24 leaf5696Box leaf5696Inputs = true := by
  rfl'

private theorem leaf5696CoversExact : CoversExact 8
    leaf5696Box leaf5696Certificate leaf5696InnerLog leaf5696Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi274RoundedFacts
    innerPair339RoundedFacts leaf5696RoundedFacts (by rfl)

private theorem leaf5696FlatSound : Sound leaf5696Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5696CertificateValid
    leaf5696InnerLogValid leaf5696CoversExact leaf5696LowerChecked

private noncomputable def component114Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (7/16), chiHi := (57/128) }

set_option maxRecDepth 1000000 in
private theorem component114Node0_sound : Sound component114Node0Box :=
  sound_of_literal_split component114Node0Box leaf5633Box leaf5634Box
    .k (97/32) (by rfl) (by rfl)
    leaf5633FlatSound leaf5634FlatSound

private noncomputable def component114Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (57/128), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component114Node1_sound : Sound component114Node1Box :=
  sound_of_literal_split component114Node1Box leaf5635Box leaf5636Box
    .k (97/32) (by rfl) (by rfl)
    leaf5635FlatSound leaf5636FlatSound

private noncomputable def component114Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (7/16), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component114Node2_sound : Sound component114Node2Box :=
  sound_of_literal_split component114Node2Box component114Node0Box component114Node1Box
    .chi (57/128) (by rfl) (by rfl)
    component114Node0_sound component114Node1_sound

private noncomputable def component114Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (7/16), chiHi := (57/128) }

set_option maxRecDepth 1000000 in
private theorem component114Node3_sound : Sound component114Node3Box :=
  sound_of_literal_split component114Node3Box leaf5637Box leaf5638Box
    .k (99/32) (by rfl) (by rfl)
    leaf5637FlatSound leaf5638FlatSound

private noncomputable def component114Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (57/128), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component114Node4_sound : Sound component114Node4Box :=
  sound_of_literal_split component114Node4Box leaf5639Box leaf5640Box
    .k (99/32) (by rfl) (by rfl)
    leaf5639FlatSound leaf5640FlatSound

private noncomputable def component114Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (7/16), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component114Node5_sound : Sound component114Node5Box :=
  sound_of_literal_split component114Node5Box component114Node3Box component114Node4Box
    .chi (57/128) (by rfl) (by rfl)
    component114Node3_sound component114Node4_sound

private noncomputable def component114Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (7/16), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component114Node6_sound : Sound component114Node6Box :=
  sound_of_literal_split component114Node6Box component114Node2Box component114Node5Box
    .k (49/16) (by rfl) (by rfl)
    component114Node2_sound component114Node5_sound

private noncomputable def component114Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (29/64), chiHi := (59/128) }

set_option maxRecDepth 1000000 in
private theorem component114Node7_sound : Sound component114Node7Box :=
  sound_of_literal_split component114Node7Box leaf5641Box leaf5642Box
    .k (97/32) (by rfl) (by rfl)
    leaf5641FlatSound leaf5642FlatSound

private noncomputable def component114Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (59/128), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component114Node8_sound : Sound component114Node8Box :=
  sound_of_literal_split component114Node8Box leaf5643Box leaf5644Box
    .k (97/32) (by rfl) (by rfl)
    leaf5643FlatSound leaf5644FlatSound

private noncomputable def component114Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (29/64), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component114Node9_sound : Sound component114Node9Box :=
  sound_of_literal_split component114Node9Box component114Node7Box component114Node8Box
    .chi (59/128) (by rfl) (by rfl)
    component114Node7_sound component114Node8_sound

private noncomputable def component114Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (29/64), chiHi := (59/128) }

set_option maxRecDepth 1000000 in
private theorem component114Node10_sound : Sound component114Node10Box :=
  sound_of_literal_split component114Node10Box leaf5645Box leaf5646Box
    .k (99/32) (by rfl) (by rfl)
    leaf5645FlatSound leaf5646FlatSound

private noncomputable def component114Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (59/128), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component114Node11_sound : Sound component114Node11Box :=
  sound_of_literal_split component114Node11Box leaf5647Box leaf5648Box
    .k (99/32) (by rfl) (by rfl)
    leaf5647FlatSound leaf5648FlatSound

private noncomputable def component114Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (29/64), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component114Node12_sound : Sound component114Node12Box :=
  sound_of_literal_split component114Node12Box component114Node10Box component114Node11Box
    .chi (59/128) (by rfl) (by rfl)
    component114Node10_sound component114Node11_sound

private noncomputable def component114Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (29/64), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component114Node13_sound : Sound component114Node13Box :=
  sound_of_literal_split component114Node13Box component114Node9Box component114Node12Box
    .k (49/16) (by rfl) (by rfl)
    component114Node9_sound component114Node12_sound

private noncomputable def component114Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (7/16), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component114Node14_sound : Sound component114Node14Box :=
  sound_of_literal_split component114Node14Box component114Node6Box component114Node13Box
    .chi (29/64) (by rfl) (by rfl)
    component114Node6_sound component114Node13_sound

private noncomputable def component114Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (15/32), chiHi := (61/128) }

set_option maxRecDepth 1000000 in
private theorem component114Node15_sound : Sound component114Node15Box :=
  sound_of_literal_split component114Node15Box leaf5649Box leaf5650Box
    .k (97/32) (by rfl) (by rfl)
    leaf5649FlatSound leaf5650FlatSound

private noncomputable def component114Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (61/128), chiHi := (31/64) }

set_option maxRecDepth 1000000 in
private theorem component114Node16_sound : Sound component114Node16Box :=
  sound_of_literal_split component114Node16Box leaf5651Box leaf5652Box
    .k (97/32) (by rfl) (by rfl)
    leaf5651FlatSound leaf5652FlatSound

private noncomputable def component114Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (15/32), chiHi := (31/64) }

set_option maxRecDepth 1000000 in
private theorem component114Node17_sound : Sound component114Node17Box :=
  sound_of_literal_split component114Node17Box component114Node15Box component114Node16Box
    .chi (61/128) (by rfl) (by rfl)
    component114Node15_sound component114Node16_sound

private noncomputable def component114Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (15/32), chiHi := (61/128) }

set_option maxRecDepth 1000000 in
private theorem component114Node18_sound : Sound component114Node18Box :=
  sound_of_literal_split component114Node18Box leaf5653Box leaf5654Box
    .k (99/32) (by rfl) (by rfl)
    leaf5653FlatSound leaf5654FlatSound

private noncomputable def component114Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (61/128), chiHi := (31/64) }

set_option maxRecDepth 1000000 in
private theorem component114Node19_sound : Sound component114Node19Box :=
  sound_of_literal_split component114Node19Box leaf5655Box leaf5656Box
    .k (99/32) (by rfl) (by rfl)
    leaf5655FlatSound leaf5656FlatSound

private noncomputable def component114Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (15/32), chiHi := (31/64) }

set_option maxRecDepth 1000000 in
private theorem component114Node20_sound : Sound component114Node20Box :=
  sound_of_literal_split component114Node20Box component114Node18Box component114Node19Box
    .chi (61/128) (by rfl) (by rfl)
    component114Node18_sound component114Node19_sound

private noncomputable def component114Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (15/32), chiHi := (31/64) }

set_option maxRecDepth 1000000 in
private theorem component114Node21_sound : Sound component114Node21Box :=
  sound_of_literal_split component114Node21Box component114Node17Box component114Node20Box
    .k (49/16) (by rfl) (by rfl)
    component114Node17_sound component114Node20_sound

private noncomputable def component114Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (31/64), chiHi := (63/128) }

set_option maxRecDepth 1000000 in
private theorem component114Node22_sound : Sound component114Node22Box :=
  sound_of_literal_split component114Node22Box leaf5657Box leaf5658Box
    .k (97/32) (by rfl) (by rfl)
    leaf5657FlatSound leaf5658FlatSound

private noncomputable def component114Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (63/128), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component114Node23_sound : Sound component114Node23Box :=
  sound_of_literal_split component114Node23Box leaf5659Box leaf5660Box
    .k (97/32) (by rfl) (by rfl)
    leaf5659FlatSound leaf5660FlatSound

private noncomputable def component114Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (31/64), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component114Node24_sound : Sound component114Node24Box :=
  sound_of_literal_split component114Node24Box component114Node22Box component114Node23Box
    .chi (63/128) (by rfl) (by rfl)
    component114Node22_sound component114Node23_sound

private noncomputable def component114Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (31/64), chiHi := (63/128) }

set_option maxRecDepth 1000000 in
private theorem component114Node25_sound : Sound component114Node25Box :=
  sound_of_literal_split component114Node25Box leaf5661Box leaf5662Box
    .k (99/32) (by rfl) (by rfl)
    leaf5661FlatSound leaf5662FlatSound

private noncomputable def component114Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (63/128), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component114Node26_sound : Sound component114Node26Box :=
  sound_of_literal_split component114Node26Box leaf5663Box leaf5664Box
    .k (99/32) (by rfl) (by rfl)
    leaf5663FlatSound leaf5664FlatSound

private noncomputable def component114Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (31/64), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component114Node27_sound : Sound component114Node27Box :=
  sound_of_literal_split component114Node27Box component114Node25Box component114Node26Box
    .chi (63/128) (by rfl) (by rfl)
    component114Node25_sound component114Node26_sound

private noncomputable def component114Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (31/64), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component114Node28_sound : Sound component114Node28Box :=
  sound_of_literal_split component114Node28Box component114Node24Box component114Node27Box
    .k (49/16) (by rfl) (by rfl)
    component114Node24_sound component114Node27_sound

private noncomputable def component114Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (15/32), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component114Node29_sound : Sound component114Node29Box :=
  sound_of_literal_split component114Node29Box component114Node21Box component114Node28Box
    .chi (31/64) (by rfl) (by rfl)
    component114Node21_sound component114Node28_sound

private noncomputable def component114Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (7/16), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component114Node30_sound : Sound component114Node30Box :=
  sound_of_literal_split component114Node30Box component114Node14Box component114Node29Box
    .chi (15/32) (by rfl) (by rfl)
    component114Node14_sound component114Node29_sound

private noncomputable def component114Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (7/16), chiHi := (57/128) }

set_option maxRecDepth 1000000 in
private theorem component114Node31_sound : Sound component114Node31Box :=
  sound_of_literal_split component114Node31Box leaf5665Box leaf5666Box
    .k (101/32) (by rfl) (by rfl)
    leaf5665FlatSound leaf5666FlatSound

private noncomputable def component114Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (57/128), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component114Node32_sound : Sound component114Node32Box :=
  sound_of_literal_split component114Node32Box leaf5667Box leaf5668Box
    .k (101/32) (by rfl) (by rfl)
    leaf5667FlatSound leaf5668FlatSound

private noncomputable def component114Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (7/16), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component114Node33_sound : Sound component114Node33Box :=
  sound_of_literal_split component114Node33Box component114Node31Box component114Node32Box
    .chi (57/128) (by rfl) (by rfl)
    component114Node31_sound component114Node32_sound

private noncomputable def component114Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (7/16), chiHi := (57/128) }

set_option maxRecDepth 1000000 in
private theorem component114Node34_sound : Sound component114Node34Box :=
  sound_of_literal_split component114Node34Box leaf5669Box leaf5670Box
    .k (103/32) (by rfl) (by rfl)
    leaf5669FlatSound leaf5670FlatSound

private noncomputable def component114Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (57/128), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component114Node35_sound : Sound component114Node35Box :=
  sound_of_literal_split component114Node35Box leaf5671Box leaf5672Box
    .k (103/32) (by rfl) (by rfl)
    leaf5671FlatSound leaf5672FlatSound

private noncomputable def component114Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (7/16), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component114Node36_sound : Sound component114Node36Box :=
  sound_of_literal_split component114Node36Box component114Node34Box component114Node35Box
    .chi (57/128) (by rfl) (by rfl)
    component114Node34_sound component114Node35_sound

private noncomputable def component114Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (7/16), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component114Node37_sound : Sound component114Node37Box :=
  sound_of_literal_split component114Node37Box component114Node33Box component114Node36Box
    .k (51/16) (by rfl) (by rfl)
    component114Node33_sound component114Node36_sound

private noncomputable def component114Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (29/64), chiHi := (59/128) }

set_option maxRecDepth 1000000 in
private theorem component114Node38_sound : Sound component114Node38Box :=
  sound_of_literal_split component114Node38Box leaf5673Box leaf5674Box
    .k (101/32) (by rfl) (by rfl)
    leaf5673FlatSound leaf5674FlatSound

private noncomputable def component114Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (59/128), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component114Node39_sound : Sound component114Node39Box :=
  sound_of_literal_split component114Node39Box leaf5675Box leaf5676Box
    .k (101/32) (by rfl) (by rfl)
    leaf5675FlatSound leaf5676FlatSound

private noncomputable def component114Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (29/64), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component114Node40_sound : Sound component114Node40Box :=
  sound_of_literal_split component114Node40Box component114Node38Box component114Node39Box
    .chi (59/128) (by rfl) (by rfl)
    component114Node38_sound component114Node39_sound

private noncomputable def component114Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (29/64), chiHi := (59/128) }

set_option maxRecDepth 1000000 in
private theorem component114Node41_sound : Sound component114Node41Box :=
  sound_of_literal_split component114Node41Box leaf5677Box leaf5678Box
    .k (103/32) (by rfl) (by rfl)
    leaf5677FlatSound leaf5678FlatSound

private noncomputable def component114Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (59/128), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component114Node42_sound : Sound component114Node42Box :=
  sound_of_literal_split component114Node42Box leaf5679Box leaf5680Box
    .k (103/32) (by rfl) (by rfl)
    leaf5679FlatSound leaf5680FlatSound

private noncomputable def component114Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (29/64), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component114Node43_sound : Sound component114Node43Box :=
  sound_of_literal_split component114Node43Box component114Node41Box component114Node42Box
    .chi (59/128) (by rfl) (by rfl)
    component114Node41_sound component114Node42_sound

private noncomputable def component114Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (29/64), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component114Node44_sound : Sound component114Node44Box :=
  sound_of_literal_split component114Node44Box component114Node40Box component114Node43Box
    .k (51/16) (by rfl) (by rfl)
    component114Node40_sound component114Node43_sound

private noncomputable def component114Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (7/16), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component114Node45_sound : Sound component114Node45Box :=
  sound_of_literal_split component114Node45Box component114Node37Box component114Node44Box
    .chi (29/64) (by rfl) (by rfl)
    component114Node37_sound component114Node44_sound

private noncomputable def component114Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (15/32), chiHi := (61/128) }

set_option maxRecDepth 1000000 in
private theorem component114Node46_sound : Sound component114Node46Box :=
  sound_of_literal_split component114Node46Box leaf5681Box leaf5682Box
    .k (101/32) (by rfl) (by rfl)
    leaf5681FlatSound leaf5682FlatSound

private noncomputable def component114Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (61/128), chiHi := (31/64) }

set_option maxRecDepth 1000000 in
private theorem component114Node47_sound : Sound component114Node47Box :=
  sound_of_literal_split component114Node47Box leaf5683Box leaf5684Box
    .k (101/32) (by rfl) (by rfl)
    leaf5683FlatSound leaf5684FlatSound

private noncomputable def component114Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (15/32), chiHi := (31/64) }

set_option maxRecDepth 1000000 in
private theorem component114Node48_sound : Sound component114Node48Box :=
  sound_of_literal_split component114Node48Box component114Node46Box component114Node47Box
    .chi (61/128) (by rfl) (by rfl)
    component114Node46_sound component114Node47_sound

private noncomputable def component114Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (15/32), chiHi := (61/128) }

set_option maxRecDepth 1000000 in
private theorem component114Node49_sound : Sound component114Node49Box :=
  sound_of_literal_split component114Node49Box leaf5685Box leaf5686Box
    .k (103/32) (by rfl) (by rfl)
    leaf5685FlatSound leaf5686FlatSound

private noncomputable def component114Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (61/128), chiHi := (31/64) }

set_option maxRecDepth 1000000 in
private theorem component114Node50_sound : Sound component114Node50Box :=
  sound_of_literal_split component114Node50Box leaf5687Box leaf5688Box
    .k (103/32) (by rfl) (by rfl)
    leaf5687FlatSound leaf5688FlatSound

private noncomputable def component114Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (15/32), chiHi := (31/64) }

set_option maxRecDepth 1000000 in
private theorem component114Node51_sound : Sound component114Node51Box :=
  sound_of_literal_split component114Node51Box component114Node49Box component114Node50Box
    .chi (61/128) (by rfl) (by rfl)
    component114Node49_sound component114Node50_sound

private noncomputable def component114Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (15/32), chiHi := (31/64) }

set_option maxRecDepth 1000000 in
private theorem component114Node52_sound : Sound component114Node52Box :=
  sound_of_literal_split component114Node52Box component114Node48Box component114Node51Box
    .k (51/16) (by rfl) (by rfl)
    component114Node48_sound component114Node51_sound

private noncomputable def component114Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (31/64), chiHi := (63/128) }

set_option maxRecDepth 1000000 in
private theorem component114Node53_sound : Sound component114Node53Box :=
  sound_of_literal_split component114Node53Box leaf5689Box leaf5690Box
    .k (101/32) (by rfl) (by rfl)
    leaf5689FlatSound leaf5690FlatSound

private noncomputable def component114Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (63/128), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component114Node54_sound : Sound component114Node54Box :=
  sound_of_literal_split component114Node54Box leaf5691Box leaf5692Box
    .k (101/32) (by rfl) (by rfl)
    leaf5691FlatSound leaf5692FlatSound

private noncomputable def component114Node55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (31/64), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component114Node55_sound : Sound component114Node55Box :=
  sound_of_literal_split component114Node55Box component114Node53Box component114Node54Box
    .chi (63/128) (by rfl) (by rfl)
    component114Node53_sound component114Node54_sound

private noncomputable def component114Node56Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (31/64), chiHi := (63/128) }

set_option maxRecDepth 1000000 in
private theorem component114Node56_sound : Sound component114Node56Box :=
  sound_of_literal_split component114Node56Box leaf5693Box leaf5694Box
    .k (103/32) (by rfl) (by rfl)
    leaf5693FlatSound leaf5694FlatSound

private noncomputable def component114Node57Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (63/128), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component114Node57_sound : Sound component114Node57Box :=
  sound_of_literal_split component114Node57Box leaf5695Box leaf5696Box
    .k (103/32) (by rfl) (by rfl)
    leaf5695FlatSound leaf5696FlatSound

private noncomputable def component114Node58Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (31/64), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component114Node58_sound : Sound component114Node58Box :=
  sound_of_literal_split component114Node58Box component114Node56Box component114Node57Box
    .chi (63/128) (by rfl) (by rfl)
    component114Node56_sound component114Node57_sound

private noncomputable def component114Node59Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (31/64), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component114Node59_sound : Sound component114Node59Box :=
  sound_of_literal_split component114Node59Box component114Node55Box component114Node58Box
    .k (51/16) (by rfl) (by rfl)
    component114Node55_sound component114Node58_sound

private noncomputable def component114Node60Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (15/32), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component114Node60_sound : Sound component114Node60Box :=
  sound_of_literal_split component114Node60Box component114Node52Box component114Node59Box
    .chi (31/64) (by rfl) (by rfl)
    component114Node52_sound component114Node59_sound

private noncomputable def component114Node61Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (7/16), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component114Node61_sound : Sound component114Node61Box :=
  sound_of_literal_split component114Node61Box component114Node45Box component114Node60Box
    .chi (15/32) (by rfl) (by rfl)
    component114Node45_sound component114Node60_sound

noncomputable def component114Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (13/4), chiLo := (7/16), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
theorem component114_sound : Sound component114Box :=
  sound_of_literal_split component114Box component114Node30Box component114Node61Box
    .k (25/8) (by rfl) (by rfl)
    component114Node30_sound component114Node61_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
