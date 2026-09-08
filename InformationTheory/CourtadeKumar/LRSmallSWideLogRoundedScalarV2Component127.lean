import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch6
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch7
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch10
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch11
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch9
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheSKBatch1

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

private noncomputable def leaf6301Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (1/2), chiHi := (65/128) }

private noncomputable def leaf6301Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217947/134217728) }, vSqrt := { lower := (32765/32768), upper := (17179377663/17178371584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (318722855/268435456) }, upper := { exponent := 1, mantissa := (4973/4096) } }, logOuter := sk95LogOuterCertificate, logK := sk95LogKCertificate, logChi := chi329LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (34357749247/34356743168) } }, logDArg := sk95LogDArgCertificate }

private noncomputable def leaf6301InnerLog : WideLogData :=
  innerPair273Data

set_option maxRecDepth 1000000 in
private theorem leaf6301LocalValidity :
    LeafFacts leaf6301Box leaf6301Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6301Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (17179377663/17178371584) }) = true
      norm_num [leaf6301Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6301CertificateValid :
    WideCertificateValid leaf6301Box leaf6301Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk95ValidityFacts chi329ValidityFacts
    leaf6301LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6301CoverageChecked :
    coverageCheck (innerAD leaf6301Box) leaf6301InnerLog = true := by
  rfl'

private theorem leaf6301InnerLogValid :
    leaf6301InnerLog.Valid 8 (innerAD leaf6301Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint78PositiveFacts.valid leaf6301CoverageChecked

private noncomputable def leaf6301InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907393/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6301InputLogOnePlusV_eq :
    leaf6301InputLogOnePlusV = outerEnclosure 24
      (leaf6301Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6301RoundedFacts : LeafRoundedFacts 8
    leaf6301Certificate.logOnePlusV leaf6301InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6301InputLogOnePlusV_eq }

private noncomputable def leaf6301Inputs : Inputs :=
  inputsOfCaches globalInput sk95RoundedInputs
    chi329InputQChi innerPair273Input
    leaf6301InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6301LowerChecked :
    lowerCheck 24 leaf6301Box leaf6301Inputs = true := by
  rfl'

private theorem leaf6301CoversExact : CoversExact 8
    leaf6301Box leaf6301Certificate leaf6301InnerLog leaf6301Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk95RoundedFacts chi329RoundedFacts
    innerPair273RoundedFacts leaf6301RoundedFacts (by rfl)

private theorem leaf6301FlatSound : Sound leaf6301Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6301CertificateValid
    leaf6301InnerLogValid leaf6301CoversExact leaf6301LowerChecked

private noncomputable def leaf6302Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (65/128), chiHi := (33/64) }

private noncomputable def leaf6302Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217949/134217728) }, vSqrt := { lower := (32765/32768), upper := (2454196809/2454049792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (321606261/268435456) }, upper := { exponent := 1, mantissa := (2509/2048) } }, logOuter := sk95LogOuterCertificate, logK := sk95LogKCertificate, logChi := chi330LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (4908246601/4908099584) } }, logDArg := sk95LogDArgCertificate }

private noncomputable def leaf6302InnerLog : WideLogData :=
  innerPair586Data

set_option maxRecDepth 1000000 in
private theorem leaf6302LocalValidity :
    LeafFacts leaf6302Box leaf6302Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6302Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (2454196809/2454049792) }) = true
      norm_num [leaf6302Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6302CertificateValid :
    WideCertificateValid leaf6302Box leaf6302Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk95ValidityFacts chi330ValidityFacts
    leaf6302LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6302CoverageChecked :
    coverageCheck (innerAD leaf6302Box) leaf6302InnerLog = true := by
  rfl'

private theorem leaf6302InnerLogValid :
    leaf6302InnerLog.Valid 8 (innerAD leaf6302Box) :=
  wideLogDataValid_of_cachedCheck endpoint304PositiveFacts
    endpoint403PositiveFacts.valid leaf6302CoverageChecked

private noncomputable def leaf6302InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629583/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6302InputLogOnePlusV_eq :
    leaf6302InputLogOnePlusV = outerEnclosure 24
      (leaf6302Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6302RoundedFacts : LeafRoundedFacts 8
    leaf6302Certificate.logOnePlusV leaf6302InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6302InputLogOnePlusV_eq }

private noncomputable def leaf6302Inputs : Inputs :=
  inputsOfCaches globalInput sk95RoundedInputs
    chi330InputQChi innerPair586Input
    leaf6302InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6302LowerChecked :
    lowerCheck 24 leaf6302Box leaf6302Inputs = true := by
  rfl'

private theorem leaf6302CoversExact : CoversExact 8
    leaf6302Box leaf6302Certificate leaf6302InnerLog leaf6302Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk95RoundedFacts chi330RoundedFacts
    innerPair586RoundedFacts leaf6302RoundedFacts (by rfl)

private theorem leaf6302FlatSound : Sound leaf6302Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6302CertificateValid
    leaf6302InnerLogValid leaf6302CoversExact leaf6302LowerChecked

private noncomputable def leaf6303Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (33/64), chiHi := (67/128) }

private noncomputable def leaf6303Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217951/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34356651008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (324489667/268435456) }, upper := { exponent := 1, mantissa := (5063/4096) } }, logOuter := sk95LogOuterCertificate, logK := sk95LogKCertificate, logChi := chi331LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714882045/68713302016) } }, logDArg := sk95LogDArgCertificate }

private noncomputable def leaf6303InnerLog : WideLogData :=
  innerPair279Data

set_option maxRecDepth 1000000 in
private theorem leaf6303LocalValidity :
    LeafFacts leaf6303Box leaf6303Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6303Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34356651008) }) = true
      norm_num [leaf6303Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6303CertificateValid :
    WideCertificateValid leaf6303Box leaf6303Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk95ValidityFacts chi331ValidityFacts
    leaf6303LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6303CoverageChecked :
    coverageCheck (innerAD leaf6303Box) leaf6303InnerLog = true := by
  rfl'

private theorem leaf6303InnerLogValid :
    leaf6303InnerLog.Valid 8 (innerAD leaf6303Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint79PositiveFacts.valid leaf6303CoverageChecked

private noncomputable def leaf6303InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629467/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6303InputLogOnePlusV_eq :
    leaf6303InputLogOnePlusV = outerEnclosure 24
      (leaf6303Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6303RoundedFacts : LeafRoundedFacts 8
    leaf6303Certificate.logOnePlusV leaf6303InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6303InputLogOnePlusV_eq }

private noncomputable def leaf6303Inputs : Inputs :=
  inputsOfCaches globalInput sk95RoundedInputs
    chi331InputQChi innerPair279Input
    leaf6303InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6303LowerChecked :
    lowerCheck 24 leaf6303Box leaf6303Inputs = true := by
  rfl'

private theorem leaf6303CoversExact : CoversExact 8
    leaf6303Box leaf6303Certificate leaf6303InnerLog leaf6303Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk95RoundedFacts chi331RoundedFacts
    innerPair279RoundedFacts leaf6303RoundedFacts (by rfl)

private theorem leaf6303FlatSound : Sound leaf6303Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6303CertificateValid
    leaf6303InnerLogValid leaf6303CoversExact leaf6303LowerChecked

private noncomputable def leaf6304Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (67/128), chiHi := (17/32) }

private noncomputable def leaf6304Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217953/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34356604928) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (327373073/268435456) }, upper := { exponent := 1, mantissa := (1277/1024) } }, logOuter := sk95LogOuterCertificate, logK := sk95LogKCertificate, logChi := chi332LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714835965/68713209856) } }, logDArg := sk95LogDArgCertificate }

private noncomputable def leaf6304InnerLog : WideLogData :=
  innerPair285Data

set_option maxRecDepth 1000000 in
private theorem leaf6304LocalValidity :
    LeafFacts leaf6304Box leaf6304Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6304Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34356604928) }) = true
      norm_num [leaf6304Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6304CertificateValid :
    WideCertificateValid leaf6304Box leaf6304Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk95ValidityFacts chi332ValidityFacts
    leaf6304LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6304CoverageChecked :
    coverageCheck (innerAD leaf6304Box) leaf6304InnerLog = true := by
  rfl'

private theorem leaf6304InnerLogValid :
    leaf6304InnerLog.Valid 8 (innerAD leaf6304Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint79PositiveFacts.valid leaf6304CoverageChecked

private noncomputable def leaf6304InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814739/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6304InputLogOnePlusV_eq :
    leaf6304InputLogOnePlusV = outerEnclosure 24
      (leaf6304Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6304RoundedFacts : LeafRoundedFacts 8
    leaf6304Certificate.logOnePlusV leaf6304InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6304InputLogOnePlusV_eq }

private noncomputable def leaf6304Inputs : Inputs :=
  inputsOfCaches globalInput sk95RoundedInputs
    chi332InputQChi innerPair285Input
    leaf6304InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6304LowerChecked :
    lowerCheck 24 leaf6304Box leaf6304Inputs = true := by
  rfl'

private theorem leaf6304CoversExact : CoversExact 8
    leaf6304Box leaf6304Certificate leaf6304InnerLog leaf6304Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk95RoundedFacts chi332RoundedFacts
    innerPair285RoundedFacts leaf6304RoundedFacts (by rfl)

private theorem leaf6304FlatSound : Sound leaf6304Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6304CertificateValid
    leaf6304InnerLogValid leaf6304CoversExact leaf6304LowerChecked

private noncomputable def leaf6305Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (1/2), chiHi := (65/128) }

private noncomputable def leaf6305Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217949/134217728) }, vSqrt := { lower := (32765/32768), upper := (5726459221/5726112768) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (322916901/268435456) }, upper := { exponent := 1, mantissa := (2519/2048) } }, logOuter := sk96LogOuterCertificate, logK := sk96LogKCertificate, logChi := chi329LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (11452571989/11452225536) } }, logDArg := sk96LogDArgCertificate }

private noncomputable def leaf6305InnerLog : WideLogData :=
  innerPair584Data

set_option maxRecDepth 1000000 in
private theorem leaf6305LocalValidity :
    LeafFacts leaf6305Box leaf6305Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6305Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (5726459221/5726112768) }) = true
      norm_num [leaf6305Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6305CertificateValid :
    WideCertificateValid leaf6305Box leaf6305Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk96ValidityFacts chi329ValidityFacts
    leaf6305LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6305CoverageChecked :
    coverageCheck (innerAD leaf6305Box) leaf6305InnerLog = true := by
  rfl'

private theorem leaf6305InnerLogValid :
    leaf6305InnerLog.Valid 8 (innerAD leaf6305Box) :=
  wideLogDataValid_of_cachedCheck endpoint304PositiveFacts
    endpoint94PositiveFacts.valid leaf6305CoverageChecked

private noncomputable def leaf6305InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907397/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6305InputLogOnePlusV_eq :
    leaf6305InputLogOnePlusV = outerEnclosure 24
      (leaf6305Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6305RoundedFacts : LeafRoundedFacts 8
    leaf6305Certificate.logOnePlusV leaf6305InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6305InputLogOnePlusV_eq }

private noncomputable def leaf6305Inputs : Inputs :=
  inputsOfCaches globalInput sk96RoundedInputs
    chi329InputQChi innerPair584Input
    leaf6305InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6305LowerChecked :
    lowerCheck 24 leaf6305Box leaf6305Inputs = true := by
  rfl'

private theorem leaf6305CoversExact : CoversExact 8
    leaf6305Box leaf6305Certificate leaf6305InnerLog leaf6305Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk96RoundedFacts chi329RoundedFacts
    innerPair584RoundedFacts leaf6305RoundedFacts (by rfl)

private theorem leaf6305FlatSound : Sound leaf6305Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6305CertificateValid
    leaf6305InnerLogValid leaf6305CoversExact leaf6305LowerChecked

private noncomputable def leaf6306Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (65/128), chiHi := (33/64) }

private noncomputable def leaf6306Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217951/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34356629504) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (325865839/268435456) }, upper := { exponent := 1, mantissa := (1271/1024) } }, logOuter := sk96LogOuterCertificate, logK := sk96LogKCertificate, logChi := chi330LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714860541/68713259008) } }, logDArg := sk96LogDArgCertificate }

private noncomputable def leaf6306InnerLog : WideLogData :=
  innerPair279Data

set_option maxRecDepth 1000000 in
private theorem leaf6306LocalValidity :
    LeafFacts leaf6306Box leaf6306Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6306Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34356629504) }) = true
      norm_num [leaf6306Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6306CertificateValid :
    WideCertificateValid leaf6306Box leaf6306Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk96ValidityFacts chi330ValidityFacts
    leaf6306LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6306CoverageChecked :
    coverageCheck (innerAD leaf6306Box) leaf6306InnerLog = true := by
  rfl'

private theorem leaf6306InnerLogValid :
    leaf6306InnerLog.Valid 8 (innerAD leaf6306Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint79PositiveFacts.valid leaf6306CoverageChecked

private noncomputable def leaf6306InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (363421/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf6306InputLogOnePlusV_eq :
    leaf6306InputLogOnePlusV = outerEnclosure 24
      (leaf6306Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6306RoundedFacts : LeafRoundedFacts 8
    leaf6306Certificate.logOnePlusV leaf6306InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6306InputLogOnePlusV_eq }

private noncomputable def leaf6306Inputs : Inputs :=
  inputsOfCaches globalInput sk96RoundedInputs
    chi330InputQChi innerPair279Input
    leaf6306InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6306LowerChecked :
    lowerCheck 24 leaf6306Box leaf6306Inputs = true := by
  rfl'

private theorem leaf6306CoversExact : CoversExact 8
    leaf6306Box leaf6306Certificate leaf6306InnerLog leaf6306Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk96RoundedFacts chi330RoundedFacts
    innerPair279RoundedFacts leaf6306RoundedFacts (by rfl)

private theorem leaf6306FlatSound : Sound leaf6306Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6306CertificateValid
    leaf6306InnerLogValid leaf6306CoversExact leaf6306LowerChecked

private noncomputable def leaf6307Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (33/64), chiHi := (67/128) }

private noncomputable def leaf6307Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217953/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34356582400) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (328814777/268435456) }, upper := { exponent := 1, mantissa := (2565/2048) } }, logOuter := sk96LogOuterCertificate, logK := sk96LogKCertificate, logChi := chi331LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714813437/68713164800) } }, logDArg := sk96LogDArgCertificate }

private noncomputable def leaf6307InnerLog : WideLogData :=
  innerPair291Data

set_option maxRecDepth 1000000 in
private theorem leaf6307LocalValidity :
    LeafFacts leaf6307Box leaf6307Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6307Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34356582400) }) = true
      norm_num [leaf6307Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6307CertificateValid :
    WideCertificateValid leaf6307Box leaf6307Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk96ValidityFacts chi331ValidityFacts
    leaf6307LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6307CoverageChecked :
    coverageCheck (innerAD leaf6307Box) leaf6307InnerLog = true := by
  rfl'

private theorem leaf6307InnerLogValid :
    leaf6307InnerLog.Valid 8 (innerAD leaf6307Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint419PositiveFacts.valid leaf6307CoverageChecked

private noncomputable def leaf6307InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629483/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6307InputLogOnePlusV_eq :
    leaf6307InputLogOnePlusV = outerEnclosure 24
      (leaf6307Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6307RoundedFacts : LeafRoundedFacts 8
    leaf6307Certificate.logOnePlusV leaf6307InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6307InputLogOnePlusV_eq }

private noncomputable def leaf6307Inputs : Inputs :=
  inputsOfCaches globalInput sk96RoundedInputs
    chi331InputQChi innerPair291Input
    leaf6307InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6307LowerChecked :
    lowerCheck 24 leaf6307Box leaf6307Inputs = true := by
  rfl'

private theorem leaf6307CoversExact : CoversExact 8
    leaf6307Box leaf6307Certificate leaf6307InnerLog leaf6307Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk96RoundedFacts chi331RoundedFacts
    innerPair291RoundedFacts leaf6307RoundedFacts (by rfl)

private theorem leaf6307FlatSound : Sound leaf6307Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6307CertificateValid
    leaf6307InnerLogValid leaf6307CoversExact leaf6307LowerChecked

private noncomputable def leaf6308Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (67/128), chiHi := (17/32) }

private noncomputable def leaf6308Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217955/134217728) }, vSqrt := { lower := (32765/32768), upper := (11452743679/11452178432) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (331763715/268435456) }, upper := { exponent := 1, mantissa := (647/512) } }, logOuter := sk96LogOuterCertificate, logK := sk96LogKCertificate, logChi := chi332LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (22904922111/22904356864) } }, logDArg := sk96LogDArgCertificate }

private noncomputable def leaf6308InnerLog : WideLogData :=
  innerPair286Data

set_option maxRecDepth 1000000 in
private theorem leaf6308LocalValidity :
    LeafFacts leaf6308Box leaf6308Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6308Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (11452743679/11452178432) }) = true
      norm_num [leaf6308Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6308CertificateValid :
    WideCertificateValid leaf6308Box leaf6308Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk96ValidityFacts chi332ValidityFacts
    leaf6308LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6308CoverageChecked :
    coverageCheck (innerAD leaf6308Box) leaf6308InnerLog = true := by
  rfl'

private theorem leaf6308InnerLogValid :
    leaf6308InnerLog.Valid 8 (innerAD leaf6308Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint90PositiveFacts.valid leaf6308CoverageChecked

private noncomputable def leaf6308InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629495/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6308InputLogOnePlusV_eq :
    leaf6308InputLogOnePlusV = outerEnclosure 24
      (leaf6308Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6308RoundedFacts : LeafRoundedFacts 8
    leaf6308Certificate.logOnePlusV leaf6308InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6308InputLogOnePlusV_eq }

private noncomputable def leaf6308Inputs : Inputs :=
  inputsOfCaches globalInput sk96RoundedInputs
    chi332InputQChi innerPair286Input
    leaf6308InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6308LowerChecked :
    lowerCheck 24 leaf6308Box leaf6308Inputs = true := by
  rfl'

private theorem leaf6308CoversExact : CoversExact 8
    leaf6308Box leaf6308Certificate leaf6308InnerLog leaf6308Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk96RoundedFacts chi332RoundedFacts
    innerPair286RoundedFacts leaf6308RoundedFacts (by rfl)

private theorem leaf6308FlatSound : Sound leaf6308Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6308CertificateValid
    leaf6308InnerLogValid leaf6308CoversExact leaf6308LowerChecked

private noncomputable def leaf6309Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (17/32), chiHi := (69/128) }

private noncomputable def leaf6309Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217955/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34356558848) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (330256479/268435456) }, upper := { exponent := 1, mantissa := (5153/4096) } }, logOuter := sk95LogOuterCertificate, logK := sk95LogKCertificate, logChi := chi327LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714789885/68713117696) } }, logDArg := sk95LogDArgCertificate }

private noncomputable def leaf6309InnerLog : WideLogData :=
  innerPair286Data

set_option maxRecDepth 1000000 in
private theorem leaf6309LocalValidity :
    LeafFacts leaf6309Box leaf6309Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6309Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34356558848) }) = true
      norm_num [leaf6309Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6309CertificateValid :
    WideCertificateValid leaf6309Box leaf6309Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk95ValidityFacts chi327ValidityFacts
    leaf6309LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6309CoverageChecked :
    coverageCheck (innerAD leaf6309Box) leaf6309InnerLog = true := by
  rfl'

private theorem leaf6309InnerLogValid :
    leaf6309InnerLog.Valid 8 (innerAD leaf6309Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint90PositiveFacts.valid leaf6309CoverageChecked

private noncomputable def leaf6309InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629489/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6309InputLogOnePlusV_eq :
    leaf6309InputLogOnePlusV = outerEnclosure 24
      (leaf6309Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6309RoundedFacts : LeafRoundedFacts 8
    leaf6309Certificate.logOnePlusV leaf6309InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6309InputLogOnePlusV_eq }

private noncomputable def leaf6309Inputs : Inputs :=
  inputsOfCaches globalInput sk95RoundedInputs
    chi327InputQChi innerPair286Input
    leaf6309InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6309LowerChecked :
    lowerCheck 24 leaf6309Box leaf6309Inputs = true := by
  rfl'

private theorem leaf6309CoversExact : CoversExact 8
    leaf6309Box leaf6309Certificate leaf6309InnerLog leaf6309Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk95RoundedFacts chi327RoundedFacts
    innerPair286RoundedFacts leaf6309RoundedFacts (by rfl)

private theorem leaf6309FlatSound : Sound leaf6309Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6309CertificateValid
    leaf6309InnerLogValid leaf6309CoversExact leaf6309LowerChecked

private noncomputable def leaf6310Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (69/128), chiHi := (35/64) }

private noncomputable def leaf6310Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217957/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34356512768) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (333139885/268435456) }, upper := { exponent := 1, mantissa := (2599/2048) } }, logOuter := sk95LogOuterCertificate, logK := sk95LogKCertificate, logChi := chi328LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714743805/68713025536) } }, logDArg := sk95LogDArgCertificate }

private noncomputable def leaf6310InnerLog : WideLogData :=
  innerPair286Data

set_option maxRecDepth 1000000 in
private theorem leaf6310LocalValidity :
    LeafFacts leaf6310Box leaf6310Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6310Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34356512768) }) = true
      norm_num [leaf6310Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6310CertificateValid :
    WideCertificateValid leaf6310Box leaf6310Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk95ValidityFacts chi328ValidityFacts
    leaf6310LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6310CoverageChecked :
    coverageCheck (innerAD leaf6310Box) leaf6310InnerLog = true := by
  rfl'

private theorem leaf6310InnerLogValid :
    leaf6310InnerLog.Valid 8 (innerAD leaf6310Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint90PositiveFacts.valid leaf6310CoverageChecked

private noncomputable def leaf6310InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907375/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6310InputLogOnePlusV_eq :
    leaf6310InputLogOnePlusV = outerEnclosure 24
      (leaf6310Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6310RoundedFacts : LeafRoundedFacts 8
    leaf6310Certificate.logOnePlusV leaf6310InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6310InputLogOnePlusV_eq }

private noncomputable def leaf6310Inputs : Inputs :=
  inputsOfCaches globalInput sk95RoundedInputs
    chi328InputQChi innerPair286Input
    leaf6310InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6310LowerChecked :
    lowerCheck 24 leaf6310Box leaf6310Inputs = true := by
  rfl'

private theorem leaf6310CoversExact : CoversExact 8
    leaf6310Box leaf6310Certificate leaf6310InnerLog leaf6310Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk95RoundedFacts chi328RoundedFacts
    innerPair286RoundedFacts leaf6310RoundedFacts (by rfl)

private theorem leaf6310FlatSound : Sound leaf6310Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6310CertificateValid
    leaf6310InnerLogValid leaf6310CoversExact leaf6310LowerChecked

private noncomputable def leaf6311Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (35/64), chiHi := (71/128) }

private noncomputable def leaf6311Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217959/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34356466688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (336023291/268435456) }, upper := { exponent := 1, mantissa := (5243/4096) } }, logOuter := sk95LogOuterCertificate, logK := sk95LogKCertificate, logChi := chi333LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714697725/68712933376) } }, logDArg := sk95LogDArgCertificate }

private noncomputable def leaf6311InnerLog : WideLogData :=
  innerPair293Data

set_option maxRecDepth 1000000 in
private theorem leaf6311LocalValidity :
    LeafFacts leaf6311Box leaf6311Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6311Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34356466688) }) = true
      norm_num [leaf6311Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6311CertificateValid :
    WideCertificateValid leaf6311Box leaf6311Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk95ValidityFacts chi333ValidityFacts
    leaf6311LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6311CoverageChecked :
    coverageCheck (innerAD leaf6311Box) leaf6311InnerLog = true := by
  rfl'

private theorem leaf6311InnerLogValid :
    leaf6311InnerLog.Valid 8 (innerAD leaf6311Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint90PositiveFacts.valid leaf6311CoverageChecked

private noncomputable def leaf6311InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453689/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf6311InputLogOnePlusV_eq :
    leaf6311InputLogOnePlusV = outerEnclosure 24
      (leaf6311Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6311RoundedFacts : LeafRoundedFacts 8
    leaf6311Certificate.logOnePlusV leaf6311InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6311InputLogOnePlusV_eq }

private noncomputable def leaf6311Inputs : Inputs :=
  inputsOfCaches globalInput sk95RoundedInputs
    chi333InputQChi innerPair293Input
    leaf6311InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6311LowerChecked :
    lowerCheck 24 leaf6311Box leaf6311Inputs = true := by
  rfl'

private theorem leaf6311CoversExact : CoversExact 8
    leaf6311Box leaf6311Certificate leaf6311InnerLog leaf6311Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk95RoundedFacts chi333RoundedFacts
    innerPair293RoundedFacts leaf6311RoundedFacts (by rfl)

private theorem leaf6311FlatSound : Sound leaf6311Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6311CertificateValid
    leaf6311InnerLogValid leaf6311CoversExact leaf6311LowerChecked

private noncomputable def leaf6312Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (71/128), chiHi := (9/16) }

private noncomputable def leaf6312Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217961/134217728) }, vSqrt := { lower := (32765/32768), upper := (483918747/483893248) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (338906697/268435456) }, upper := { exponent := 1, mantissa := (661/512) } }, logOuter := sk95LogOuterCertificate, logK := sk95LogKCertificate, logChi := chi334LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (967811995/967786496) } }, logDArg := sk95LogDArgCertificate }

private noncomputable def leaf6312InnerLog : WideLogData :=
  innerPair294Data

set_option maxRecDepth 1000000 in
private theorem leaf6312LocalValidity :
    LeafFacts leaf6312Box leaf6312Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6312Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (483918747/483893248) }) = true
      norm_num [leaf6312Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6312CertificateValid :
    WideCertificateValid leaf6312Box leaf6312Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk95ValidityFacts chi334ValidityFacts
    leaf6312LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6312CoverageChecked :
    coverageCheck (innerAD leaf6312Box) leaf6312InnerLog = true := by
  rfl'

private theorem leaf6312InnerLogValid :
    leaf6312InnerLog.Valid 8 (innerAD leaf6312Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint91PositiveFacts.valid leaf6312CoverageChecked

private noncomputable def leaf6312InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629523/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6312InputLogOnePlusV_eq :
    leaf6312InputLogOnePlusV = outerEnclosure 24
      (leaf6312Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6312RoundedFacts : LeafRoundedFacts 8
    leaf6312Certificate.logOnePlusV leaf6312InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6312InputLogOnePlusV_eq }

private noncomputable def leaf6312Inputs : Inputs :=
  inputsOfCaches globalInput sk95RoundedInputs
    chi334InputQChi innerPair294Input
    leaf6312InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6312LowerChecked :
    lowerCheck 24 leaf6312Box leaf6312Inputs = true := by
  rfl'

private theorem leaf6312CoversExact : CoversExact 8
    leaf6312Box leaf6312Certificate leaf6312InnerLog leaf6312Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk95RoundedFacts chi334RoundedFacts
    innerPair294RoundedFacts leaf6312RoundedFacts (by rfl)

private theorem leaf6312FlatSound : Sound leaf6312Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6312CertificateValid
    leaf6312InnerLogValid leaf6312CoversExact leaf6312LowerChecked

private noncomputable def leaf6313Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (17/32), chiHi := (69/128) }

private noncomputable def leaf6313Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217957/134217728) }, vSqrt := { lower := (32765/32768), upper := (2642940849/2642806784) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (334712653/268435456) }, upper := { exponent := 1, mantissa := (2611/2048) } }, logOuter := sk96LogOuterCertificate, logK := sk96LogKCertificate, logChi := chi327LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (5285747633/5285613568) } }, logDArg := sk96LogDArgCertificate }

private noncomputable def leaf6313InnerLog : WideLogData :=
  innerPair286Data

set_option maxRecDepth 1000000 in
private theorem leaf6313LocalValidity :
    LeafFacts leaf6313Box leaf6313Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6313Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (2642940849/2642806784) }) = true
      norm_num [leaf6313Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6313CertificateValid :
    WideCertificateValid leaf6313Box leaf6313Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk96ValidityFacts chi327ValidityFacts
    leaf6313LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6313CoverageChecked :
    coverageCheck (innerAD leaf6313Box) leaf6313InnerLog = true := by
  rfl'

private theorem leaf6313InnerLogValid :
    leaf6313InnerLog.Valid 8 (innerAD leaf6313Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint90PositiveFacts.valid leaf6313CoverageChecked

private noncomputable def leaf6313InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814753/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6313InputLogOnePlusV_eq :
    leaf6313InputLogOnePlusV = outerEnclosure 24
      (leaf6313Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6313RoundedFacts : LeafRoundedFacts 8
    leaf6313Certificate.logOnePlusV leaf6313InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6313InputLogOnePlusV_eq }

private noncomputable def leaf6313Inputs : Inputs :=
  inputsOfCaches globalInput sk96RoundedInputs
    chi327InputQChi innerPair286Input
    leaf6313InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6313LowerChecked :
    lowerCheck 24 leaf6313Box leaf6313Inputs = true := by
  rfl'

private theorem leaf6313CoversExact : CoversExact 8
    leaf6313Box leaf6313Certificate leaf6313InnerLog leaf6313Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk96RoundedFacts chi327RoundedFacts
    innerPair286RoundedFacts leaf6313RoundedFacts (by rfl)

private theorem leaf6313FlatSound : Sound leaf6313Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6313CertificateValid
    leaf6313InnerLogValid leaf6313CoversExact leaf6313LowerChecked

private noncomputable def leaf6314Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (69/128), chiHi := (35/64) }

private noncomputable def leaf6314Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217959/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34356441088) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (337661591/268435456) }, upper := { exponent := 1, mantissa := (1317/1024) } }, logOuter := sk96LogOuterCertificate, logK := sk96LogKCertificate, logChi := chi328LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714672125/68712882176) } }, logDArg := sk96LogDArgCertificate }

private noncomputable def leaf6314InnerLog : WideLogData :=
  innerPair671Data

set_option maxRecDepth 1000000 in
private theorem leaf6314LocalValidity :
    LeafFacts leaf6314Box leaf6314Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6314Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34356441088) }) = true
      norm_num [leaf6314Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6314CertificateValid :
    WideCertificateValid leaf6314Box leaf6314Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk96ValidityFacts chi328ValidityFacts
    leaf6314LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6314CoverageChecked :
    coverageCheck (innerAD leaf6314Box) leaf6314InnerLog = true := by
  rfl'

private theorem leaf6314InnerLogValid :
    leaf6314InnerLog.Valid 8 (innerAD leaf6314Box) :=
  wideLogDataValid_of_cachedCheck endpoint419PositiveFacts
    endpoint435PositiveFacts.valid leaf6314CoverageChecked

private noncomputable def leaf6314InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814759/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6314InputLogOnePlusV_eq :
    leaf6314InputLogOnePlusV = outerEnclosure 24
      (leaf6314Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6314RoundedFacts : LeafRoundedFacts 8
    leaf6314Certificate.logOnePlusV leaf6314InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6314InputLogOnePlusV_eq }

private noncomputable def leaf6314Inputs : Inputs :=
  inputsOfCaches globalInput sk96RoundedInputs
    chi328InputQChi innerPair671Input
    leaf6314InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6314LowerChecked :
    lowerCheck 24 leaf6314Box leaf6314Inputs = true := by
  rfl'

private theorem leaf6314CoversExact : CoversExact 8
    leaf6314Box leaf6314Certificate leaf6314InnerLog leaf6314Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk96RoundedFacts chi328RoundedFacts
    innerPair671RoundedFacts leaf6314RoundedFacts (by rfl)

private theorem leaf6314FlatSound : Sound leaf6314Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6314CertificateValid
    leaf6314InnerLogValid leaf6314CoversExact leaf6314LowerChecked

private noncomputable def leaf6315Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (35/64), chiHi := (71/128) }

private noncomputable def leaf6315Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217961/134217728) }, vSqrt := { lower := (32765/32768), upper := (11452743679/11452131328) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (340610529/268435456) }, upper := { exponent := 1, mantissa := (2657/2048) } }, logOuter := sk96LogOuterCertificate, logK := sk96LogKCertificate, logChi := chi333LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (22904875007/22904262656) } }, logDArg := sk96LogDArgCertificate }

private noncomputable def leaf6315InnerLog : WideLogData :=
  innerPair294Data

set_option maxRecDepth 1000000 in
private theorem leaf6315LocalValidity :
    LeafFacts leaf6315Box leaf6315Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6315Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (11452743679/11452131328) }) = true
      norm_num [leaf6315Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6315CertificateValid :
    WideCertificateValid leaf6315Box leaf6315Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk96ValidityFacts chi333ValidityFacts
    leaf6315LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6315CoverageChecked :
    coverageCheck (innerAD leaf6315Box) leaf6315InnerLog = true := by
  rfl'

private theorem leaf6315InnerLogValid :
    leaf6315InnerLog.Valid 8 (innerAD leaf6315Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint91PositiveFacts.valid leaf6315CoverageChecked

private noncomputable def leaf6315InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629529/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6315InputLogOnePlusV_eq :
    leaf6315InputLogOnePlusV = outerEnclosure 24
      (leaf6315Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6315RoundedFacts : LeafRoundedFacts 8
    leaf6315Certificate.logOnePlusV leaf6315InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6315InputLogOnePlusV_eq }

private noncomputable def leaf6315Inputs : Inputs :=
  inputsOfCaches globalInput sk96RoundedInputs
    chi333InputQChi innerPair294Input
    leaf6315InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6315LowerChecked :
    lowerCheck 24 leaf6315Box leaf6315Inputs = true := by
  rfl'

private theorem leaf6315CoversExact : CoversExact 8
    leaf6315Box leaf6315Certificate leaf6315InnerLog leaf6315Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk96RoundedFacts chi333RoundedFacts
    innerPair294RoundedFacts leaf6315RoundedFacts (by rfl)

private theorem leaf6315FlatSound : Sound leaf6315Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6315CertificateValid
    leaf6315InnerLogValid leaf6315CoversExact leaf6315LowerChecked

private noncomputable def leaf6316Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (71/128), chiHi := (9/16) }

private noncomputable def leaf6316Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217963/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34356346880) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (343559467/268435456) }, upper := { exponent := 1, mantissa := (335/256) } }, logOuter := sk96LogOuterCertificate, logK := sk96LogKCertificate, logChi := chi334LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714577917/68712693760) } }, logDArg := sk96LogDArgCertificate }

private noncomputable def leaf6316InnerLog : WideLogData :=
  innerPair294Data

set_option maxRecDepth 1000000 in
private theorem leaf6316LocalValidity :
    LeafFacts leaf6316Box leaf6316Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6316Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34356346880) }) = true
      norm_num [leaf6316Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6316CertificateValid :
    WideCertificateValid leaf6316Box leaf6316Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk96ValidityFacts chi334ValidityFacts
    leaf6316LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6316CoverageChecked :
    coverageCheck (innerAD leaf6316Box) leaf6316InnerLog = true := by
  rfl'

private theorem leaf6316InnerLogValid :
    leaf6316InnerLog.Valid 8 (innerAD leaf6316Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint91PositiveFacts.valid leaf6316CoverageChecked

private noncomputable def leaf6316InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629541/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6316InputLogOnePlusV_eq :
    leaf6316InputLogOnePlusV = outerEnclosure 24
      (leaf6316Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6316RoundedFacts : LeafRoundedFacts 8
    leaf6316Certificate.logOnePlusV leaf6316InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6316InputLogOnePlusV_eq }

private noncomputable def leaf6316Inputs : Inputs :=
  inputsOfCaches globalInput sk96RoundedInputs
    chi334InputQChi innerPair294Input
    leaf6316InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6316LowerChecked :
    lowerCheck 24 leaf6316Box leaf6316Inputs = true := by
  rfl'

private theorem leaf6316CoversExact : CoversExact 8
    leaf6316Box leaf6316Certificate leaf6316InnerLog leaf6316Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk96RoundedFacts chi334RoundedFacts
    innerPair294RoundedFacts leaf6316RoundedFacts (by rfl)

private theorem leaf6316FlatSound : Sound leaf6316Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6316CertificateValid
    leaf6316InnerLogValid leaf6316CoversExact leaf6316LowerChecked

private noncomputable def leaf6317Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (1/2), chiHi := (65/128) }

private noncomputable def leaf6317Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217951/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34356610048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (327110947/268435456) }, upper := { exponent := 1, mantissa := (5103/4096) } }, logOuter := sk97LogOuterCertificate, logK := sk97LogKCertificate, logChi := chi329LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714841085/68713220096) } }, logDArg := sk97LogDArgCertificate }

private noncomputable def leaf6317InnerLog : WideLogData :=
  innerPair279Data

set_option maxRecDepth 1000000 in
private theorem leaf6317LocalValidity :
    LeafFacts leaf6317Box leaf6317Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6317Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34356610048) }) = true
      norm_num [leaf6317Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6317CertificateValid :
    WideCertificateValid leaf6317Box leaf6317Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk97ValidityFacts chi329ValidityFacts
    leaf6317LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6317CoverageChecked :
    coverageCheck (innerAD leaf6317Box) leaf6317InnerLog = true := by
  rfl'

private theorem leaf6317InnerLogValid :
    leaf6317InnerLog.Valid 8 (innerAD leaf6317Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint79PositiveFacts.valid leaf6317CoverageChecked

private noncomputable def leaf6317InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629477/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6317InputLogOnePlusV_eq :
    leaf6317InputLogOnePlusV = outerEnclosure 24
      (leaf6317Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6317RoundedFacts : LeafRoundedFacts 8
    leaf6317Certificate.logOnePlusV leaf6317InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6317InputLogOnePlusV_eq }

private noncomputable def leaf6317Inputs : Inputs :=
  inputsOfCaches globalInput sk97RoundedInputs
    chi329InputQChi innerPair279Input
    leaf6317InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6317LowerChecked :
    lowerCheck 24 leaf6317Box leaf6317Inputs = true := by
  rfl'

private theorem leaf6317CoversExact : CoversExact 8
    leaf6317Box leaf6317Certificate leaf6317InnerLog leaf6317Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk97RoundedFacts chi329RoundedFacts
    innerPair279RoundedFacts leaf6317RoundedFacts (by rfl)

private theorem leaf6317FlatSound : Sound leaf6317Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6317CertificateValid
    leaf6317InnerLogValid leaf6317CoversExact leaf6317LowerChecked

private noncomputable def leaf6318Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (65/128), chiHi := (33/64) }

private noncomputable def leaf6318Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217953/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34356561920) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (330125417/268435456) }, upper := { exponent := 1, mantissa := (2575/2048) } }, logOuter := sk97LogOuterCertificate, logK := sk97LogKCertificate, logChi := chi330LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714792957/68713123840) } }, logDArg := sk97LogDArgCertificate }

private noncomputable def leaf6318InnerLog : WideLogData :=
  innerPair658Data

set_option maxRecDepth 1000000 in
private theorem leaf6318LocalValidity :
    LeafFacts leaf6318Box leaf6318Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6318Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34356561920) }) = true
      norm_num [leaf6318Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6318CertificateValid :
    WideCertificateValid leaf6318Box leaf6318Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk97ValidityFacts chi330ValidityFacts
    leaf6318LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6318CoverageChecked :
    coverageCheck (innerAD leaf6318Box) leaf6318InnerLog = true := by
  rfl'

private theorem leaf6318InnerLogValid :
    leaf6318InnerLog.Valid 8 (innerAD leaf6318Box) :=
  wideLogDataValid_of_cachedCheck endpoint403PositiveFacts
    endpoint419PositiveFacts.valid leaf6318CoverageChecked

private noncomputable def leaf6318InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (726843/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf6318InputLogOnePlusV_eq :
    leaf6318InputLogOnePlusV = outerEnclosure 24
      (leaf6318Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6318RoundedFacts : LeafRoundedFacts 8
    leaf6318Certificate.logOnePlusV leaf6318InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6318InputLogOnePlusV_eq }

private noncomputable def leaf6318Inputs : Inputs :=
  inputsOfCaches globalInput sk97RoundedInputs
    chi330InputQChi innerPair658Input
    leaf6318InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6318LowerChecked :
    lowerCheck 24 leaf6318Box leaf6318Inputs = true := by
  rfl'

private theorem leaf6318CoversExact : CoversExact 8
    leaf6318Box leaf6318Certificate leaf6318InnerLog leaf6318Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk97RoundedFacts chi330RoundedFacts
    innerPair658RoundedFacts leaf6318RoundedFacts (by rfl)

private theorem leaf6318FlatSound : Sound leaf6318Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6318CertificateValid
    leaf6318InnerLogValid leaf6318CoversExact leaf6318LowerChecked

private noncomputable def leaf6319Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (33/64), chiHi := (67/128) }

private noncomputable def leaf6319Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217955/134217728) }, vSqrt := { lower := (32765/32768), upper := (11452743679/11452171264) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (333139887/268435456) }, upper := { exponent := 1, mantissa := (5197/4096) } }, logOuter := sk97LogOuterCertificate, logK := sk97LogKCertificate, logChi := chi331LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (22904914943/22904342528) } }, logDArg := sk97LogDArgCertificate }

private noncomputable def leaf6319InnerLog : WideLogData :=
  innerPair286Data

set_option maxRecDepth 1000000 in
private theorem leaf6319LocalValidity :
    LeafFacts leaf6319Box leaf6319Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6319Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (11452743679/11452171264) }) = true
      norm_num [leaf6319Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6319CertificateValid :
    WideCertificateValid leaf6319Box leaf6319Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk97ValidityFacts chi331ValidityFacts
    leaf6319LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6319CoverageChecked :
    coverageCheck (innerAD leaf6319Box) leaf6319InnerLog = true := by
  rfl'

private theorem leaf6319InnerLogValid :
    leaf6319InnerLog.Valid 8 (innerAD leaf6319Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint90PositiveFacts.valid leaf6319CoverageChecked

private noncomputable def leaf6319InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907375/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6319InputLogOnePlusV_eq :
    leaf6319InputLogOnePlusV = outerEnclosure 24
      (leaf6319Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6319RoundedFacts : LeafRoundedFacts 8
    leaf6319Certificate.logOnePlusV leaf6319InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6319InputLogOnePlusV_eq }

private noncomputable def leaf6319Inputs : Inputs :=
  inputsOfCaches globalInput sk97RoundedInputs
    chi331InputQChi innerPair286Input
    leaf6319InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6319LowerChecked :
    lowerCheck 24 leaf6319Box leaf6319Inputs = true := by
  rfl'

private theorem leaf6319CoversExact : CoversExact 8
    leaf6319Box leaf6319Certificate leaf6319InnerLog leaf6319Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk97RoundedFacts chi331RoundedFacts
    innerPair286RoundedFacts leaf6319RoundedFacts (by rfl)

private theorem leaf6319FlatSound : Sound leaf6319Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6319CertificateValid
    leaf6319InnerLogValid leaf6319CoversExact leaf6319LowerChecked

private noncomputable def leaf6320Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (67/128), chiHi := (17/32) }

private noncomputable def leaf6320Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217957/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34356465664) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (336154357/268435456) }, upper := { exponent := 1, mantissa := (1311/1024) } }, logOuter := sk97LogOuterCertificate, logK := sk97LogKCertificate, logChi := chi332LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714696701/68712931328) } }, logDArg := sk97LogDArgCertificate }

private noncomputable def leaf6320InnerLog : WideLogData :=
  innerPair293Data

set_option maxRecDepth 1000000 in
private theorem leaf6320LocalValidity :
    LeafFacts leaf6320Box leaf6320Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6320Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34356465664) }) = true
      norm_num [leaf6320Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6320CertificateValid :
    WideCertificateValid leaf6320Box leaf6320Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk97ValidityFacts chi332ValidityFacts
    leaf6320LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6320CoverageChecked :
    coverageCheck (innerAD leaf6320Box) leaf6320InnerLog = true := by
  rfl'

private theorem leaf6320InnerLogValid :
    leaf6320InnerLog.Valid 8 (innerAD leaf6320Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint90PositiveFacts.valid leaf6320CoverageChecked

private noncomputable def leaf6320InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453689/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf6320InputLogOnePlusV_eq :
    leaf6320InputLogOnePlusV = outerEnclosure 24
      (leaf6320Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6320RoundedFacts : LeafRoundedFacts 8
    leaf6320Certificate.logOnePlusV leaf6320InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6320InputLogOnePlusV_eq }

private noncomputable def leaf6320Inputs : Inputs :=
  inputsOfCaches globalInput sk97RoundedInputs
    chi332InputQChi innerPair293Input
    leaf6320InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6320LowerChecked :
    lowerCheck 24 leaf6320Box leaf6320Inputs = true := by
  rfl'

private theorem leaf6320CoversExact : CoversExact 8
    leaf6320Box leaf6320Certificate leaf6320InnerLog leaf6320Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk97RoundedFacts chi332RoundedFacts
    innerPair293RoundedFacts leaf6320RoundedFacts (by rfl)

private theorem leaf6320FlatSound : Sound leaf6320Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6320CertificateValid
    leaf6320InnerLogValid leaf6320CoversExact leaf6320LowerChecked

private noncomputable def leaf6321Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (1/2), chiHi := (65/128) }

private noncomputable def leaf6321Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217953/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34356543488) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (331304993/268435456) }, upper := { exponent := 1, mantissa := (323/256) } }, logOuter := sk98LogOuterCertificate, logK := sk98LogKCertificate, logChi := chi329LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68714774525/68713086976) } }, logDArg := sk98LogDArgCertificate }

private noncomputable def leaf6321InnerLog : WideLogData :=
  innerPair740Data

set_option maxRecDepth 1000000 in
private theorem leaf6321LocalValidity :
    LeafFacts leaf6321Box leaf6321Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6321Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34356543488) }) = true
      norm_num [leaf6321Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6321CertificateValid :
    WideCertificateValid leaf6321Box leaf6321Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk98ValidityFacts chi329ValidityFacts
    leaf6321LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6321CoverageChecked :
    coverageCheck (innerAD leaf6321Box) leaf6321InnerLog = true := by
  rfl'

private theorem leaf6321InnerLogValid :
    leaf6321InnerLog.Valid 8 (innerAD leaf6321Box) :=
  wideLogDataValid_of_cachedCheck endpoint477PositiveFacts
    endpoint478PositiveFacts.valid leaf6321CoverageChecked

private noncomputable def leaf6321InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629493/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6321InputLogOnePlusV_eq :
    leaf6321InputLogOnePlusV = outerEnclosure 24
      (leaf6321Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6321RoundedFacts : LeafRoundedFacts 8
    leaf6321Certificate.logOnePlusV leaf6321InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6321InputLogOnePlusV_eq }

private noncomputable def leaf6321Inputs : Inputs :=
  inputsOfCaches globalInput sk98RoundedInputs
    chi329InputQChi innerPair740Input
    leaf6321InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6321LowerChecked :
    lowerCheck 24 leaf6321Box leaf6321Inputs = true := by
  rfl'

private theorem leaf6321CoversExact : CoversExact 8
    leaf6321Box leaf6321Certificate leaf6321InnerLog leaf6321Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk98RoundedFacts chi329RoundedFacts
    innerPair740RoundedFacts leaf6321RoundedFacts (by rfl)

private theorem leaf6321FlatSound : Sound leaf6321Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6321CertificateValid
    leaf6321InnerLogValid leaf6321CoversExact leaf6321LowerChecked

private noncomputable def leaf6322Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (65/128), chiHi := (33/64) }

private noncomputable def leaf6322Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217955/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34356494336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (334384995/268435456) }, upper := { exponent := 1, mantissa := (163/128) } }, logOuter := sk98LogOuterCertificate, logK := sk98LogKCertificate, logChi := chi330LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68714725373/68712988672) } }, logDArg := sk98LogDArgCertificate }

private noncomputable def leaf6322InnerLog : WideLogData :=
  innerPair669Data

set_option maxRecDepth 1000000 in
private theorem leaf6322LocalValidity :
    LeafFacts leaf6322Box leaf6322Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6322Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34356494336) }) = true
      norm_num [leaf6322Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6322CertificateValid :
    WideCertificateValid leaf6322Box leaf6322Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk98ValidityFacts chi330ValidityFacts
    leaf6322LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6322CoverageChecked :
    coverageCheck (innerAD leaf6322Box) leaf6322InnerLog = true := by
  rfl'

private theorem leaf6322InnerLogValid :
    leaf6322InnerLog.Valid 8 (innerAD leaf6322Box) :=
  wideLogDataValid_of_cachedCheck endpoint414PositiveFacts
    endpoint437PositiveFacts.valid leaf6322CoverageChecked

private noncomputable def leaf6322InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629505/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6322InputLogOnePlusV_eq :
    leaf6322InputLogOnePlusV = outerEnclosure 24
      (leaf6322Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6322RoundedFacts : LeafRoundedFacts 8
    leaf6322Certificate.logOnePlusV leaf6322InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6322InputLogOnePlusV_eq }

private noncomputable def leaf6322Inputs : Inputs :=
  inputsOfCaches globalInput sk98RoundedInputs
    chi330InputQChi innerPair669Input
    leaf6322InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6322LowerChecked :
    lowerCheck 24 leaf6322Box leaf6322Inputs = true := by
  rfl'

private theorem leaf6322CoversExact : CoversExact 8
    leaf6322Box leaf6322Certificate leaf6322InnerLog leaf6322Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk98RoundedFacts chi330RoundedFacts
    innerPair669RoundedFacts leaf6322RoundedFacts (by rfl)

private theorem leaf6322FlatSound : Sound leaf6322Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6322CertificateValid
    leaf6322InnerLogValid leaf6322CoversExact leaf6322LowerChecked

private noncomputable def leaf6323Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (33/64), chiHi := (67/128) }

private noncomputable def leaf6323Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217957/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34356445184) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (337464997/268435456) }, upper := { exponent := 1, mantissa := (329/256) } }, logOuter := sk98LogOuterCertificate, logK := sk98LogKCertificate, logChi := chi331LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68714676221/68712890368) } }, logDArg := sk98LogDArgCertificate }

private noncomputable def leaf6323InnerLog : WideLogData :=
  innerPair298Data

set_option maxRecDepth 1000000 in
private theorem leaf6323LocalValidity :
    LeafFacts leaf6323Box leaf6323Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6323Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34356445184) }) = true
      norm_num [leaf6323Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6323CertificateValid :
    WideCertificateValid leaf6323Box leaf6323Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk98ValidityFacts chi331ValidityFacts
    leaf6323LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6323CoverageChecked :
    coverageCheck (innerAD leaf6323Box) leaf6323InnerLog = true := by
  rfl'

private theorem leaf6323InnerLogValid :
    leaf6323InnerLog.Valid 8 (innerAD leaf6323Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint435PositiveFacts.valid leaf6323CoverageChecked

private noncomputable def leaf6323InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629517/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6323InputLogOnePlusV_eq :
    leaf6323InputLogOnePlusV = outerEnclosure 24
      (leaf6323Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6323RoundedFacts : LeafRoundedFacts 8
    leaf6323Certificate.logOnePlusV leaf6323InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6323InputLogOnePlusV_eq }

private noncomputable def leaf6323Inputs : Inputs :=
  inputsOfCaches globalInput sk98RoundedInputs
    chi331InputQChi innerPair298Input
    leaf6323InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6323LowerChecked :
    lowerCheck 24 leaf6323Box leaf6323Inputs = true := by
  rfl'

private theorem leaf6323CoversExact : CoversExact 8
    leaf6323Box leaf6323Certificate leaf6323InnerLog leaf6323Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk98RoundedFacts chi331RoundedFacts
    innerPair298RoundedFacts leaf6323RoundedFacts (by rfl)

private theorem leaf6323FlatSound : Sound leaf6323Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6323CertificateValid
    leaf6323InnerLogValid leaf6323CoversExact leaf6323LowerChecked

private noncomputable def leaf6324Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (67/128), chiHi := (17/32) }

private noncomputable def leaf6324Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217959/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34356396032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (340544999/268435456) }, upper := { exponent := 1, mantissa := (83/64) } }, logOuter := sk98LogOuterCertificate, logK := sk98LogKCertificate, logChi := chi332LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68714627069/68712792064) } }, logDArg := sk98LogDArgCertificate }

private noncomputable def leaf6324InnerLog : WideLogData :=
  innerPair682Data

set_option maxRecDepth 1000000 in
private theorem leaf6324LocalValidity :
    LeafFacts leaf6324Box leaf6324Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6324Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34356396032) }) = true
      norm_num [leaf6324Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6324CertificateValid :
    WideCertificateValid leaf6324Box leaf6324Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk98ValidityFacts chi332ValidityFacts
    leaf6324LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6324CoverageChecked :
    coverageCheck (innerAD leaf6324Box) leaf6324InnerLog = true := by
  rfl'

private theorem leaf6324InnerLogValid :
    leaf6324InnerLog.Valid 8 (innerAD leaf6324Box) :=
  wideLogDataValid_of_cachedCheck endpoint434PositiveFacts
    endpoint436PositiveFacts.valid leaf6324CoverageChecked

private noncomputable def leaf6324InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629529/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6324InputLogOnePlusV_eq :
    leaf6324InputLogOnePlusV = outerEnclosure 24
      (leaf6324Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6324RoundedFacts : LeafRoundedFacts 8
    leaf6324Certificate.logOnePlusV leaf6324InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6324InputLogOnePlusV_eq }

private noncomputable def leaf6324Inputs : Inputs :=
  inputsOfCaches globalInput sk98RoundedInputs
    chi332InputQChi innerPair682Input
    leaf6324InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6324LowerChecked :
    lowerCheck 24 leaf6324Box leaf6324Inputs = true := by
  rfl'

private theorem leaf6324CoversExact : CoversExact 8
    leaf6324Box leaf6324Certificate leaf6324InnerLog leaf6324Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk98RoundedFacts chi332RoundedFacts
    innerPair682RoundedFacts leaf6324RoundedFacts (by rfl)

private theorem leaf6324FlatSound : Sound leaf6324Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6324CertificateValid
    leaf6324InnerLogValid leaf6324CoversExact leaf6324LowerChecked

private noncomputable def leaf6325Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (17/32), chiHi := (69/128) }

private noncomputable def leaf6325Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217959/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34356417536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (339168827/268435456) }, upper := { exponent := 1, mantissa := (5291/4096) } }, logOuter := sk97LogOuterCertificate, logK := sk97LogKCertificate, logChi := chi327LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714648573/68712835072) } }, logDArg := sk97LogDArgCertificate }

private noncomputable def leaf6325InnerLog : WideLogData :=
  innerPair672Data

set_option maxRecDepth 1000000 in
private theorem leaf6325LocalValidity :
    LeafFacts leaf6325Box leaf6325Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6325Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34356417536) }) = true
      norm_num [leaf6325Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6325CertificateValid :
    WideCertificateValid leaf6325Box leaf6325Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk97ValidityFacts chi327ValidityFacts
    leaf6325LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6325CoverageChecked :
    coverageCheck (innerAD leaf6325Box) leaf6325InnerLog = true := by
  rfl'

private theorem leaf6325InnerLogValid :
    leaf6325InnerLog.Valid 8 (innerAD leaf6325Box) :=
  wideLogDataValid_of_cachedCheck endpoint419PositiveFacts
    endpoint436PositiveFacts.valid leaf6325CoverageChecked

private noncomputable def leaf6325InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907381/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6325InputLogOnePlusV_eq :
    leaf6325InputLogOnePlusV = outerEnclosure 24
      (leaf6325Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6325RoundedFacts : LeafRoundedFacts 8
    leaf6325Certificate.logOnePlusV leaf6325InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6325InputLogOnePlusV_eq }

private noncomputable def leaf6325Inputs : Inputs :=
  inputsOfCaches globalInput sk97RoundedInputs
    chi327InputQChi innerPair672Input
    leaf6325InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6325LowerChecked :
    lowerCheck 24 leaf6325Box leaf6325Inputs = true := by
  rfl'

private theorem leaf6325CoversExact : CoversExact 8
    leaf6325Box leaf6325Certificate leaf6325InnerLog leaf6325Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk97RoundedFacts chi327RoundedFacts
    innerPair672RoundedFacts leaf6325RoundedFacts (by rfl)

private theorem leaf6325FlatSound : Sound leaf6325Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6325CertificateValid
    leaf6325InnerLogValid leaf6325CoversExact leaf6325LowerChecked

private noncomputable def leaf6326Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (69/128), chiHi := (35/64) }

private noncomputable def leaf6326Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217961/134217728) }, vSqrt := { lower := (32765/32768), upper := (11452743679/11452123136) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (342183297/268435456) }, upper := { exponent := 1, mantissa := (2669/2048) } }, logOuter := sk97LogOuterCertificate, logK := sk97LogKCertificate, logChi := chi328LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (22904866815/22904246272) } }, logDArg := sk97LogDArgCertificate }

private noncomputable def leaf6326InnerLog : WideLogData :=
  innerPair294Data

set_option maxRecDepth 1000000 in
private theorem leaf6326LocalValidity :
    LeafFacts leaf6326Box leaf6326Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6326Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (11452743679/11452123136) }) = true
      norm_num [leaf6326Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6326CertificateValid :
    WideCertificateValid leaf6326Box leaf6326Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk97ValidityFacts chi328ValidityFacts
    leaf6326LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6326CoverageChecked :
    coverageCheck (innerAD leaf6326Box) leaf6326InnerLog = true := by
  rfl'

private theorem leaf6326InnerLogValid :
    leaf6326InnerLog.Valid 8 (innerAD leaf6326Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint91PositiveFacts.valid leaf6326CoverageChecked

private noncomputable def leaf6326InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629535/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6326InputLogOnePlusV_eq :
    leaf6326InputLogOnePlusV = outerEnclosure 24
      (leaf6326Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6326RoundedFacts : LeafRoundedFacts 8
    leaf6326Certificate.logOnePlusV leaf6326InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6326InputLogOnePlusV_eq }

private noncomputable def leaf6326Inputs : Inputs :=
  inputsOfCaches globalInput sk97RoundedInputs
    chi328InputQChi innerPair294Input
    leaf6326InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6326LowerChecked :
    lowerCheck 24 leaf6326Box leaf6326Inputs = true := by
  rfl'

private theorem leaf6326CoversExact : CoversExact 8
    leaf6326Box leaf6326Certificate leaf6326InnerLog leaf6326Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk97RoundedFacts chi328RoundedFacts
    innerPair294RoundedFacts leaf6326RoundedFacts (by rfl)

private theorem leaf6326FlatSound : Sound leaf6326Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6326CertificateValid
    leaf6326InnerLogValid leaf6326CoversExact leaf6326LowerChecked

private noncomputable def leaf6327Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (35/64), chiHi := (71/128) }

private noncomputable def leaf6327Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217963/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34356321280) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (345197767/268435456) }, upper := { exponent := 1, mantissa := (5385/4096) } }, logOuter := sk97LogOuterCertificate, logK := sk97LogKCertificate, logChi := chi333LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714552317/68712642560) } }, logDArg := sk97LogDArgCertificate }

private noncomputable def leaf6327InnerLog : WideLogData :=
  innerPair342Data

set_option maxRecDepth 1000000 in
private theorem leaf6327LocalValidity :
    LeafFacts leaf6327Box leaf6327Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6327Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34356321280) }) = true
      norm_num [leaf6327Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6327CertificateValid :
    WideCertificateValid leaf6327Box leaf6327Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk97ValidityFacts chi333ValidityFacts
    leaf6327LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6327CoverageChecked :
    coverageCheck (innerAD leaf6327Box) leaf6327InnerLog = true := by
  rfl'

private theorem leaf6327InnerLogValid :
    leaf6327InnerLog.Valid 8 (innerAD leaf6327Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint95PositiveFacts.valid leaf6327CoverageChecked

private noncomputable def leaf6327InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629547/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6327InputLogOnePlusV_eq :
    leaf6327InputLogOnePlusV = outerEnclosure 24
      (leaf6327Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6327RoundedFacts : LeafRoundedFacts 8
    leaf6327Certificate.logOnePlusV leaf6327InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6327InputLogOnePlusV_eq }

private noncomputable def leaf6327Inputs : Inputs :=
  inputsOfCaches globalInput sk97RoundedInputs
    chi333InputQChi innerPair342Input
    leaf6327InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6327LowerChecked :
    lowerCheck 24 leaf6327Box leaf6327Inputs = true := by
  rfl'

private theorem leaf6327CoversExact : CoversExact 8
    leaf6327Box leaf6327Certificate leaf6327InnerLog leaf6327Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk97RoundedFacts chi333RoundedFacts
    innerPair342RoundedFacts leaf6327RoundedFacts (by rfl)

private theorem leaf6327FlatSound : Sound leaf6327Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6327CertificateValid
    leaf6327InnerLogValid leaf6327CoversExact leaf6327LowerChecked

private noncomputable def leaf6328Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (71/128), chiHi := (9/16) }

private noncomputable def leaf6328Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217965/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34356273152) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (348212237/268435456) }, upper := { exponent := 1, mantissa := (679/512) } }, logOuter := sk97LogOuterCertificate, logK := sk97LogKCertificate, logChi := chi334LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714504189/68712546304) } }, logDArg := sk97LogDArgCertificate }

private noncomputable def leaf6328InnerLog : WideLogData :=
  innerPair340Data

set_option maxRecDepth 1000000 in
private theorem leaf6328LocalValidity :
    LeafFacts leaf6328Box leaf6328Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6328Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34356273152) }) = true
      norm_num [leaf6328Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6328CertificateValid :
    WideCertificateValid leaf6328Box leaf6328Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk97ValidityFacts chi334ValidityFacts
    leaf6328LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6328CoverageChecked :
    coverageCheck (innerAD leaf6328Box) leaf6328InnerLog = true := by
  rfl'

private theorem leaf6328InnerLogValid :
    leaf6328InnerLog.Valid 8 (innerAD leaf6328Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint92PositiveFacts.valid leaf6328CoverageChecked

private noncomputable def leaf6328InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629559/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6328InputLogOnePlusV_eq :
    leaf6328InputLogOnePlusV = outerEnclosure 24
      (leaf6328Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6328RoundedFacts : LeafRoundedFacts 8
    leaf6328Certificate.logOnePlusV leaf6328InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6328InputLogOnePlusV_eq }

private noncomputable def leaf6328Inputs : Inputs :=
  inputsOfCaches globalInput sk97RoundedInputs
    chi334InputQChi innerPair340Input
    leaf6328InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6328LowerChecked :
    lowerCheck 24 leaf6328Box leaf6328Inputs = true := by
  rfl'

private theorem leaf6328CoversExact : CoversExact 8
    leaf6328Box leaf6328Certificate leaf6328InnerLog leaf6328Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk97RoundedFacts chi334RoundedFacts
    innerPair340RoundedFacts leaf6328RoundedFacts (by rfl)

private theorem leaf6328FlatSound : Sound leaf6328Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6328CertificateValid
    leaf6328InnerLogValid leaf6328CoversExact leaf6328LowerChecked

private noncomputable def leaf6329Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (17/32), chiHi := (69/128) }

private noncomputable def leaf6329Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217961/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34356346880) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (343625001/268435456) }, upper := { exponent := 1, mantissa := (335/256) } }, logOuter := sk98LogOuterCertificate, logK := sk98LogKCertificate, logChi := chi327LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68714577917/68712693760) } }, logDArg := sk98LogDArgCertificate }

private noncomputable def leaf6329InnerLog : WideLogData :=
  innerPair294Data

set_option maxRecDepth 1000000 in
private theorem leaf6329LocalValidity :
    LeafFacts leaf6329Box leaf6329Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6329Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34356346880) }) = true
      norm_num [leaf6329Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6329CertificateValid :
    WideCertificateValid leaf6329Box leaf6329Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk98ValidityFacts chi327ValidityFacts
    leaf6329LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6329CoverageChecked :
    coverageCheck (innerAD leaf6329Box) leaf6329InnerLog = true := by
  rfl'

private theorem leaf6329InnerLogValid :
    leaf6329InnerLog.Valid 8 (innerAD leaf6329Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint91PositiveFacts.valid leaf6329CoverageChecked

private noncomputable def leaf6329InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629541/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6329InputLogOnePlusV_eq :
    leaf6329InputLogOnePlusV = outerEnclosure 24
      (leaf6329Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6329RoundedFacts : LeafRoundedFacts 8
    leaf6329Certificate.logOnePlusV leaf6329InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6329InputLogOnePlusV_eq }

private noncomputable def leaf6329Inputs : Inputs :=
  inputsOfCaches globalInput sk98RoundedInputs
    chi327InputQChi innerPair294Input
    leaf6329InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6329LowerChecked :
    lowerCheck 24 leaf6329Box leaf6329Inputs = true := by
  rfl'

private theorem leaf6329CoversExact : CoversExact 8
    leaf6329Box leaf6329Certificate leaf6329InnerLog leaf6329Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk98RoundedFacts chi327RoundedFacts
    innerPair294RoundedFacts leaf6329RoundedFacts (by rfl)

private theorem leaf6329FlatSound : Sound leaf6329Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6329CertificateValid
    leaf6329InnerLogValid leaf6329CoversExact leaf6329LowerChecked

private noncomputable def leaf6330Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (69/128), chiHi := (35/64) }

private noncomputable def leaf6330Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217963/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34356297728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (346705003/268435456) }, upper := { exponent := 1, mantissa := (169/128) } }, logOuter := sk98LogOuterCertificate, logK := sk98LogKCertificate, logChi := chi328LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68714528765/68712595456) } }, logDArg := sk98LogDArgCertificate }

private noncomputable def leaf6330InnerLog : WideLogData :=
  innerPair684Data

set_option maxRecDepth 1000000 in
private theorem leaf6330LocalValidity :
    LeafFacts leaf6330Box leaf6330Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6330Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34356297728) }) = true
      norm_num [leaf6330Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6330CertificateValid :
    WideCertificateValid leaf6330Box leaf6330Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk98ValidityFacts chi328ValidityFacts
    leaf6330LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6330CoverageChecked :
    coverageCheck (innerAD leaf6330Box) leaf6330InnerLog = true := by
  rfl'

private theorem leaf6330InnerLogValid :
    leaf6330InnerLog.Valid 8 (innerAD leaf6330Box) :=
  wideLogDataValid_of_cachedCheck endpoint435PositiveFacts
    endpoint95PositiveFacts.valid leaf6330CoverageChecked

private noncomputable def leaf6330InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629553/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6330InputLogOnePlusV_eq :
    leaf6330InputLogOnePlusV = outerEnclosure 24
      (leaf6330Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6330RoundedFacts : LeafRoundedFacts 8
    leaf6330Certificate.logOnePlusV leaf6330InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6330InputLogOnePlusV_eq }

private noncomputable def leaf6330Inputs : Inputs :=
  inputsOfCaches globalInput sk98RoundedInputs
    chi328InputQChi innerPair684Input
    leaf6330InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6330LowerChecked :
    lowerCheck 24 leaf6330Box leaf6330Inputs = true := by
  rfl'

private theorem leaf6330CoversExact : CoversExact 8
    leaf6330Box leaf6330Certificate leaf6330InnerLog leaf6330Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk98RoundedFacts chi328RoundedFacts
    innerPair684RoundedFacts leaf6330RoundedFacts (by rfl)

private theorem leaf6330FlatSound : Sound leaf6330Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6330CertificateValid
    leaf6330InnerLogValid leaf6330CoversExact leaf6330LowerChecked

private noncomputable def leaf6331Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (35/64), chiHi := (71/128) }

private noncomputable def leaf6331Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217965/134217728) }, vSqrt := { lower := (65529/65536), upper := (2642940849/2642788352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (349785005/268435456) }, upper := { exponent := 1, mantissa := (341/256) } }, logOuter := sk98LogOuterCertificate, logK := sk98LogKCertificate, logChi := chi333LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (5285729201/5285576704) } }, logDArg := sk98LogDArgCertificate }

private noncomputable def leaf6331InnerLog : WideLogData :=
  innerPair340Data

set_option maxRecDepth 1000000 in
private theorem leaf6331LocalValidity :
    LeafFacts leaf6331Box leaf6331Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6331Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (2642940849/2642788352) }) = true
      norm_num [leaf6331Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6331CertificateValid :
    WideCertificateValid leaf6331Box leaf6331Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk98ValidityFacts chi333ValidityFacts
    leaf6331LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6331CoverageChecked :
    coverageCheck (innerAD leaf6331Box) leaf6331InnerLog = true := by
  rfl'

private theorem leaf6331InnerLogValid :
    leaf6331InnerLog.Valid 8 (innerAD leaf6331Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint92PositiveFacts.valid leaf6331CoverageChecked

private noncomputable def leaf6331InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629565/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6331InputLogOnePlusV_eq :
    leaf6331InputLogOnePlusV = outerEnclosure 24
      (leaf6331Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6331RoundedFacts : LeafRoundedFacts 8
    leaf6331Certificate.logOnePlusV leaf6331InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6331InputLogOnePlusV_eq }

private noncomputable def leaf6331Inputs : Inputs :=
  inputsOfCaches globalInput sk98RoundedInputs
    chi333InputQChi innerPair340Input
    leaf6331InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6331LowerChecked :
    lowerCheck 24 leaf6331Box leaf6331Inputs = true := by
  rfl'

private theorem leaf6331CoversExact : CoversExact 8
    leaf6331Box leaf6331Certificate leaf6331InnerLog leaf6331Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk98RoundedFacts chi333RoundedFacts
    innerPair340RoundedFacts leaf6331RoundedFacts (by rfl)

private theorem leaf6331FlatSound : Sound leaf6331Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6331CertificateValid
    leaf6331InnerLogValid leaf6331CoversExact leaf6331LowerChecked

private noncomputable def leaf6332Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (71/128), chiHi := (9/16) }

private noncomputable def leaf6332Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217967/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34356199424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (352865007/268435456) }, upper := { exponent := 1, mantissa := (43/32) } }, logOuter := sk98LogOuterCertificate, logK := sk98LogKCertificate, logChi := chi334LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68714430461/68712398848) } }, logDArg := sk98LogDArgCertificate }

private noncomputable def leaf6332InnerLog : WideLogData :=
  innerPair345Data

set_option maxRecDepth 1000000 in
private theorem leaf6332LocalValidity :
    LeafFacts leaf6332Box leaf6332Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6332Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34356199424) }) = true
      norm_num [leaf6332Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6332CertificateValid :
    WideCertificateValid leaf6332Box leaf6332Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk98ValidityFacts chi334ValidityFacts
    leaf6332LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6332CoverageChecked :
    coverageCheck (innerAD leaf6332Box) leaf6332InnerLog = true := by
  rfl'

private theorem leaf6332InnerLogValid :
    leaf6332InnerLog.Valid 8 (innerAD leaf6332Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint92PositiveFacts.valid leaf6332CoverageChecked

private noncomputable def leaf6332InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629577/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6332InputLogOnePlusV_eq :
    leaf6332InputLogOnePlusV = outerEnclosure 24
      (leaf6332Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6332RoundedFacts : LeafRoundedFacts 8
    leaf6332Certificate.logOnePlusV leaf6332InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6332InputLogOnePlusV_eq }

private noncomputable def leaf6332Inputs : Inputs :=
  inputsOfCaches globalInput sk98RoundedInputs
    chi334InputQChi innerPair345Input
    leaf6332InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6332LowerChecked :
    lowerCheck 24 leaf6332Box leaf6332Inputs = true := by
  rfl'

private theorem leaf6332CoversExact : CoversExact 8
    leaf6332Box leaf6332Certificate leaf6332InnerLog leaf6332Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk98RoundedFacts chi334RoundedFacts
    innerPair345RoundedFacts leaf6332RoundedFacts (by rfl)

private theorem leaf6332FlatSound : Sound leaf6332Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6332CertificateValid
    leaf6332InnerLogValid leaf6332CoversExact leaf6332LowerChecked

private noncomputable def leaf6333Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (9/16), chiHi := (73/128) }

private noncomputable def leaf6333Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217963/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34356374528) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (341790103/268435456) }, upper := { exponent := 1, mantissa := (5333/4096) } }, logOuter := sk95LogOuterCertificate, logK := sk95LogKCertificate, logChi := chi335LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714605565/68712749056) } }, logDArg := sk95LogDArgCertificate }

private noncomputable def leaf6333InnerLog : WideLogData :=
  innerPair294Data

set_option maxRecDepth 1000000 in
private theorem leaf6333LocalValidity :
    LeafFacts leaf6333Box leaf6333Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6333Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34356374528) }) = true
      norm_num [leaf6333Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6333CertificateValid :
    WideCertificateValid leaf6333Box leaf6333Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk95ValidityFacts chi335ValidityFacts
    leaf6333LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6333CoverageChecked :
    coverageCheck (innerAD leaf6333Box) leaf6333InnerLog = true := by
  rfl'

private theorem leaf6333InnerLogValid :
    leaf6333InnerLog.Valid 8 (innerAD leaf6333Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint91PositiveFacts.valid leaf6333CoverageChecked

private noncomputable def leaf6333InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814767/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6333InputLogOnePlusV_eq :
    leaf6333InputLogOnePlusV = outerEnclosure 24
      (leaf6333Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6333RoundedFacts : LeafRoundedFacts 8
    leaf6333Certificate.logOnePlusV leaf6333InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6333InputLogOnePlusV_eq }

private noncomputable def leaf6333Inputs : Inputs :=
  inputsOfCaches globalInput sk95RoundedInputs
    chi335InputQChi innerPair294Input
    leaf6333InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6333LowerChecked :
    lowerCheck 24 leaf6333Box leaf6333Inputs = true := by
  rfl'

private theorem leaf6333CoversExact : CoversExact 8
    leaf6333Box leaf6333Certificate leaf6333InnerLog leaf6333Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk95RoundedFacts chi335RoundedFacts
    innerPair294RoundedFacts leaf6333RoundedFacts (by rfl)

private theorem leaf6333FlatSound : Sound leaf6333Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6333CertificateValid
    leaf6333InnerLogValid leaf6333CoversExact leaf6333LowerChecked

private noncomputable def leaf6334Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (73/128), chiHi := (37/64) }

private noncomputable def leaf6334Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217965/134217728) }, vSqrt := { lower := (32765/32768), upper := (2642940849/2642794496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (344673509/268435456) }, upper := { exponent := 1, mantissa := (2689/2048) } }, logOuter := sk95LogOuterCertificate, logK := sk95LogKCertificate, logChi := chi336LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (5285735345/5285588992) } }, logDArg := sk95LogDArgCertificate }

private noncomputable def leaf6334InnerLog : WideLogData :=
  innerPair340Data

set_option maxRecDepth 1000000 in
private theorem leaf6334LocalValidity :
    LeafFacts leaf6334Box leaf6334Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6334Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (2642940849/2642794496) }) = true
      norm_num [leaf6334Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6334CertificateValid :
    WideCertificateValid leaf6334Box leaf6334Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk95ValidityFacts chi336ValidityFacts
    leaf6334LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6334CoverageChecked :
    coverageCheck (innerAD leaf6334Box) leaf6334InnerLog = true := by
  rfl'

private theorem leaf6334InnerLogValid :
    leaf6334InnerLog.Valid 8 (innerAD leaf6334Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint92PositiveFacts.valid leaf6334CoverageChecked

private noncomputable def leaf6334InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629545/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6334InputLogOnePlusV_eq :
    leaf6334InputLogOnePlusV = outerEnclosure 24
      (leaf6334Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6334RoundedFacts : LeafRoundedFacts 8
    leaf6334Certificate.logOnePlusV leaf6334InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6334InputLogOnePlusV_eq }

private noncomputable def leaf6334Inputs : Inputs :=
  inputsOfCaches globalInput sk95RoundedInputs
    chi336InputQChi innerPair340Input
    leaf6334InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6334LowerChecked :
    lowerCheck 24 leaf6334Box leaf6334Inputs = true := by
  rfl'

private theorem leaf6334CoversExact : CoversExact 8
    leaf6334Box leaf6334Certificate leaf6334InnerLog leaf6334Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk95RoundedFacts chi336RoundedFacts
    innerPair340RoundedFacts leaf6334RoundedFacts (by rfl)

private theorem leaf6334FlatSound : Sound leaf6334Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6334CertificateValid
    leaf6334InnerLogValid leaf6334CoversExact leaf6334LowerChecked

private noncomputable def leaf6335Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (37/64), chiHi := (19/32) }

private noncomputable def leaf6335Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109029/67108864) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34356236288) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (173762029/134217728) }, upper := { exponent := 1, mantissa := (1367/1024) } }, logOuter := sk95LogOuterCertificate, logK := sk95LogKCertificate, logChi := chi87LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714467325/68712472576) } }, logDArg := sk95LogDArgCertificate }

private noncomputable def leaf6335InnerLog : WideLogData :=
  innerPair686Data

set_option maxRecDepth 1000000 in
private theorem leaf6335LocalValidity :
    LeafFacts leaf6335Box leaf6335Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6335Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34356236288) }) = true
      norm_num [leaf6335Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6335CertificateValid :
    WideCertificateValid leaf6335Box leaf6335Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk95ValidityFacts chi87ValidityFacts
    leaf6335LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6335CoverageChecked :
    coverageCheck (innerAD leaf6335Box) leaf6335InnerLog = true := by
  rfl'

private theorem leaf6335InnerLogValid :
    leaf6335InnerLog.Valid 8 (innerAD leaf6335Box) :=
  wideLogDataValid_of_cachedCheck endpoint435PositiveFacts
    endpoint448PositiveFacts.valid leaf6335CoverageChecked

private noncomputable def leaf6335InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11357/16384) }

set_option maxRecDepth 1000000 in
private theorem leaf6335InputLogOnePlusV_eq :
    leaf6335InputLogOnePlusV = outerEnclosure 24
      (leaf6335Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6335RoundedFacts : LeafRoundedFacts 8
    leaf6335Certificate.logOnePlusV leaf6335InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6335InputLogOnePlusV_eq }

private noncomputable def leaf6335Inputs : Inputs :=
  inputsOfCaches globalInput sk95RoundedInputs
    chi87InputQChi innerPair686Input
    leaf6335InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6335LowerChecked :
    lowerCheck 24 leaf6335Box leaf6335Inputs = true := by
  rfl'

private theorem leaf6335CoversExact : CoversExact 8
    leaf6335Box leaf6335Certificate leaf6335InnerLog leaf6335Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk95RoundedFacts chi87RoundedFacts
    innerPair686RoundedFacts leaf6335RoundedFacts (by rfl)

private theorem leaf6335FlatSound : Sound leaf6335Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6335CertificateValid
    leaf6335InnerLogValid leaf6335CoversExact leaf6335LowerChecked

private noncomputable def leaf6336Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (9/16), chiHi := (73/128) }

private noncomputable def leaf6336Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217965/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34356299776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (346508405/268435456) }, upper := { exponent := 1, mantissa := (2703/2048) } }, logOuter := sk96LogOuterCertificate, logK := sk96LogKCertificate, logChi := chi335LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714530813/68712599552) } }, logDArg := sk96LogDArgCertificate }

private noncomputable def leaf6336InnerLog : WideLogData :=
  innerPair340Data

set_option maxRecDepth 1000000 in
private theorem leaf6336LocalValidity :
    LeafFacts leaf6336Box leaf6336Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6336Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34356299776) }) = true
      norm_num [leaf6336Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6336CertificateValid :
    WideCertificateValid leaf6336Box leaf6336Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk96ValidityFacts chi335ValidityFacts
    leaf6336LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6336CoverageChecked :
    coverageCheck (innerAD leaf6336Box) leaf6336InnerLog = true := by
  rfl'

private theorem leaf6336InnerLogValid :
    leaf6336InnerLog.Valid 8 (innerAD leaf6336Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint92PositiveFacts.valid leaf6336CoverageChecked

private noncomputable def leaf6336InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (726847/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf6336InputLogOnePlusV_eq :
    leaf6336InputLogOnePlusV = outerEnclosure 24
      (leaf6336Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6336RoundedFacts : LeafRoundedFacts 8
    leaf6336Certificate.logOnePlusV leaf6336InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6336InputLogOnePlusV_eq }

private noncomputable def leaf6336Inputs : Inputs :=
  inputsOfCaches globalInput sk96RoundedInputs
    chi335InputQChi innerPair340Input
    leaf6336InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6336LowerChecked :
    lowerCheck 24 leaf6336Box leaf6336Inputs = true := by
  rfl'

private theorem leaf6336CoversExact : CoversExact 8
    leaf6336Box leaf6336Certificate leaf6336InnerLog leaf6336Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk96RoundedFacts chi335RoundedFacts
    innerPair340RoundedFacts leaf6336RoundedFacts (by rfl)

private theorem leaf6336FlatSound : Sound leaf6336Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6336CertificateValid
    leaf6336InnerLogValid leaf6336CoversExact leaf6336LowerChecked

private noncomputable def leaf6337Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (73/128), chiHi := (37/64) }

private noncomputable def leaf6337Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217967/134217728) }, vSqrt := { lower := (32765/32768), upper := (11452743679/11452084224) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (349457343/268435456) }, upper := { exponent := 1, mantissa := (1363/1024) } }, logOuter := sk96LogOuterCertificate, logK := sk96LogKCertificate, logChi := chi336LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (22904827903/22904168448) } }, logDArg := sk96LogDArgCertificate }

private noncomputable def leaf6337InnerLog : WideLogData :=
  innerPair340Data

set_option maxRecDepth 1000000 in
private theorem leaf6337LocalValidity :
    LeafFacts leaf6337Box leaf6337Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6337Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (11452743679/11452084224) }) = true
      norm_num [leaf6337Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6337CertificateValid :
    WideCertificateValid leaf6337Box leaf6337Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk96ValidityFacts chi336ValidityFacts
    leaf6337LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6337CoverageChecked :
    coverageCheck (innerAD leaf6337Box) leaf6337InnerLog = true := by
  rfl'

private theorem leaf6337InnerLogValid :
    leaf6337InnerLog.Valid 8 (innerAD leaf6337Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint92PositiveFacts.valid leaf6337CoverageChecked

private noncomputable def leaf6337InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907391/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6337InputLogOnePlusV_eq :
    leaf6337InputLogOnePlusV = outerEnclosure 24
      (leaf6337Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6337RoundedFacts : LeafRoundedFacts 8
    leaf6337Certificate.logOnePlusV leaf6337InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6337InputLogOnePlusV_eq }

private noncomputable def leaf6337Inputs : Inputs :=
  inputsOfCaches globalInput sk96RoundedInputs
    chi336InputQChi innerPair340Input
    leaf6337InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6337LowerChecked :
    lowerCheck 24 leaf6337Box leaf6337Inputs = true := by
  rfl'

private theorem leaf6337CoversExact : CoversExact 8
    leaf6337Box leaf6337Certificate leaf6337InnerLog leaf6337Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk96RoundedFacts chi336RoundedFacts
    innerPair340RoundedFacts leaf6337RoundedFacts (by rfl)

private theorem leaf6337FlatSound : Sound leaf6337Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6337CertificateValid
    leaf6337InnerLogValid leaf6337CoversExact leaf6337LowerChecked

private noncomputable def leaf6338Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (37/64), chiHi := (19/32) }

private noncomputable def leaf6338Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109031/67108864) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34356158464) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (176186711/134217728) }, upper := { exponent := 1, mantissa := (693/512) } }, logOuter := sk96LogOuterCertificate, logK := sk96LogKCertificate, logChi := chi87LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714389501/68712316928) } }, logDArg := sk96LogDArgCertificate }

private noncomputable def leaf6338InnerLog : WideLogData :=
  innerPair351Data

set_option maxRecDepth 1000000 in
private theorem leaf6338LocalValidity :
    LeafFacts leaf6338Box leaf6338Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6338Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34356158464) }) = true
      norm_num [leaf6338Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6338CertificateValid :
    WideCertificateValid leaf6338Box leaf6338Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk96ValidityFacts chi87ValidityFacts
    leaf6338LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6338CoverageChecked :
    coverageCheck (innerAD leaf6338Box) leaf6338InnerLog = true := by
  rfl'

private theorem leaf6338InnerLogValid :
    leaf6338InnerLog.Valid 8 (innerAD leaf6338Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint465PositiveFacts.valid leaf6338CoverageChecked

private noncomputable def leaf6338InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629587/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6338InputLogOnePlusV_eq :
    leaf6338InputLogOnePlusV = outerEnclosure 24
      (leaf6338Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6338RoundedFacts : LeafRoundedFacts 8
    leaf6338Certificate.logOnePlusV leaf6338InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6338InputLogOnePlusV_eq }

private noncomputable def leaf6338Inputs : Inputs :=
  inputsOfCaches globalInput sk96RoundedInputs
    chi87InputQChi innerPair351Input
    leaf6338InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6338LowerChecked :
    lowerCheck 24 leaf6338Box leaf6338Inputs = true := by
  rfl'

private theorem leaf6338CoversExact : CoversExact 8
    leaf6338Box leaf6338Certificate leaf6338InnerLog leaf6338Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk96RoundedFacts chi87RoundedFacts
    innerPair351RoundedFacts leaf6338RoundedFacts (by rfl)

private theorem leaf6338FlatSound : Sound leaf6338Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6338CertificateValid
    leaf6338InnerLogValid leaf6338CoversExact leaf6338LowerChecked

private noncomputable def leaf6339Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (19/32), chiHi := (39/64) }

private noncomputable def leaf6339Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109031/67108864) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34356144128) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (176645435/134217728) }, upper := { exponent := 1, mantissa := (2779/2048) } }, logOuter := sk95LogOuterCertificate, logK := sk95LogKCertificate, logChi := chi321LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714375165/68712288256) } }, logDArg := sk95LogDArgCertificate }

private noncomputable def leaf6339InnerLog : WideLogData :=
  innerPair350Data

set_option maxRecDepth 1000000 in
private theorem leaf6339LocalValidity :
    LeafFacts leaf6339Box leaf6339Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6339Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34356144128) }) = true
      norm_num [leaf6339Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6339CertificateValid :
    WideCertificateValid leaf6339Box leaf6339Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk95ValidityFacts chi321ValidityFacts
    leaf6339LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6339CoverageChecked :
    coverageCheck (innerAD leaf6339Box) leaf6339InnerLog = true := by
  rfl'

private theorem leaf6339InnerLogValid :
    leaf6339InnerLog.Valid 8 (innerAD leaf6339Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint461PositiveFacts.valid leaf6339CoverageChecked

private noncomputable def leaf6339InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814795/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6339InputLogOnePlusV_eq :
    leaf6339InputLogOnePlusV = outerEnclosure 24
      (leaf6339Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6339RoundedFacts : LeafRoundedFacts 8
    leaf6339Certificate.logOnePlusV leaf6339InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6339InputLogOnePlusV_eq }

private noncomputable def leaf6339Inputs : Inputs :=
  inputsOfCaches globalInput sk95RoundedInputs
    chi321InputQChi innerPair350Input
    leaf6339InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6339LowerChecked :
    lowerCheck 24 leaf6339Box leaf6339Inputs = true := by
  rfl'

private theorem leaf6339CoversExact : CoversExact 8
    leaf6339Box leaf6339Certificate leaf6339InnerLog leaf6339Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk95RoundedFacts chi321RoundedFacts
    innerPair350RoundedFacts leaf6339RoundedFacts (by rfl)

private theorem leaf6339FlatSound : Sound leaf6339Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6339CertificateValid
    leaf6339InnerLogValid leaf6339CoversExact leaf6339LowerChecked

private noncomputable def leaf6340Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (39/64), chiHi := (5/8) }

private noncomputable def leaf6340Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109033/67108864) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34356051968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (179528841/134217728) }, upper := { exponent := 1, mantissa := (353/256) } }, logOuter := sk95LogOuterCertificate, logK := sk95LogKCertificate, logChi := chi322LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714283005/68712103936) } }, logDArg := sk95LogDArgCertificate }

private noncomputable def leaf6340InnerLog : WideLogData :=
  innerPair704Data

set_option maxRecDepth 1000000 in
private theorem leaf6340LocalValidity :
    LeafFacts leaf6340Box leaf6340Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6340Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34356051968) }) = true
      norm_num [leaf6340Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6340CertificateValid :
    WideCertificateValid leaf6340Box leaf6340Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk95ValidityFacts chi322ValidityFacts
    leaf6340LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6340CoverageChecked :
    coverageCheck (innerAD leaf6340Box) leaf6340InnerLog = true := by
  rfl'

private theorem leaf6340InnerLogValid :
    leaf6340InnerLog.Valid 8 (innerAD leaf6340Box) :=
  wideLogDataValid_of_cachedCheck endpoint448PositiveFacts
    endpoint460PositiveFacts.valid leaf6340CoverageChecked

private noncomputable def leaf6340InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629613/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6340InputLogOnePlusV_eq :
    leaf6340InputLogOnePlusV = outerEnclosure 24
      (leaf6340Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6340RoundedFacts : LeafRoundedFacts 8
    leaf6340Certificate.logOnePlusV leaf6340InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6340InputLogOnePlusV_eq }

private noncomputable def leaf6340Inputs : Inputs :=
  inputsOfCaches globalInput sk95RoundedInputs
    chi322InputQChi innerPair704Input
    leaf6340InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6340LowerChecked :
    lowerCheck 24 leaf6340Box leaf6340Inputs = true := by
  rfl'

private theorem leaf6340CoversExact : CoversExact 8
    leaf6340Box leaf6340Certificate leaf6340InnerLog leaf6340Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk95RoundedFacts chi322RoundedFacts
    innerPair704RoundedFacts leaf6340RoundedFacts (by rfl)

private theorem leaf6340FlatSound : Sound leaf6340Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6340CertificateValid
    leaf6340InnerLogValid leaf6340CoversExact leaf6340LowerChecked

private noncomputable def leaf6341Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (19/32), chiHi := (39/64) }

private noncomputable def leaf6341Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109033/67108864) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34356064256) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (179135649/134217728) }, upper := { exponent := 1, mantissa := (1409/1024) } }, logOuter := sk96LogOuterCertificate, logK := sk96LogKCertificate, logChi := chi321LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714295293/68712128512) } }, logDArg := sk96LogDArgCertificate }

private noncomputable def leaf6341InnerLog : WideLogData :=
  innerPair741Data

set_option maxRecDepth 1000000 in
private theorem leaf6341LocalValidity :
    LeafFacts leaf6341Box leaf6341Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6341Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34356064256) }) = true
      norm_num [leaf6341Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6341CertificateValid :
    WideCertificateValid leaf6341Box leaf6341Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk96ValidityFacts chi321ValidityFacts
    leaf6341LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6341CoverageChecked :
    coverageCheck (innerAD leaf6341Box) leaf6341InnerLog = true := by
  rfl'

private theorem leaf6341InnerLogValid :
    leaf6341InnerLog.Valid 8 (innerAD leaf6341Box) :=
  wideLogDataValid_of_cachedCheck endpoint479PositiveFacts
    endpoint466PositiveFacts.valid leaf6341CoverageChecked

private noncomputable def leaf6341InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814805/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6341InputLogOnePlusV_eq :
    leaf6341InputLogOnePlusV = outerEnclosure 24
      (leaf6341Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6341RoundedFacts : LeafRoundedFacts 8
    leaf6341Certificate.logOnePlusV leaf6341InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6341InputLogOnePlusV_eq }

private noncomputable def leaf6341Inputs : Inputs :=
  inputsOfCaches globalInput sk96RoundedInputs
    chi321InputQChi innerPair741Input
    leaf6341InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6341LowerChecked :
    lowerCheck 24 leaf6341Box leaf6341Inputs = true := by
  rfl'

private theorem leaf6341CoversExact : CoversExact 8
    leaf6341Box leaf6341Certificate leaf6341InnerLog leaf6341Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk96RoundedFacts chi321RoundedFacts
    innerPair741RoundedFacts leaf6341RoundedFacts (by rfl)

private theorem leaf6341FlatSound : Sound leaf6341Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6341CertificateValid
    leaf6341InnerLogValid leaf6341CoversExact leaf6341LowerChecked

private noncomputable def leaf6342Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (39/64), chiHi := (5/8) }

private noncomputable def leaf6342Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109035/67108864) }, vSqrt := { lower := (32765/32768), upper := (11452743679/11451990016) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (182084587/134217728) }, upper := { exponent := 1, mantissa := (179/128) } }, logOuter := sk96LogOuterCertificate, logK := sk96LogKCertificate, logChi := chi322LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (22904733695/22903980032) } }, logDArg := sk96LogDArgCertificate }

private noncomputable def leaf6342InnerLog : WideLogData :=
  innerPair353Data

set_option maxRecDepth 1000000 in
private theorem leaf6342LocalValidity :
    LeafFacts leaf6342Box leaf6342Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6342Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (11452743679/11451990016) }) = true
      norm_num [leaf6342Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6342CertificateValid :
    WideCertificateValid leaf6342Box leaf6342Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk96ValidityFacts chi322ValidityFacts
    leaf6342LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6342CoverageChecked :
    coverageCheck (innerAD leaf6342Box) leaf6342InnerLog = true := by
  rfl'

private theorem leaf6342InnerLogValid :
    leaf6342InnerLog.Valid 8 (innerAD leaf6342Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint96PositiveFacts.valid leaf6342CoverageChecked

private noncomputable def leaf6342InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629633/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6342InputLogOnePlusV_eq :
    leaf6342InputLogOnePlusV = outerEnclosure 24
      (leaf6342Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6342RoundedFacts : LeafRoundedFacts 8
    leaf6342Certificate.logOnePlusV leaf6342InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6342InputLogOnePlusV_eq }

private noncomputable def leaf6342Inputs : Inputs :=
  inputsOfCaches globalInput sk96RoundedInputs
    chi322InputQChi innerPair353Input
    leaf6342InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6342LowerChecked :
    lowerCheck 24 leaf6342Box leaf6342Inputs = true := by
  rfl'

private theorem leaf6342CoversExact : CoversExact 8
    leaf6342Box leaf6342Certificate leaf6342InnerLog leaf6342Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk96RoundedFacts chi322RoundedFacts
    innerPair353RoundedFacts leaf6342RoundedFacts (by rfl)

private theorem leaf6342FlatSound : Sound leaf6342Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6342CertificateValid
    leaf6342InnerLogValid leaf6342CoversExact leaf6342LowerChecked

private noncomputable def leaf6343Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (9/16), chiHi := (73/128) }

private noncomputable def leaf6343Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217967/134217728) }, vSqrt := { lower := (32765/32768), upper := (11452743679/11452075008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (351226707/268435456) }, upper := { exponent := 1, mantissa := (5479/4096) } }, logOuter := sk97LogOuterCertificate, logK := sk97LogKCertificate, logChi := chi335LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (22904818687/22904150016) } }, logDArg := sk97LogDArgCertificate }

private noncomputable def leaf6343InnerLog : WideLogData :=
  innerPair340Data

set_option maxRecDepth 1000000 in
private theorem leaf6343LocalValidity :
    LeafFacts leaf6343Box leaf6343Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6343Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (11452743679/11452075008) }) = true
      norm_num [leaf6343Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6343CertificateValid :
    WideCertificateValid leaf6343Box leaf6343Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk97ValidityFacts chi335ValidityFacts
    leaf6343LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6343CoverageChecked :
    coverageCheck (innerAD leaf6343Box) leaf6343InnerLog = true := by
  rfl'

private theorem leaf6343InnerLogValid :
    leaf6343InnerLog.Valid 8 (innerAD leaf6343Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint92PositiveFacts.valid leaf6343CoverageChecked

private noncomputable def leaf6343InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629571/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6343InputLogOnePlusV_eq :
    leaf6343InputLogOnePlusV = outerEnclosure 24
      (leaf6343Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6343RoundedFacts : LeafRoundedFacts 8
    leaf6343Certificate.logOnePlusV leaf6343InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6343InputLogOnePlusV_eq }

private noncomputable def leaf6343Inputs : Inputs :=
  inputsOfCaches globalInput sk97RoundedInputs
    chi335InputQChi innerPair340Input
    leaf6343InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6343LowerChecked :
    lowerCheck 24 leaf6343Box leaf6343Inputs = true := by
  rfl'

private theorem leaf6343CoversExact : CoversExact 8
    leaf6343Box leaf6343Certificate leaf6343InnerLog leaf6343Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk97RoundedFacts chi335RoundedFacts
    innerPair340RoundedFacts leaf6343RoundedFacts (by rfl)

private theorem leaf6343FlatSound : Sound leaf6343Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6343CertificateValid
    leaf6343InnerLogValid leaf6343CoversExact leaf6343LowerChecked

private noncomputable def leaf6344Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (73/128), chiHi := (37/64) }

private noncomputable def leaf6344Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217969/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34356176896) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (354241177/268435456) }, upper := { exponent := 1, mantissa := (2763/2048) } }, logOuter := sk97LogOuterCertificate, logK := sk97LogKCertificate, logChi := chi336LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714407933/68712353792) } }, logDArg := sk97LogDArgCertificate }

private noncomputable def leaf6344InnerLog : WideLogData :=
  innerPair346Data

set_option maxRecDepth 1000000 in
private theorem leaf6344LocalValidity :
    LeafFacts leaf6344Box leaf6344Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6344Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34356176896) }) = true
      norm_num [leaf6344Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6344CertificateValid :
    WideCertificateValid leaf6344Box leaf6344Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk97ValidityFacts chi336ValidityFacts
    leaf6344LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6344CoverageChecked :
    coverageCheck (innerAD leaf6344Box) leaf6344InnerLog = true := by
  rfl'

private theorem leaf6344InnerLogValid :
    leaf6344InnerLog.Valid 8 (innerAD leaf6344Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint93PositiveFacts.valid leaf6344CoverageChecked

private noncomputable def leaf6344InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814791/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6344InputLogOnePlusV_eq :
    leaf6344InputLogOnePlusV = outerEnclosure 24
      (leaf6344Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6344RoundedFacts : LeafRoundedFacts 8
    leaf6344Certificate.logOnePlusV leaf6344InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6344InputLogOnePlusV_eq }

private noncomputable def leaf6344Inputs : Inputs :=
  inputsOfCaches globalInput sk97RoundedInputs
    chi336InputQChi innerPair346Input
    leaf6344InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6344LowerChecked :
    lowerCheck 24 leaf6344Box leaf6344Inputs = true := by
  rfl'

private theorem leaf6344CoversExact : CoversExact 8
    leaf6344Box leaf6344Certificate leaf6344InnerLog leaf6344Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk97RoundedFacts chi336RoundedFacts
    innerPair346RoundedFacts leaf6344RoundedFacts (by rfl)

private theorem leaf6344FlatSound : Sound leaf6344Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6344CertificateValid
    leaf6344InnerLogValid leaf6344CoversExact leaf6344LowerChecked

private noncomputable def leaf6345Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (37/64), chiHi := (75/128) }

private noncomputable def leaf6345Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217971/134217728) }, vSqrt := { lower := (32765/32768), upper := (2642940849/2642779136) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (357255647/268435456) }, upper := { exponent := 1, mantissa := (5573/4096) } }, logOuter := sk97LogOuterCertificate, logK := sk97LogKCertificate, logChi := chi337LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (5285719985/5285558272) } }, logDArg := sk97LogDArgCertificate }

private noncomputable def leaf6345InnerLog : WideLogData :=
  innerPair346Data

set_option maxRecDepth 1000000 in
private theorem leaf6345LocalValidity :
    LeafFacts leaf6345Box leaf6345Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6345Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (2642940849/2642779136) }) = true
      norm_num [leaf6345Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6345CertificateValid :
    WideCertificateValid leaf6345Box leaf6345Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk97ValidityFacts chi337ValidityFacts
    leaf6345LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6345CoverageChecked :
    coverageCheck (innerAD leaf6345Box) leaf6345InnerLog = true := by
  rfl'

private theorem leaf6345InnerLogValid :
    leaf6345InnerLog.Valid 8 (innerAD leaf6345Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint93PositiveFacts.valid leaf6345CoverageChecked

private noncomputable def leaf6345InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814797/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6345InputLogOnePlusV_eq :
    leaf6345InputLogOnePlusV = outerEnclosure 24
      (leaf6345Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6345RoundedFacts : LeafRoundedFacts 8
    leaf6345Certificate.logOnePlusV leaf6345InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6345InputLogOnePlusV_eq }

private noncomputable def leaf6345Inputs : Inputs :=
  inputsOfCaches globalInput sk97RoundedInputs
    chi337InputQChi innerPair346Input
    leaf6345InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6345LowerChecked :
    lowerCheck 24 leaf6345Box leaf6345Inputs = true := by
  rfl'

private theorem leaf6345CoversExact : CoversExact 8
    leaf6345Box leaf6345Certificate leaf6345InnerLog leaf6345Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk97RoundedFacts chi337RoundedFacts
    innerPair346RoundedFacts leaf6345RoundedFacts (by rfl)

private theorem leaf6345FlatSound : Sound leaf6345Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6345CertificateValid
    leaf6345InnerLogValid leaf6345CoversExact leaf6345LowerChecked

private noncomputable def leaf6346Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (75/128), chiHi := (19/32) }

private noncomputable def leaf6346Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217973/134217728) }, vSqrt := { lower := (32765/32768), upper := (11452743679/11452026880) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (360270117/268435456) }, upper := { exponent := 1, mantissa := (1405/1024) } }, logOuter := sk97LogOuterCertificate, logK := sk97LogKCertificate, logChi := chi338LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (22904770559/22904053760) } }, logDArg := sk97LogDArgCertificate }

private noncomputable def leaf6346InnerLog : WideLogData :=
  innerPair346Data

set_option maxRecDepth 1000000 in
private theorem leaf6346LocalValidity :
    LeafFacts leaf6346Box leaf6346Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6346Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (11452743679/11452026880) }) = true
      norm_num [leaf6346Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6346CertificateValid :
    WideCertificateValid leaf6346Box leaf6346Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk97ValidityFacts chi338ValidityFacts
    leaf6346LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6346CoverageChecked :
    coverageCheck (innerAD leaf6346Box) leaf6346InnerLog = true := by
  rfl'

private theorem leaf6346InnerLogValid :
    leaf6346InnerLog.Valid 8 (innerAD leaf6346Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint93PositiveFacts.valid leaf6346CoverageChecked

private noncomputable def leaf6346InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814803/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6346InputLogOnePlusV_eq :
    leaf6346InputLogOnePlusV = outerEnclosure 24
      (leaf6346Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6346RoundedFacts : LeafRoundedFacts 8
    leaf6346Certificate.logOnePlusV leaf6346InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6346InputLogOnePlusV_eq }

private noncomputable def leaf6346Inputs : Inputs :=
  inputsOfCaches globalInput sk97RoundedInputs
    chi338InputQChi innerPair346Input
    leaf6346InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6346LowerChecked :
    lowerCheck 24 leaf6346Box leaf6346Inputs = true := by
  rfl'

private theorem leaf6346CoversExact : CoversExact 8
    leaf6346Box leaf6346Certificate leaf6346InnerLog leaf6346Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk97RoundedFacts chi338RoundedFacts
    innerPair346RoundedFacts leaf6346RoundedFacts (by rfl)

private theorem leaf6346FlatSound : Sound leaf6346Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6346CertificateValid
    leaf6346InnerLogValid leaf6346CoversExact leaf6346LowerChecked

private noncomputable def leaf6347Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (9/16), chiHi := (73/128) }

private noncomputable def leaf6347Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217969/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34356150272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (355945009/268435456) }, upper := { exponent := 1, mantissa := (347/256) } }, logOuter := sk98LogOuterCertificate, logK := sk98LogKCertificate, logChi := chi335LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68714381309/68712300544) } }, logDArg := sk98LogDArgCertificate }

private noncomputable def leaf6347InnerLog : WideLogData :=
  innerPair346Data

set_option maxRecDepth 1000000 in
private theorem leaf6347LocalValidity :
    LeafFacts leaf6347Box leaf6347Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6347Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34356150272) }) = true
      norm_num [leaf6347Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6347CertificateValid :
    WideCertificateValid leaf6347Box leaf6347Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk98ValidityFacts chi335ValidityFacts
    leaf6347LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6347CoverageChecked :
    coverageCheck (innerAD leaf6347Box) leaf6347InnerLog = true := by
  rfl'

private theorem leaf6347InnerLogValid :
    leaf6347InnerLog.Valid 8 (innerAD leaf6347Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint93PositiveFacts.valid leaf6347CoverageChecked

private noncomputable def leaf6347InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629589/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6347InputLogOnePlusV_eq :
    leaf6347InputLogOnePlusV = outerEnclosure 24
      (leaf6347Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6347RoundedFacts : LeafRoundedFacts 8
    leaf6347Certificate.logOnePlusV leaf6347InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6347InputLogOnePlusV_eq }

private noncomputable def leaf6347Inputs : Inputs :=
  inputsOfCaches globalInput sk98RoundedInputs
    chi335InputQChi innerPair346Input
    leaf6347InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6347LowerChecked :
    lowerCheck 24 leaf6347Box leaf6347Inputs = true := by
  rfl'

private theorem leaf6347CoversExact : CoversExact 8
    leaf6347Box leaf6347Certificate leaf6347InnerLog leaf6347Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk98RoundedFacts chi335RoundedFacts
    innerPair346RoundedFacts leaf6347RoundedFacts (by rfl)

private theorem leaf6347FlatSound : Sound leaf6347Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6347CertificateValid
    leaf6347InnerLogValid leaf6347CoversExact leaf6347LowerChecked

private noncomputable def leaf6348Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (73/128), chiHi := (37/64) }

private noncomputable def leaf6348Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217971/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34356101120) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (359025011/268435456) }, upper := { exponent := 1, mantissa := (175/128) } }, logOuter := sk98LogOuterCertificate, logK := sk98LogKCertificate, logChi := chi336LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68714332157/68712202240) } }, logDArg := sk98LogDArgCertificate }

private noncomputable def leaf6348InnerLog : WideLogData :=
  innerPair346Data

set_option maxRecDepth 1000000 in
private theorem leaf6348LocalValidity :
    LeafFacts leaf6348Box leaf6348Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6348Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34356101120) }) = true
      norm_num [leaf6348Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6348CertificateValid :
    WideCertificateValid leaf6348Box leaf6348Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk98ValidityFacts chi336ValidityFacts
    leaf6348LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6348CoverageChecked :
    coverageCheck (innerAD leaf6348Box) leaf6348InnerLog = true := by
  rfl'

private theorem leaf6348InnerLogValid :
    leaf6348InnerLog.Valid 8 (innerAD leaf6348Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint93PositiveFacts.valid leaf6348CoverageChecked

private noncomputable def leaf6348InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629601/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6348InputLogOnePlusV_eq :
    leaf6348InputLogOnePlusV = outerEnclosure 24
      (leaf6348Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6348RoundedFacts : LeafRoundedFacts 8
    leaf6348Certificate.logOnePlusV leaf6348InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6348InputLogOnePlusV_eq }

private noncomputable def leaf6348Inputs : Inputs :=
  inputsOfCaches globalInput sk98RoundedInputs
    chi336InputQChi innerPair346Input
    leaf6348InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6348LowerChecked :
    lowerCheck 24 leaf6348Box leaf6348Inputs = true := by
  rfl'

private theorem leaf6348CoversExact : CoversExact 8
    leaf6348Box leaf6348Certificate leaf6348InnerLog leaf6348Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk98RoundedFacts chi336RoundedFacts
    innerPair346RoundedFacts leaf6348RoundedFacts (by rfl)

private theorem leaf6348FlatSound : Sound leaf6348Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6348CertificateValid
    leaf6348InnerLogValid leaf6348CoversExact leaf6348LowerChecked

private noncomputable def leaf6349Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (37/64), chiHi := (75/128) }

private noncomputable def leaf6349Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217973/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34356051968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (362105013/268435456) }, upper := { exponent := 1, mantissa := (353/256) } }, logOuter := sk98LogOuterCertificate, logK := sk98LogKCertificate, logChi := chi337LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68714283005/68712103936) } }, logDArg := sk98LogDArgCertificate }

private noncomputable def leaf6349InnerLog : WideLogData :=
  innerPair353Data

set_option maxRecDepth 1000000 in
private theorem leaf6349LocalValidity :
    LeafFacts leaf6349Box leaf6349Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6349Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34356051968) }) = true
      norm_num [leaf6349Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6349CertificateValid :
    WideCertificateValid leaf6349Box leaf6349Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk98ValidityFacts chi337ValidityFacts
    leaf6349LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6349CoverageChecked :
    coverageCheck (innerAD leaf6349Box) leaf6349InnerLog = true := by
  rfl'

private theorem leaf6349InnerLogValid :
    leaf6349InnerLog.Valid 8 (innerAD leaf6349Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint96PositiveFacts.valid leaf6349CoverageChecked

private noncomputable def leaf6349InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629613/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6349InputLogOnePlusV_eq :
    leaf6349InputLogOnePlusV = outerEnclosure 24
      (leaf6349Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6349RoundedFacts : LeafRoundedFacts 8
    leaf6349Certificate.logOnePlusV leaf6349InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6349InputLogOnePlusV_eq }

private noncomputable def leaf6349Inputs : Inputs :=
  inputsOfCaches globalInput sk98RoundedInputs
    chi337InputQChi innerPair353Input
    leaf6349InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6349LowerChecked :
    lowerCheck 24 leaf6349Box leaf6349Inputs = true := by
  rfl'

private theorem leaf6349CoversExact : CoversExact 8
    leaf6349Box leaf6349Certificate leaf6349InnerLog leaf6349Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk98RoundedFacts chi337RoundedFacts
    innerPair353RoundedFacts leaf6349RoundedFacts (by rfl)

private theorem leaf6349FlatSound : Sound leaf6349Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6349CertificateValid
    leaf6349InnerLogValid leaf6349CoversExact leaf6349LowerChecked

private noncomputable def leaf6350Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (75/128), chiHi := (19/32) }

private noncomputable def leaf6350Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217975/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34356002816) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (365185015/268435456) }, upper := { exponent := 1, mantissa := (89/64) } }, logOuter := sk98LogOuterCertificate, logK := sk98LogKCertificate, logChi := chi338LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68714233853/68712005632) } }, logDArg := sk98LogDArgCertificate }

private noncomputable def leaf6350InnerLog : WideLogData :=
  innerPair353Data

set_option maxRecDepth 1000000 in
private theorem leaf6350LocalValidity :
    LeafFacts leaf6350Box leaf6350Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6350Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34356002816) }) = true
      norm_num [leaf6350Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6350CertificateValid :
    WideCertificateValid leaf6350Box leaf6350Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk98ValidityFacts chi338ValidityFacts
    leaf6350LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6350CoverageChecked :
    coverageCheck (innerAD leaf6350Box) leaf6350InnerLog = true := by
  rfl'

private theorem leaf6350InnerLogValid :
    leaf6350InnerLog.Valid 8 (innerAD leaf6350Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint96PositiveFacts.valid leaf6350CoverageChecked

private noncomputable def leaf6350InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629625/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6350InputLogOnePlusV_eq :
    leaf6350InputLogOnePlusV = outerEnclosure 24
      (leaf6350Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6350RoundedFacts : LeafRoundedFacts 8
    leaf6350Certificate.logOnePlusV leaf6350InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6350InputLogOnePlusV_eq }

private noncomputable def leaf6350Inputs : Inputs :=
  inputsOfCaches globalInput sk98RoundedInputs
    chi338InputQChi innerPair353Input
    leaf6350InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6350LowerChecked :
    lowerCheck 24 leaf6350Box leaf6350Inputs = true := by
  rfl'

private theorem leaf6350CoversExact : CoversExact 8
    leaf6350Box leaf6350Certificate leaf6350InnerLog leaf6350Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk98RoundedFacts chi338RoundedFacts
    innerPair353RoundedFacts leaf6350RoundedFacts (by rfl)

private theorem leaf6350FlatSound : Sound leaf6350Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6350CertificateValid
    leaf6350InnerLogValid leaf6350CoversExact leaf6350LowerChecked

private noncomputable def leaf6351Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (19/32), chiHi := (39/64) }

private noncomputable def leaf6351Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109035/67108864) }, vSqrt := { lower := (32765/32768), upper := (483918747/483887104) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (181625863/134217728) }, upper := { exponent := 1, mantissa := (2857/2048) } }, logOuter := sk97LogOuterCertificate, logK := sk97LogKCertificate, logChi := chi321LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (967805851/967774208) } }, logDArg := sk97LogDArgCertificate }

private noncomputable def leaf6351InnerLog : WideLogData :=
  innerPair711Data

set_option maxRecDepth 1000000 in
private theorem leaf6351LocalValidity :
    LeafFacts leaf6351Box leaf6351Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6351Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (483918747/483887104) }) = true
      norm_num [leaf6351Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6351CertificateValid :
    WideCertificateValid leaf6351Box leaf6351Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk97ValidityFacts chi321ValidityFacts
    leaf6351LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6351CoverageChecked :
    coverageCheck (innerAD leaf6351Box) leaf6351InnerLog = true := by
  rfl'

private theorem leaf6351InnerLogValid :
    leaf6351InnerLog.Valid 8 (innerAD leaf6351Box) :=
  wideLogDataValid_of_cachedCheck endpoint451PositiveFacts
    endpoint480PositiveFacts.valid leaf6351CoverageChecked

private noncomputable def leaf6351InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629629/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6351InputLogOnePlusV_eq :
    leaf6351InputLogOnePlusV = outerEnclosure 24
      (leaf6351Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6351RoundedFacts : LeafRoundedFacts 8
    leaf6351Certificate.logOnePlusV leaf6351InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6351InputLogOnePlusV_eq }

private noncomputable def leaf6351Inputs : Inputs :=
  inputsOfCaches globalInput sk97RoundedInputs
    chi321InputQChi innerPair711Input
    leaf6351InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6351LowerChecked :
    lowerCheck 24 leaf6351Box leaf6351Inputs = true := by
  rfl'

private theorem leaf6351CoversExact : CoversExact 8
    leaf6351Box leaf6351Certificate leaf6351InnerLog leaf6351Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk97RoundedFacts chi321RoundedFacts
    innerPair711RoundedFacts leaf6351RoundedFacts (by rfl)

private theorem leaf6351FlatSound : Sound leaf6351Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6351CertificateValid
    leaf6351InnerLogValid leaf6351CoversExact leaf6351LowerChecked

private noncomputable def leaf6352Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (39/64), chiHi := (5/8) }

private noncomputable def leaf6352Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109037/67108864) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34355888128) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (184640333/134217728) }, upper := { exponent := 1, mantissa := (363/256) } }, logOuter := sk97LogOuterCertificate, logK := sk97LogKCertificate, logChi := chi322LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714119165/68711776256) } }, logDArg := sk97LogDArgCertificate }

private noncomputable def leaf6352InnerLog : WideLogData :=
  innerPair360Data

set_option maxRecDepth 1000000 in
private theorem leaf6352LocalValidity :
    LeafFacts leaf6352Box leaf6352Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6352Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34355888128) }) = true
      norm_num [leaf6352Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6352CertificateValid :
    WideCertificateValid leaf6352Box leaf6352Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk97ValidityFacts chi322ValidityFacts
    leaf6352LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6352CoverageChecked :
    coverageCheck (innerAD leaf6352Box) leaf6352InnerLog = true := by
  rfl'

private theorem leaf6352InnerLogValid :
    leaf6352InnerLog.Valid 8 (innerAD leaf6352Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint469PositiveFacts.valid leaf6352CoverageChecked

private noncomputable def leaf6352InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629653/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6352InputLogOnePlusV_eq :
    leaf6352InputLogOnePlusV = outerEnclosure 24
      (leaf6352Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6352RoundedFacts : LeafRoundedFacts 8
    leaf6352Certificate.logOnePlusV leaf6352InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6352InputLogOnePlusV_eq }

private noncomputable def leaf6352Inputs : Inputs :=
  inputsOfCaches globalInput sk97RoundedInputs
    chi322InputQChi innerPair360Input
    leaf6352InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6352LowerChecked :
    lowerCheck 24 leaf6352Box leaf6352Inputs = true := by
  rfl'

private theorem leaf6352CoversExact : CoversExact 8
    leaf6352Box leaf6352Certificate leaf6352InnerLog leaf6352Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk97RoundedFacts chi322RoundedFacts
    innerPair360RoundedFacts leaf6352RoundedFacts (by rfl)

private theorem leaf6352FlatSound : Sound leaf6352Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6352CertificateValid
    leaf6352InnerLogValid leaf6352CoversExact leaf6352LowerChecked

private noncomputable def leaf6353Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (19/32), chiHi := (77/128) }

private noncomputable def leaf6353Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217977/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34355953664) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (368265017/268435456) }, upper := { exponent := 1, mantissa := (359/256) } }, logOuter := sk98LogOuterCertificate, logK := sk98LogKCertificate, logChi := chi339LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68714184701/68711907328) } }, logDArg := sk98LogDArgCertificate }

private noncomputable def leaf6353InnerLog : WideLogData :=
  innerPair353Data

set_option maxRecDepth 1000000 in
private theorem leaf6353LocalValidity :
    LeafFacts leaf6353Box leaf6353Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6353Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34355953664) }) = true
      norm_num [leaf6353Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6353CertificateValid :
    WideCertificateValid leaf6353Box leaf6353Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk98ValidityFacts chi339ValidityFacts
    leaf6353LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6353CoverageChecked :
    coverageCheck (innerAD leaf6353Box) leaf6353InnerLog = true := by
  rfl'

private theorem leaf6353InnerLogValid :
    leaf6353InnerLog.Valid 8 (innerAD leaf6353Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint96PositiveFacts.valid leaf6353CoverageChecked

private noncomputable def leaf6353InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629637/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6353InputLogOnePlusV_eq :
    leaf6353InputLogOnePlusV = outerEnclosure 24
      (leaf6353Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6353RoundedFacts : LeafRoundedFacts 8
    leaf6353Certificate.logOnePlusV leaf6353InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6353InputLogOnePlusV_eq }

private noncomputable def leaf6353Inputs : Inputs :=
  inputsOfCaches globalInput sk98RoundedInputs
    chi339InputQChi innerPair353Input
    leaf6353InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6353LowerChecked :
    lowerCheck 24 leaf6353Box leaf6353Inputs = true := by
  rfl'

private theorem leaf6353CoversExact : CoversExact 8
    leaf6353Box leaf6353Certificate leaf6353InnerLog leaf6353Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk98RoundedFacts chi339RoundedFacts
    innerPair353RoundedFacts leaf6353RoundedFacts (by rfl)

private theorem leaf6353FlatSound : Sound leaf6353Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6353CertificateValid
    leaf6353InnerLogValid leaf6353CoversExact leaf6353LowerChecked

private noncomputable def leaf6354Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (77/128), chiHi := (39/64) }

private noncomputable def leaf6354Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217979/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34355904512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (371345019/268435456) }, upper := { exponent := 1, mantissa := (181/128) } }, logOuter := sk98LogOuterCertificate, logK := sk98LogKCertificate, logChi := chi340LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68714135549/68711809024) } }, logDArg := sk98LogDArgCertificate }

private noncomputable def leaf6354InnerLog : WideLogData :=
  innerPair357Data

set_option maxRecDepth 1000000 in
private theorem leaf6354LocalValidity :
    LeafFacts leaf6354Box leaf6354Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6354Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34355904512) }) = true
      norm_num [leaf6354Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6354CertificateValid :
    WideCertificateValid leaf6354Box leaf6354Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk98ValidityFacts chi340ValidityFacts
    leaf6354LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6354CoverageChecked :
    coverageCheck (innerAD leaf6354Box) leaf6354InnerLog = true := by
  rfl'

private theorem leaf6354InnerLogValid :
    leaf6354InnerLog.Valid 8 (innerAD leaf6354Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint97PositiveFacts.valid leaf6354CoverageChecked

private noncomputable def leaf6354InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629649/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6354InputLogOnePlusV_eq :
    leaf6354InputLogOnePlusV = outerEnclosure 24
      (leaf6354Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6354RoundedFacts : LeafRoundedFacts 8
    leaf6354Certificate.logOnePlusV leaf6354InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6354InputLogOnePlusV_eq }

private noncomputable def leaf6354Inputs : Inputs :=
  inputsOfCaches globalInput sk98RoundedInputs
    chi340InputQChi innerPair357Input
    leaf6354InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6354LowerChecked :
    lowerCheck 24 leaf6354Box leaf6354Inputs = true := by
  rfl'

private theorem leaf6354CoversExact : CoversExact 8
    leaf6354Box leaf6354Certificate leaf6354InnerLog leaf6354Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk98RoundedFacts chi340RoundedFacts
    innerPair357RoundedFacts leaf6354RoundedFacts (by rfl)

private theorem leaf6354FlatSound : Sound leaf6354Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6354CertificateValid
    leaf6354InnerLogValid leaf6354CoversExact leaf6354LowerChecked

private noncomputable def leaf6355Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (39/64), chiHi := (5/8) }

private noncomputable def leaf6355Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109039/67108864) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34355806208) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (187196079/134217728) }, upper := { exponent := 1, mantissa := (23/16) } }, logOuter := sk98LogOuterCertificate, logK := sk98LogKCertificate, logChi := chi322LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68714037245/68711612416) } }, logDArg := sk98LogDArgCertificate }

private noncomputable def leaf6355InnerLog : WideLogData :=
  innerPair357Data

set_option maxRecDepth 1000000 in
private theorem leaf6355LocalValidity :
    LeafFacts leaf6355Box leaf6355Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6355Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34355806208) }) = true
      norm_num [leaf6355Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6355CertificateValid :
    WideCertificateValid leaf6355Box leaf6355Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk98ValidityFacts chi322ValidityFacts
    leaf6355LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6355CoverageChecked :
    coverageCheck (innerAD leaf6355Box) leaf6355InnerLog = true := by
  rfl'

private theorem leaf6355InnerLogValid :
    leaf6355InnerLog.Valid 8 (innerAD leaf6355Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint97PositiveFacts.valid leaf6355CoverageChecked

private noncomputable def leaf6355InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629673/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6355InputLogOnePlusV_eq :
    leaf6355InputLogOnePlusV = outerEnclosure 24
      (leaf6355Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6355RoundedFacts : LeafRoundedFacts 8
    leaf6355Certificate.logOnePlusV leaf6355InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6355InputLogOnePlusV_eq }

private noncomputable def leaf6355Inputs : Inputs :=
  inputsOfCaches globalInput sk98RoundedInputs
    chi322InputQChi innerPair357Input
    leaf6355InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6355LowerChecked :
    lowerCheck 24 leaf6355Box leaf6355Inputs = true := by
  rfl'

private theorem leaf6355CoversExact : CoversExact 8
    leaf6355Box leaf6355Certificate leaf6355InnerLog leaf6355Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk98RoundedFacts chi322RoundedFacts
    innerPair357RoundedFacts leaf6355RoundedFacts (by rfl)

private theorem leaf6355FlatSound : Sound leaf6355Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6355CertificateValid
    leaf6355InnerLogValid leaf6355CoversExact leaf6355LowerChecked

private noncomputable def component127Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (1/2), chiHi := (33/64) }

set_option maxRecDepth 1000000 in
private theorem component127Node0_sound : Sound component127Node0Box :=
  sound_of_literal_split component127Node0Box leaf6301Box leaf6302Box
    .chi (65/128) (by rfl) (by rfl)
    leaf6301FlatSound leaf6302FlatSound

private noncomputable def component127Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (33/64), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component127Node1_sound : Sound component127Node1Box :=
  sound_of_literal_split component127Node1Box leaf6303Box leaf6304Box
    .chi (67/128) (by rfl) (by rfl)
    leaf6303FlatSound leaf6304FlatSound

private noncomputable def component127Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (1/2), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component127Node2_sound : Sound component127Node2Box :=
  sound_of_literal_split component127Node2Box component127Node0Box component127Node1Box
    .chi (33/64) (by rfl) (by rfl)
    component127Node0_sound component127Node1_sound

private noncomputable def component127Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (1/2), chiHi := (33/64) }

set_option maxRecDepth 1000000 in
private theorem component127Node3_sound : Sound component127Node3Box :=
  sound_of_literal_split component127Node3Box leaf6305Box leaf6306Box
    .chi (65/128) (by rfl) (by rfl)
    leaf6305FlatSound leaf6306FlatSound

private noncomputable def component127Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (33/64), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component127Node4_sound : Sound component127Node4Box :=
  sound_of_literal_split component127Node4Box leaf6307Box leaf6308Box
    .chi (67/128) (by rfl) (by rfl)
    leaf6307FlatSound leaf6308FlatSound

private noncomputable def component127Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (1/2), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component127Node5_sound : Sound component127Node5Box :=
  sound_of_literal_split component127Node5Box component127Node3Box component127Node4Box
    .chi (33/64) (by rfl) (by rfl)
    component127Node3_sound component127Node4_sound

private noncomputable def component127Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (1/2), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component127Node6_sound : Sound component127Node6Box :=
  sound_of_literal_split component127Node6Box component127Node2Box component127Node5Box
    .k (45/16) (by rfl) (by rfl)
    component127Node2_sound component127Node5_sound

private noncomputable def component127Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (17/32), chiHi := (35/64) }

set_option maxRecDepth 1000000 in
private theorem component127Node7_sound : Sound component127Node7Box :=
  sound_of_literal_split component127Node7Box leaf6309Box leaf6310Box
    .chi (69/128) (by rfl) (by rfl)
    leaf6309FlatSound leaf6310FlatSound

private noncomputable def component127Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (35/64), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component127Node8_sound : Sound component127Node8Box :=
  sound_of_literal_split component127Node8Box leaf6311Box leaf6312Box
    .chi (71/128) (by rfl) (by rfl)
    leaf6311FlatSound leaf6312FlatSound

private noncomputable def component127Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (17/32), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component127Node9_sound : Sound component127Node9Box :=
  sound_of_literal_split component127Node9Box component127Node7Box component127Node8Box
    .chi (35/64) (by rfl) (by rfl)
    component127Node7_sound component127Node8_sound

private noncomputable def component127Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (17/32), chiHi := (35/64) }

set_option maxRecDepth 1000000 in
private theorem component127Node10_sound : Sound component127Node10Box :=
  sound_of_literal_split component127Node10Box leaf6313Box leaf6314Box
    .chi (69/128) (by rfl) (by rfl)
    leaf6313FlatSound leaf6314FlatSound

private noncomputable def component127Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (35/64), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component127Node11_sound : Sound component127Node11Box :=
  sound_of_literal_split component127Node11Box leaf6315Box leaf6316Box
    .chi (71/128) (by rfl) (by rfl)
    leaf6315FlatSound leaf6316FlatSound

private noncomputable def component127Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (17/32), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component127Node12_sound : Sound component127Node12Box :=
  sound_of_literal_split component127Node12Box component127Node10Box component127Node11Box
    .chi (35/64) (by rfl) (by rfl)
    component127Node10_sound component127Node11_sound

private noncomputable def component127Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (17/32), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component127Node13_sound : Sound component127Node13Box :=
  sound_of_literal_split component127Node13Box component127Node9Box component127Node12Box
    .k (45/16) (by rfl) (by rfl)
    component127Node9_sound component127Node12_sound

private noncomputable def component127Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (1/2), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component127Node14_sound : Sound component127Node14Box :=
  sound_of_literal_split component127Node14Box component127Node6Box component127Node13Box
    .chi (17/32) (by rfl) (by rfl)
    component127Node6_sound component127Node13_sound

private noncomputable def component127Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (1/2), chiHi := (33/64) }

set_option maxRecDepth 1000000 in
private theorem component127Node15_sound : Sound component127Node15Box :=
  sound_of_literal_split component127Node15Box leaf6317Box leaf6318Box
    .chi (65/128) (by rfl) (by rfl)
    leaf6317FlatSound leaf6318FlatSound

private noncomputable def component127Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (33/64), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component127Node16_sound : Sound component127Node16Box :=
  sound_of_literal_split component127Node16Box leaf6319Box leaf6320Box
    .chi (67/128) (by rfl) (by rfl)
    leaf6319FlatSound leaf6320FlatSound

private noncomputable def component127Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (1/2), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component127Node17_sound : Sound component127Node17Box :=
  sound_of_literal_split component127Node17Box component127Node15Box component127Node16Box
    .chi (33/64) (by rfl) (by rfl)
    component127Node15_sound component127Node16_sound

private noncomputable def component127Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (1/2), chiHi := (33/64) }

set_option maxRecDepth 1000000 in
private theorem component127Node18_sound : Sound component127Node18Box :=
  sound_of_literal_split component127Node18Box leaf6321Box leaf6322Box
    .chi (65/128) (by rfl) (by rfl)
    leaf6321FlatSound leaf6322FlatSound

private noncomputable def component127Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (33/64), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component127Node19_sound : Sound component127Node19Box :=
  sound_of_literal_split component127Node19Box leaf6323Box leaf6324Box
    .chi (67/128) (by rfl) (by rfl)
    leaf6323FlatSound leaf6324FlatSound

private noncomputable def component127Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (1/2), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component127Node20_sound : Sound component127Node20Box :=
  sound_of_literal_split component127Node20Box component127Node18Box component127Node19Box
    .chi (33/64) (by rfl) (by rfl)
    component127Node18_sound component127Node19_sound

private noncomputable def component127Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (1/2), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component127Node21_sound : Sound component127Node21Box :=
  sound_of_literal_split component127Node21Box component127Node17Box component127Node20Box
    .k (47/16) (by rfl) (by rfl)
    component127Node17_sound component127Node20_sound

private noncomputable def component127Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (17/32), chiHi := (35/64) }

set_option maxRecDepth 1000000 in
private theorem component127Node22_sound : Sound component127Node22Box :=
  sound_of_literal_split component127Node22Box leaf6325Box leaf6326Box
    .chi (69/128) (by rfl) (by rfl)
    leaf6325FlatSound leaf6326FlatSound

private noncomputable def component127Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (35/64), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component127Node23_sound : Sound component127Node23Box :=
  sound_of_literal_split component127Node23Box leaf6327Box leaf6328Box
    .chi (71/128) (by rfl) (by rfl)
    leaf6327FlatSound leaf6328FlatSound

private noncomputable def component127Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (17/32), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component127Node24_sound : Sound component127Node24Box :=
  sound_of_literal_split component127Node24Box component127Node22Box component127Node23Box
    .chi (35/64) (by rfl) (by rfl)
    component127Node22_sound component127Node23_sound

private noncomputable def component127Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (17/32), chiHi := (35/64) }

set_option maxRecDepth 1000000 in
private theorem component127Node25_sound : Sound component127Node25Box :=
  sound_of_literal_split component127Node25Box leaf6329Box leaf6330Box
    .chi (69/128) (by rfl) (by rfl)
    leaf6329FlatSound leaf6330FlatSound

private noncomputable def component127Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (35/64), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component127Node26_sound : Sound component127Node26Box :=
  sound_of_literal_split component127Node26Box leaf6331Box leaf6332Box
    .chi (71/128) (by rfl) (by rfl)
    leaf6331FlatSound leaf6332FlatSound

private noncomputable def component127Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (17/32), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component127Node27_sound : Sound component127Node27Box :=
  sound_of_literal_split component127Node27Box component127Node25Box component127Node26Box
    .chi (35/64) (by rfl) (by rfl)
    component127Node25_sound component127Node26_sound

private noncomputable def component127Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (17/32), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component127Node28_sound : Sound component127Node28Box :=
  sound_of_literal_split component127Node28Box component127Node24Box component127Node27Box
    .k (47/16) (by rfl) (by rfl)
    component127Node24_sound component127Node27_sound

private noncomputable def component127Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (1/2), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component127Node29_sound : Sound component127Node29Box :=
  sound_of_literal_split component127Node29Box component127Node21Box component127Node28Box
    .chi (17/32) (by rfl) (by rfl)
    component127Node21_sound component127Node28_sound

private noncomputable def component127Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (3), chiLo := (1/2), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component127Node30_sound : Sound component127Node30Box :=
  sound_of_literal_split component127Node30Box component127Node14Box component127Node29Box
    .k (23/8) (by rfl) (by rfl)
    component127Node14_sound component127Node29_sound

private noncomputable def component127Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (9/16), chiHi := (37/64) }

set_option maxRecDepth 1000000 in
private theorem component127Node31_sound : Sound component127Node31Box :=
  sound_of_literal_split component127Node31Box leaf6333Box leaf6334Box
    .chi (73/128) (by rfl) (by rfl)
    leaf6333FlatSound leaf6334FlatSound

private noncomputable def component127Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (9/16), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component127Node32_sound : Sound component127Node32Box :=
  sound_of_literal_split component127Node32Box component127Node31Box leaf6335Box
    .chi (37/64) (by rfl) (by rfl)
    component127Node31_sound leaf6335FlatSound

private noncomputable def component127Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (9/16), chiHi := (37/64) }

set_option maxRecDepth 1000000 in
private theorem component127Node33_sound : Sound component127Node33Box :=
  sound_of_literal_split component127Node33Box leaf6336Box leaf6337Box
    .chi (73/128) (by rfl) (by rfl)
    leaf6336FlatSound leaf6337FlatSound

private noncomputable def component127Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (9/16), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component127Node34_sound : Sound component127Node34Box :=
  sound_of_literal_split component127Node34Box component127Node33Box leaf6338Box
    .chi (37/64) (by rfl) (by rfl)
    component127Node33_sound leaf6338FlatSound

private noncomputable def component127Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (9/16), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component127Node35_sound : Sound component127Node35Box :=
  sound_of_literal_split component127Node35Box component127Node32Box component127Node34Box
    .k (45/16) (by rfl) (by rfl)
    component127Node32_sound component127Node34_sound

private noncomputable def component127Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (19/32), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component127Node36_sound : Sound component127Node36Box :=
  sound_of_literal_split component127Node36Box leaf6339Box leaf6340Box
    .chi (39/64) (by rfl) (by rfl)
    leaf6339FlatSound leaf6340FlatSound

private noncomputable def component127Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (19/32), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component127Node37_sound : Sound component127Node37Box :=
  sound_of_literal_split component127Node37Box leaf6341Box leaf6342Box
    .chi (39/64) (by rfl) (by rfl)
    leaf6341FlatSound leaf6342FlatSound

private noncomputable def component127Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (19/32), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component127Node38_sound : Sound component127Node38Box :=
  sound_of_literal_split component127Node38Box component127Node36Box component127Node37Box
    .k (45/16) (by rfl) (by rfl)
    component127Node36_sound component127Node37_sound

private noncomputable def component127Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (9/16), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component127Node39_sound : Sound component127Node39Box :=
  sound_of_literal_split component127Node39Box component127Node35Box component127Node38Box
    .chi (19/32) (by rfl) (by rfl)
    component127Node35_sound component127Node38_sound

private noncomputable def component127Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (9/16), chiHi := (37/64) }

set_option maxRecDepth 1000000 in
private theorem component127Node40_sound : Sound component127Node40Box :=
  sound_of_literal_split component127Node40Box leaf6343Box leaf6344Box
    .chi (73/128) (by rfl) (by rfl)
    leaf6343FlatSound leaf6344FlatSound

private noncomputable def component127Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (37/64), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component127Node41_sound : Sound component127Node41Box :=
  sound_of_literal_split component127Node41Box leaf6345Box leaf6346Box
    .chi (75/128) (by rfl) (by rfl)
    leaf6345FlatSound leaf6346FlatSound

private noncomputable def component127Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (9/16), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component127Node42_sound : Sound component127Node42Box :=
  sound_of_literal_split component127Node42Box component127Node40Box component127Node41Box
    .chi (37/64) (by rfl) (by rfl)
    component127Node40_sound component127Node41_sound

private noncomputable def component127Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (9/16), chiHi := (37/64) }

set_option maxRecDepth 1000000 in
private theorem component127Node43_sound : Sound component127Node43Box :=
  sound_of_literal_split component127Node43Box leaf6347Box leaf6348Box
    .chi (73/128) (by rfl) (by rfl)
    leaf6347FlatSound leaf6348FlatSound

private noncomputable def component127Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (37/64), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component127Node44_sound : Sound component127Node44Box :=
  sound_of_literal_split component127Node44Box leaf6349Box leaf6350Box
    .chi (75/128) (by rfl) (by rfl)
    leaf6349FlatSound leaf6350FlatSound

private noncomputable def component127Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (9/16), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component127Node45_sound : Sound component127Node45Box :=
  sound_of_literal_split component127Node45Box component127Node43Box component127Node44Box
    .chi (37/64) (by rfl) (by rfl)
    component127Node43_sound component127Node44_sound

private noncomputable def component127Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (9/16), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component127Node46_sound : Sound component127Node46Box :=
  sound_of_literal_split component127Node46Box component127Node42Box component127Node45Box
    .k (47/16) (by rfl) (by rfl)
    component127Node42_sound component127Node45_sound

private noncomputable def component127Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (19/32), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component127Node47_sound : Sound component127Node47Box :=
  sound_of_literal_split component127Node47Box leaf6351Box leaf6352Box
    .chi (39/64) (by rfl) (by rfl)
    leaf6351FlatSound leaf6352FlatSound

private noncomputable def component127Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (19/32), chiHi := (39/64) }

set_option maxRecDepth 1000000 in
private theorem component127Node48_sound : Sound component127Node48Box :=
  sound_of_literal_split component127Node48Box leaf6353Box leaf6354Box
    .chi (77/128) (by rfl) (by rfl)
    leaf6353FlatSound leaf6354FlatSound

private noncomputable def component127Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (19/32), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component127Node49_sound : Sound component127Node49Box :=
  sound_of_literal_split component127Node49Box component127Node48Box leaf6355Box
    .chi (39/64) (by rfl) (by rfl)
    component127Node48_sound leaf6355FlatSound

private noncomputable def component127Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (19/32), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component127Node50_sound : Sound component127Node50Box :=
  sound_of_literal_split component127Node50Box component127Node47Box component127Node49Box
    .k (47/16) (by rfl) (by rfl)
    component127Node47_sound component127Node49_sound

private noncomputable def component127Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (9/16), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component127Node51_sound : Sound component127Node51Box :=
  sound_of_literal_split component127Node51Box component127Node46Box component127Node50Box
    .chi (19/32) (by rfl) (by rfl)
    component127Node46_sound component127Node50_sound

private noncomputable def component127Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (3), chiLo := (9/16), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component127Node52_sound : Sound component127Node52Box :=
  sound_of_literal_split component127Node52Box component127Node39Box component127Node51Box
    .k (23/8) (by rfl) (by rfl)
    component127Node39_sound component127Node51_sound

noncomputable def component127Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (3), chiLo := (1/2), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
theorem component127_sound : Sound component127Box :=
  sound_of_literal_split component127Box component127Node30Box component127Node52Box
    .chi (9/16) (by rfl) (by rfl)
    component127Node30_sound component127Node52_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
