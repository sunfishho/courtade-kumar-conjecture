import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch6
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

private noncomputable def leaf1287Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (7/32), chiHi := (29/128) }

private noncomputable def leaf1287Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435691/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905611264) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (429873303/268435456) }, upper := { exponent := 0, mantissa := (6677/4096) } }, logOuter := sk107LogOuterCertificate, logK := sk107LogKCertificate, logChi := chi119LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811775829/45811222528) } }, logDArg := sk107LogDArgCertificate }

private noncomputable def leaf1287InnerLog : WideLogData :=
  innerPair157Data

set_option maxRecDepth 1000000 in
private theorem leaf1287LocalValidity :
    LeafFacts leaf1287Box leaf1287Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1287Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905611264) }) = true
      norm_num [leaf1287Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1287CertificateValid :
    WideCertificateValid leaf1287Box leaf1287Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk107ValidityFacts chi119ValidityFacts
    leaf1287LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1287CoverageChecked :
    coverageCheck (innerAD leaf1287Box) leaf1287InnerLog = true := by
  rfl'

private theorem leaf1287InnerLogValid :
    leaf1287InnerLog.Valid 8 (innerAD leaf1287Box) :=
  wideLogDataValid_of_cachedCheck endpoint44PositiveFacts
    endpoint45PositiveFacts.valid leaf1287CoverageChecked

private noncomputable def leaf1287InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629283/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1287InputLogOnePlusV_eq :
    leaf1287InputLogOnePlusV = outerEnclosure 24
      (leaf1287Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1287RoundedFacts : LeafRoundedFacts 8
    leaf1287Certificate.logOnePlusV leaf1287InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1287InputLogOnePlusV_eq }

private noncomputable def leaf1287Inputs : Inputs :=
  inputsOfCaches globalInput sk107RoundedInputs
    chi119InputQChi innerPair157Input
    leaf1287InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1287LowerChecked :
    lowerCheck 24 leaf1287Box leaf1287Inputs = true := by
  rfl'

private theorem leaf1287CoversExact : CoversExact 8
    leaf1287Box leaf1287Certificate leaf1287InnerLog leaf1287Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk107RoundedFacts chi119RoundedFacts
    innerPair157RoundedFacts leaf1287RoundedFacts (by rfl)

private theorem leaf1287FlatSound : Sound leaf1287Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1287CertificateValid
    leaf1287InnerLogValid leaf1287CoversExact leaf1287LowerChecked

private noncomputable def leaf1288Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (29/128), chiHi := (15/64) }

private noncomputable def leaf1288Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435693/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716742656) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (435640117/268435456) }, upper := { exponent := 0, mantissa := (3383/2048) } }, logOuter := sk107LogOuterCertificate, logK := sk107LogKCertificate, logChi := chi120LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435236351/137433485312) } }, logDArg := sk107LogDArgCertificate }

private noncomputable def leaf1288InnerLog : WideLogData :=
  innerPair167Data

set_option maxRecDepth 1000000 in
private theorem leaf1288LocalValidity :
    LeafFacts leaf1288Box leaf1288Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1288Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716742656) }) = true
      norm_num [leaf1288Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1288CertificateValid :
    WideCertificateValid leaf1288Box leaf1288Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk107ValidityFacts chi120ValidityFacts
    leaf1288LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1288CoverageChecked :
    coverageCheck (innerAD leaf1288Box) leaf1288InnerLog = true := by
  rfl'

private theorem leaf1288InnerLogValid :
    leaf1288InnerLog.Valid 8 (innerAD leaf1288Box) :=
  wideLogDataValid_of_cachedCheck endpoint46PositiveFacts
    endpoint48PositiveFacts.valid leaf1288CoverageChecked

private noncomputable def leaf1288InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629295/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1288InputLogOnePlusV_eq :
    leaf1288InputLogOnePlusV = outerEnclosure 24
      (leaf1288Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1288RoundedFacts : LeafRoundedFacts 8
    leaf1288Certificate.logOnePlusV leaf1288InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1288InputLogOnePlusV_eq }

private noncomputable def leaf1288Inputs : Inputs :=
  inputsOfCaches globalInput sk107RoundedInputs
    chi120InputQChi innerPair167Input
    leaf1288InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1288LowerChecked :
    lowerCheck 24 leaf1288Box leaf1288Inputs = true := by
  rfl'

private theorem leaf1288CoversExact : CoversExact 8
    leaf1288Box leaf1288Certificate leaf1288InnerLog leaf1288Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk107RoundedFacts chi120RoundedFacts
    innerPair167RoundedFacts leaf1288RoundedFacts (by rfl)

private theorem leaf1288FlatSound : Sound leaf1288Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1288CertificateValid
    leaf1288InnerLogValid leaf1288CoversExact leaf1288LowerChecked

private noncomputable def leaf1289Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (7/32), chiHi := (29/128) }

private noncomputable def leaf1289Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435693/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716804096) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (431708197/268435456) }, upper := { exponent := 0, mantissa := (3353/2048) } }, logOuter := sk108LogOuterCertificate, logK := sk108LogKCertificate, logChi := chi119LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435297791/137433608192) } }, logDArg := sk108LogDArgCertificate }

private noncomputable def leaf1289InnerLog : WideLogData :=
  innerPair157Data

set_option maxRecDepth 1000000 in
private theorem leaf1289LocalValidity :
    LeafFacts leaf1289Box leaf1289Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1289Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716804096) }) = true
      norm_num [leaf1289Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1289CertificateValid :
    WideCertificateValid leaf1289Box leaf1289Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk108ValidityFacts chi119ValidityFacts
    leaf1289LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1289CoverageChecked :
    coverageCheck (innerAD leaf1289Box) leaf1289InnerLog = true := by
  rfl'

private theorem leaf1289InnerLogValid :
    leaf1289InnerLog.Valid 8 (innerAD leaf1289Box) :=
  wideLogDataValid_of_cachedCheck endpoint44PositiveFacts
    endpoint45PositiveFacts.valid leaf1289CoverageChecked

private noncomputable def leaf1289InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629287/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1289InputLogOnePlusV_eq :
    leaf1289InputLogOnePlusV = outerEnclosure 24
      (leaf1289Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1289RoundedFacts : LeafRoundedFacts 8
    leaf1289Certificate.logOnePlusV leaf1289InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1289InputLogOnePlusV_eq }

private noncomputable def leaf1289Inputs : Inputs :=
  inputsOfCaches globalInput sk108RoundedInputs
    chi119InputQChi innerPair157Input
    leaf1289InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1289LowerChecked :
    lowerCheck 24 leaf1289Box leaf1289Inputs = true := by
  rfl'

private theorem leaf1289CoversExact : CoversExact 8
    leaf1289Box leaf1289Certificate leaf1289InnerLog leaf1289Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk108RoundedFacts chi119RoundedFacts
    innerPair157RoundedFacts leaf1289RoundedFacts (by rfl)

private theorem leaf1289FlatSound : Sound leaf1289Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1289CertificateValid
    leaf1289InnerLogValid leaf1289CoversExact leaf1289LowerChecked

private noncomputable def leaf1290Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (29/128), chiHi := (15/64) }

private noncomputable def leaf1290Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435695/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716711936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (437540543/268435456) }, upper := { exponent := 0, mantissa := (1699/1024) } }, logOuter := sk108LogOuterCertificate, logK := sk108LogKCertificate, logChi := chi120LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435205631/137433423872) } }, logDArg := sk108LogDArgCertificate }

private noncomputable def leaf1290InnerLog : WideLogData :=
  innerPair62Data

set_option maxRecDepth 1000000 in
private theorem leaf1290LocalValidity :
    LeafFacts leaf1290Box leaf1290Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1290Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716711936) }) = true
      norm_num [leaf1290Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1290CertificateValid :
    WideCertificateValid leaf1290Box leaf1290Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk108ValidityFacts chi120ValidityFacts
    leaf1290LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1290CoverageChecked :
    coverageCheck (innerAD leaf1290Box) leaf1290InnerLog = true := by
  rfl'

private theorem leaf1290InnerLogValid :
    leaf1290InnerLog.Valid 8 (innerAD leaf1290Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint133PositiveFacts.valid leaf1290CoverageChecked

private noncomputable def leaf1290InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814649/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1290InputLogOnePlusV_eq :
    leaf1290InputLogOnePlusV = outerEnclosure 24
      (leaf1290Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1290RoundedFacts : LeafRoundedFacts 8
    leaf1290Certificate.logOnePlusV leaf1290InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1290InputLogOnePlusV_eq }

private noncomputable def leaf1290Inputs : Inputs :=
  inputsOfCaches globalInput sk108RoundedInputs
    chi120InputQChi innerPair62Input
    leaf1290InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1290LowerChecked :
    lowerCheck 24 leaf1290Box leaf1290Inputs = true := by
  rfl'

private theorem leaf1290CoversExact : CoversExact 8
    leaf1290Box leaf1290Certificate leaf1290InnerLog leaf1290Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk108RoundedFacts chi120RoundedFacts
    innerPair62RoundedFacts leaf1290RoundedFacts (by rfl)

private theorem leaf1290FlatSound : Sound leaf1290Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1290CertificateValid
    leaf1290InnerLogValid leaf1290CoversExact leaf1290LowerChecked

private noncomputable def leaf1291Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (15/64), chiHi := (31/128) }

private noncomputable def leaf1291Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435695/268435456) }, vSqrt := { lower := (32765/32768), upper := (13743698739/13743330304) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (441406931/268435456) }, upper := { exponent := 0, mantissa := (6855/4096) } }, logOuter := sk107LogOuterCertificate, logK := sk107LogKCertificate, logChi := chi121LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (27487029043/27486660608) } }, logDArg := sk107LogDArgCertificate }

private noncomputable def leaf1291InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf1291LocalValidity :
    LeafFacts leaf1291Box leaf1291Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1291Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (13743698739/13743330304) }) = true
      norm_num [leaf1291Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1291CertificateValid :
    WideCertificateValid leaf1291Box leaf1291Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk107ValidityFacts chi121ValidityFacts
    leaf1291LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1291CoverageChecked :
    coverageCheck (innerAD leaf1291Box) leaf1291InnerLog = true := by
  rfl'

private theorem leaf1291InnerLogValid :
    leaf1291InnerLog.Valid 8 (innerAD leaf1291Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf1291CoverageChecked

private noncomputable def leaf1291InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814653/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1291InputLogOnePlusV_eq :
    leaf1291InputLogOnePlusV = outerEnclosure 24
      (leaf1291Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1291RoundedFacts : LeafRoundedFacts 8
    leaf1291Certificate.logOnePlusV leaf1291InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1291InputLogOnePlusV_eq }

private noncomputable def leaf1291Inputs : Inputs :=
  inputsOfCaches globalInput sk107RoundedInputs
    chi121InputQChi innerPair56Input
    leaf1291InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1291LowerChecked :
    lowerCheck 24 leaf1291Box leaf1291Inputs = true := by
  rfl'

private theorem leaf1291CoversExact : CoversExact 8
    leaf1291Box leaf1291Certificate leaf1291InnerLog leaf1291Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk107RoundedFacts chi121RoundedFacts
    innerPair56RoundedFacts leaf1291RoundedFacts (by rfl)

private theorem leaf1291FlatSound : Sound leaf1291Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1291CertificateValid
    leaf1291InnerLogValid leaf1291CoversExact leaf1291LowerChecked

private noncomputable def leaf1292Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (31/128), chiHi := (1/4) }

private noncomputable def leaf1292Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435697/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905520128) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (447173745/268435456) }, upper := { exponent := 0, mantissa := (217/128) } }, logOuter := sk107LogOuterCertificate, logK := sk107LogKCertificate, logChi := chi122LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811684693/45811040256) } }, logDArg := sk107LogDArgCertificate }

private noncomputable def leaf1292InnerLog : WideLogData :=
  innerPair173Data

set_option maxRecDepth 1000000 in
private theorem leaf1292LocalValidity :
    LeafFacts leaf1292Box leaf1292Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1292Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905520128) }) = true
      norm_num [leaf1292Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1292CertificateValid :
    WideCertificateValid leaf1292Box leaf1292Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk107ValidityFacts chi122ValidityFacts
    leaf1292LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1292CoverageChecked :
    coverageCheck (innerAD leaf1292Box) leaf1292InnerLog = true := by
  rfl'

private theorem leaf1292InnerLogValid :
    leaf1292InnerLog.Valid 8 (innerAD leaf1292Box) :=
  wideLogDataValid_of_cachedCheck endpoint48PositiveFacts
    endpoint20PositiveFacts.valid leaf1292CoverageChecked

private noncomputable def leaf1292InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629317/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1292InputLogOnePlusV_eq :
    leaf1292InputLogOnePlusV = outerEnclosure 24
      (leaf1292Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1292RoundedFacts : LeafRoundedFacts 8
    leaf1292Certificate.logOnePlusV leaf1292InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1292InputLogOnePlusV_eq }

private noncomputable def leaf1292Inputs : Inputs :=
  inputsOfCaches globalInput sk107RoundedInputs
    chi122InputQChi innerPair173Input
    leaf1292InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1292LowerChecked :
    lowerCheck 24 leaf1292Box leaf1292Inputs = true := by
  rfl'

private theorem leaf1292CoversExact : CoversExact 8
    leaf1292Box leaf1292Certificate leaf1292InnerLog leaf1292Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk107RoundedFacts chi122RoundedFacts
    innerPair173RoundedFacts leaf1292RoundedFacts (by rfl)

private theorem leaf1292FlatSound : Sound leaf1292Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1292CertificateValid
    leaf1292InnerLogValid leaf1292CoversExact leaf1292LowerChecked

private noncomputable def leaf1293Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (15/64), chiHi := (31/128) }

private noncomputable def leaf1293Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435697/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716619776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (443372889/268435456) }, upper := { exponent := 0, mantissa := (3443/2048) } }, logOuter := sk108LogOuterCertificate, logK := sk108LogKCertificate, logChi := chi121LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435113471/137433239552) } }, logDArg := sk108LogDArgCertificate }

private noncomputable def leaf1293InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf1293LocalValidity :
    LeafFacts leaf1293Box leaf1293Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1293Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716619776) }) = true
      norm_num [leaf1293Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1293CertificateValid :
    WideCertificateValid leaf1293Box leaf1293Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk108ValidityFacts chi121ValidityFacts
    leaf1293LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1293CoverageChecked :
    coverageCheck (innerAD leaf1293Box) leaf1293InnerLog = true := by
  rfl'

private theorem leaf1293InnerLogValid :
    leaf1293InnerLog.Valid 8 (innerAD leaf1293Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf1293CoverageChecked

private noncomputable def leaf1293InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814655/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1293InputLogOnePlusV_eq :
    leaf1293InputLogOnePlusV = outerEnclosure 24
      (leaf1293Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1293RoundedFacts : LeafRoundedFacts 8
    leaf1293Certificate.logOnePlusV leaf1293InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1293InputLogOnePlusV_eq }

private noncomputable def leaf1293Inputs : Inputs :=
  inputsOfCaches globalInput sk108RoundedInputs
    chi121InputQChi innerPair56Input
    leaf1293InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1293LowerChecked :
    lowerCheck 24 leaf1293Box leaf1293Inputs = true := by
  rfl'

private theorem leaf1293CoversExact : CoversExact 8
    leaf1293Box leaf1293Certificate leaf1293InnerLog leaf1293Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk108RoundedFacts chi121RoundedFacts
    innerPair56RoundedFacts leaf1293RoundedFacts (by rfl)

private theorem leaf1293FlatSound : Sound leaf1293Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1293CertificateValid
    leaf1293InnerLogValid leaf1293CoversExact leaf1293LowerChecked

private noncomputable def leaf1294Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (31/128), chiHi := (1/4) }

private noncomputable def leaf1294Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435699/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716527616) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (449205235/268435456) }, upper := { exponent := 0, mantissa := (109/64) } }, logOuter := sk108LogOuterCertificate, logK := sk108LogKCertificate, logChi := chi122LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435021311/137433055232) } }, logDArg := sk108LogDArgCertificate }

private noncomputable def leaf1294InnerLog : WideLogData :=
  innerPair420Data

set_option maxRecDepth 1000000 in
private theorem leaf1294LocalValidity :
    LeafFacts leaf1294Box leaf1294Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1294Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716527616) }) = true
      norm_num [leaf1294Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1294CertificateValid :
    WideCertificateValid leaf1294Box leaf1294Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk108ValidityFacts chi122ValidityFacts
    leaf1294LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1294CoverageChecked :
    coverageCheck (innerAD leaf1294Box) leaf1294InnerLog = true := by
  rfl'

private theorem leaf1294InnerLogValid :
    leaf1294InnerLog.Valid 8 (innerAD leaf1294Box) :=
  wideLogDataValid_of_cachedCheck endpoint133PositiveFacts
    endpoint20PositiveFacts.valid leaf1294CoverageChecked

private noncomputable def leaf1294InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629321/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1294InputLogOnePlusV_eq :
    leaf1294InputLogOnePlusV = outerEnclosure 24
      (leaf1294Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1294RoundedFacts : LeafRoundedFacts 8
    leaf1294Certificate.logOnePlusV leaf1294InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1294InputLogOnePlusV_eq }

private noncomputable def leaf1294Inputs : Inputs :=
  inputsOfCaches globalInput sk108RoundedInputs
    chi122InputQChi innerPair420Input
    leaf1294InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1294LowerChecked :
    lowerCheck 24 leaf1294Box leaf1294Inputs = true := by
  rfl'

private theorem leaf1294CoversExact : CoversExact 8
    leaf1294Box leaf1294Certificate leaf1294InnerLog leaf1294Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk108RoundedFacts chi122RoundedFacts
    innerPair420RoundedFacts leaf1294RoundedFacts (by rfl)

private theorem leaf1294FlatSound : Sound leaf1294Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1294CertificateValid
    leaf1294InnerLogValid leaf1294CoversExact leaf1294LowerChecked

private noncomputable def leaf1295Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32), chiLo := (7/32), chiHi := (29/128) }

private noncomputable def leaf1295Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435695/268435456) }, vSqrt := { lower := (32765/32768), upper := (808452867/808432640) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (433543091/268435456) }, upper := { exponent := 0, mantissa := (6735/4096) } }, logOuter := sk109LogOuterCertificate, logK := sk109LogKCertificate, logChi := chi119LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (1616885507/1616865280) } }, logDArg := sk109LogDArgCertificate }

private noncomputable def leaf1295InnerLog : WideLogData :=
  innerPair167Data

set_option maxRecDepth 1000000 in
private theorem leaf1295LocalValidity :
    LeafFacts leaf1295Box leaf1295Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1295Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (808452867/808432640) }) = true
      norm_num [leaf1295Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1295CertificateValid :
    WideCertificateValid leaf1295Box leaf1295Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk109ValidityFacts chi119ValidityFacts
    leaf1295LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1295CoverageChecked :
    coverageCheck (innerAD leaf1295Box) leaf1295InnerLog = true := by
  rfl'

private theorem leaf1295InnerLogValid :
    leaf1295InnerLog.Valid 8 (innerAD leaf1295Box) :=
  wideLogDataValid_of_cachedCheck endpoint46PositiveFacts
    endpoint48PositiveFacts.valid leaf1295CoverageChecked

private noncomputable def leaf1295InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629291/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1295InputLogOnePlusV_eq :
    leaf1295InputLogOnePlusV = outerEnclosure 24
      (leaf1295Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1295RoundedFacts : LeafRoundedFacts 8
    leaf1295Certificate.logOnePlusV leaf1295InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1295InputLogOnePlusV_eq }

private noncomputable def leaf1295Inputs : Inputs :=
  inputsOfCaches globalInput sk109RoundedInputs
    chi119InputQChi innerPair167Input
    leaf1295InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1295LowerChecked :
    lowerCheck 24 leaf1295Box leaf1295Inputs = true := by
  rfl'

private theorem leaf1295CoversExact : CoversExact 8
    leaf1295Box leaf1295Certificate leaf1295InnerLog leaf1295Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk109RoundedFacts chi119RoundedFacts
    innerPair167RoundedFacts leaf1295RoundedFacts (by rfl)

private theorem leaf1295FlatSound : Sound leaf1295Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1295CertificateValid
    leaf1295InnerLogValid leaf1295CoversExact leaf1295LowerChecked

private noncomputable def leaf1296Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32), chiLo := (29/128), chiHi := (15/64) }

private noncomputable def leaf1296Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435697/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716681216) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (439440969/268435456) }, upper := { exponent := 0, mantissa := (3413/2048) } }, logOuter := sk109LogOuterCertificate, logK := sk109LogKCertificate, logChi := chi120LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435174911/137433362432) } }, logDArg := sk109LogDArgCertificate }

private noncomputable def leaf1296InnerLog : WideLogData :=
  innerPair62Data

set_option maxRecDepth 1000000 in
private theorem leaf1296LocalValidity :
    LeafFacts leaf1296Box leaf1296Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1296Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716681216) }) = true
      norm_num [leaf1296Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1296CertificateValid :
    WideCertificateValid leaf1296Box leaf1296Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk109ValidityFacts chi120ValidityFacts
    leaf1296LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1296CoverageChecked :
    coverageCheck (innerAD leaf1296Box) leaf1296InnerLog = true := by
  rfl'

private theorem leaf1296InnerLogValid :
    leaf1296InnerLog.Valid 8 (innerAD leaf1296Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint133PositiveFacts.valid leaf1296CoverageChecked

private noncomputable def leaf1296InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814651/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1296InputLogOnePlusV_eq :
    leaf1296InputLogOnePlusV = outerEnclosure 24
      (leaf1296Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1296RoundedFacts : LeafRoundedFacts 8
    leaf1296Certificate.logOnePlusV leaf1296InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1296InputLogOnePlusV_eq }

private noncomputable def leaf1296Inputs : Inputs :=
  inputsOfCaches globalInput sk109RoundedInputs
    chi120InputQChi innerPair62Input
    leaf1296InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1296LowerChecked :
    lowerCheck 24 leaf1296Box leaf1296Inputs = true := by
  rfl'

private theorem leaf1296CoversExact : CoversExact 8
    leaf1296Box leaf1296Certificate leaf1296InnerLog leaf1296Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk109RoundedFacts chi120RoundedFacts
    innerPair62RoundedFacts leaf1296RoundedFacts (by rfl)

private theorem leaf1296FlatSound : Sound leaf1296Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1296CertificateValid
    leaf1296InnerLogValid leaf1296CoversExact leaf1296LowerChecked

private noncomputable def leaf1297Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8), chiLo := (7/32), chiHi := (29/128) }

private noncomputable def leaf1297Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435697/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905581568) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (435377985/268435456) }, upper := { exponent := 0, mantissa := (1691/1024) } }, logOuter := sk110LogOuterCertificate, logK := sk110LogKCertificate, logChi := chi119LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811746133/45811163136) } }, logDArg := sk110LogDArgCertificate }

private noncomputable def leaf1297InnerLog : WideLogData :=
  innerPair167Data

set_option maxRecDepth 1000000 in
private theorem leaf1297LocalValidity :
    LeafFacts leaf1297Box leaf1297Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1297Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905581568) }) = true
      norm_num [leaf1297Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1297CertificateValid :
    WideCertificateValid leaf1297Box leaf1297Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk110ValidityFacts chi119ValidityFacts
    leaf1297LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1297CoverageChecked :
    coverageCheck (innerAD leaf1297Box) leaf1297InnerLog = true := by
  rfl'

private theorem leaf1297InnerLogValid :
    leaf1297InnerLog.Valid 8 (innerAD leaf1297Box) :=
  wideLogDataValid_of_cachedCheck endpoint46PositiveFacts
    endpoint48PositiveFacts.valid leaf1297CoverageChecked

private noncomputable def leaf1297InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814647/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1297InputLogOnePlusV_eq :
    leaf1297InputLogOnePlusV = outerEnclosure 24
      (leaf1297Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1297RoundedFacts : LeafRoundedFacts 8
    leaf1297Certificate.logOnePlusV leaf1297InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1297InputLogOnePlusV_eq }

private noncomputable def leaf1297Inputs : Inputs :=
  inputsOfCaches globalInput sk110RoundedInputs
    chi119InputQChi innerPair167Input
    leaf1297InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1297LowerChecked :
    lowerCheck 24 leaf1297Box leaf1297Inputs = true := by
  rfl'

private theorem leaf1297CoversExact : CoversExact 8
    leaf1297Box leaf1297Certificate leaf1297InnerLog leaf1297Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk110RoundedFacts chi119RoundedFacts
    innerPair167RoundedFacts leaf1297RoundedFacts (by rfl)

private theorem leaf1297FlatSound : Sound leaf1297Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1297CertificateValid
    leaf1297InnerLogValid leaf1297CoversExact leaf1297LowerChecked

private noncomputable def leaf1298Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8), chiLo := (29/128), chiHi := (15/64) }

private noncomputable def leaf1298Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435699/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716650496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (441341395/268435456) }, upper := { exponent := 0, mantissa := (857/512) } }, logOuter := sk110LogOuterCertificate, logK := sk110LogKCertificate, logChi := chi120LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435144191/137433300992) } }, logDArg := sk110LogDArgCertificate }

private noncomputable def leaf1298InnerLog : WideLogData :=
  innerPair161Data

set_option maxRecDepth 1000000 in
private theorem leaf1298LocalValidity :
    LeafFacts leaf1298Box leaf1298Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1298Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716650496) }) = true
      norm_num [leaf1298Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1298CertificateValid :
    WideCertificateValid leaf1298Box leaf1298Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk110ValidityFacts chi120ValidityFacts
    leaf1298LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1298CoverageChecked :
    coverageCheck (innerAD leaf1298Box) leaf1298InnerLog = true := by
  rfl'

private theorem leaf1298InnerLogValid :
    leaf1298InnerLog.Valid 8 (innerAD leaf1298Box) :=
  wideLogDataValid_of_cachedCheck endpoint45PositiveFacts
    endpoint56PositiveFacts.valid leaf1298CoverageChecked

private noncomputable def leaf1298InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814653/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1298InputLogOnePlusV_eq :
    leaf1298InputLogOnePlusV = outerEnclosure 24
      (leaf1298Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1298RoundedFacts : LeafRoundedFacts 8
    leaf1298Certificate.logOnePlusV leaf1298InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1298InputLogOnePlusV_eq }

private noncomputable def leaf1298Inputs : Inputs :=
  inputsOfCaches globalInput sk110RoundedInputs
    chi120InputQChi innerPair161Input
    leaf1298InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1298LowerChecked :
    lowerCheck 24 leaf1298Box leaf1298Inputs = true := by
  rfl'

private theorem leaf1298CoversExact : CoversExact 8
    leaf1298Box leaf1298Certificate leaf1298InnerLog leaf1298Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk110RoundedFacts chi120RoundedFacts
    innerPair161RoundedFacts leaf1298RoundedFacts (by rfl)

private theorem leaf1298FlatSound : Sound leaf1298Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1298CertificateValid
    leaf1298InnerLogValid leaf1298CoversExact leaf1298LowerChecked

private noncomputable def leaf1299Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32), chiLo := (15/64), chiHi := (31/128) }

private noncomputable def leaf1299Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435699/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905529344) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (445338847/268435456) }, upper := { exponent := 0, mantissa := (6917/4096) } }, logOuter := sk109LogOuterCertificate, logK := sk109LogKCertificate, logChi := chi121LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811693909/45811058688) } }, logDArg := sk109LogDArgCertificate }

private noncomputable def leaf1299InnerLog : WideLogData :=
  innerPair173Data

set_option maxRecDepth 1000000 in
private theorem leaf1299LocalValidity :
    LeafFacts leaf1299Box leaf1299Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1299Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905529344) }) = true
      norm_num [leaf1299Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1299CertificateValid :
    WideCertificateValid leaf1299Box leaf1299Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk109ValidityFacts chi121ValidityFacts
    leaf1299LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1299CoverageChecked :
    coverageCheck (innerAD leaf1299Box) leaf1299InnerLog = true := by
  rfl'

private theorem leaf1299InnerLogValid :
    leaf1299InnerLog.Valid 8 (innerAD leaf1299Box) :=
  wideLogDataValid_of_cachedCheck endpoint48PositiveFacts
    endpoint20PositiveFacts.valid leaf1299CoverageChecked

private noncomputable def leaf1299InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629313/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1299InputLogOnePlusV_eq :
    leaf1299InputLogOnePlusV = outerEnclosure 24
      (leaf1299Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1299RoundedFacts : LeafRoundedFacts 8
    leaf1299Certificate.logOnePlusV leaf1299InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1299InputLogOnePlusV_eq }

private noncomputable def leaf1299Inputs : Inputs :=
  inputsOfCaches globalInput sk109RoundedInputs
    chi121InputQChi innerPair173Input
    leaf1299InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1299LowerChecked :
    lowerCheck 24 leaf1299Box leaf1299Inputs = true := by
  rfl'

private theorem leaf1299CoversExact : CoversExact 8
    leaf1299Box leaf1299Certificate leaf1299InnerLog leaf1299Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk109RoundedFacts chi121RoundedFacts
    innerPair173RoundedFacts leaf1299RoundedFacts (by rfl)

private theorem leaf1299FlatSound : Sound leaf1299Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1299CertificateValid
    leaf1299InnerLogValid leaf1299CoversExact leaf1299LowerChecked

private noncomputable def leaf1300Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32), chiLo := (31/128), chiHi := (1/4) }

private noncomputable def leaf1300Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435701/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716494848) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (451236725/268435456) }, upper := { exponent := 0, mantissa := (219/128) } }, logOuter := sk109LogOuterCertificate, logK := sk109LogKCertificate, logChi := chi122LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434988543/137432989696) } }, logDArg := sk109LogDArgCertificate }

private noncomputable def leaf1300InnerLog : WideLogData :=
  innerPair421Data

set_option maxRecDepth 1000000 in
private theorem leaf1300LocalValidity :
    LeafFacts leaf1300Box leaf1300Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1300Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716494848) }) = true
      norm_num [leaf1300Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1300CertificateValid :
    WideCertificateValid leaf1300Box leaf1300Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk109ValidityFacts chi122ValidityFacts
    leaf1300LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1300CoverageChecked :
    coverageCheck (innerAD leaf1300Box) leaf1300InnerLog = true := by
  rfl'

private theorem leaf1300InnerLogValid :
    leaf1300InnerLog.Valid 8 (innerAD leaf1300Box) :=
  wideLogDataValid_of_cachedCheck endpoint133PositiveFacts
    endpoint62PositiveFacts.valid leaf1300CoverageChecked

private noncomputable def leaf1300InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629325/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1300InputLogOnePlusV_eq :
    leaf1300InputLogOnePlusV = outerEnclosure 24
      (leaf1300Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1300RoundedFacts : LeafRoundedFacts 8
    leaf1300Certificate.logOnePlusV leaf1300InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1300InputLogOnePlusV_eq }

private noncomputable def leaf1300Inputs : Inputs :=
  inputsOfCaches globalInput sk109RoundedInputs
    chi122InputQChi innerPair421Input
    leaf1300InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1300LowerChecked :
    lowerCheck 24 leaf1300Box leaf1300Inputs = true := by
  rfl'

private theorem leaf1300CoversExact : CoversExact 8
    leaf1300Box leaf1300Certificate leaf1300InnerLog leaf1300Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk109RoundedFacts chi122RoundedFacts
    innerPair421RoundedFacts leaf1300RoundedFacts (by rfl)

private theorem leaf1300FlatSound : Sound leaf1300Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1300CertificateValid
    leaf1300InnerLogValid leaf1300CoversExact leaf1300LowerChecked

private noncomputable def leaf1301Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8), chiLo := (15/64), chiHi := (31/128) }

private noncomputable def leaf1301Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435701/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716556288) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (447304805/268435456) }, upper := { exponent := 0, mantissa := (1737/1024) } }, logOuter := sk110LogOuterCertificate, logK := sk110LogKCertificate, logChi := chi121LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435049983/137433112576) } }, logDArg := sk110LogDArgCertificate }

private noncomputable def leaf1301InnerLog : WideLogData :=
  innerPair173Data

set_option maxRecDepth 1000000 in
private theorem leaf1301LocalValidity :
    LeafFacts leaf1301Box leaf1301Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1301Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716556288) }) = true
      norm_num [leaf1301Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1301CertificateValid :
    WideCertificateValid leaf1301Box leaf1301Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk110ValidityFacts chi121ValidityFacts
    leaf1301LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1301CoverageChecked :
    coverageCheck (innerAD leaf1301Box) leaf1301InnerLog = true := by
  rfl'

private theorem leaf1301InnerLogValid :
    leaf1301InnerLog.Valid 8 (innerAD leaf1301Box) :=
  wideLogDataValid_of_cachedCheck endpoint48PositiveFacts
    endpoint20PositiveFacts.valid leaf1301CoverageChecked

private noncomputable def leaf1301InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629317/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1301InputLogOnePlusV_eq :
    leaf1301InputLogOnePlusV = outerEnclosure 24
      (leaf1301Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1301RoundedFacts : LeafRoundedFacts 8
    leaf1301Certificate.logOnePlusV leaf1301InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1301InputLogOnePlusV_eq }

private noncomputable def leaf1301Inputs : Inputs :=
  inputsOfCaches globalInput sk110RoundedInputs
    chi121InputQChi innerPair173Input
    leaf1301InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1301LowerChecked :
    lowerCheck 24 leaf1301Box leaf1301Inputs = true := by
  rfl'

private theorem leaf1301CoversExact : CoversExact 8
    leaf1301Box leaf1301Certificate leaf1301InnerLog leaf1301Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk110RoundedFacts chi121RoundedFacts
    innerPair173RoundedFacts leaf1301RoundedFacts (by rfl)

private theorem leaf1301FlatSound : Sound leaf1301Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1301CertificateValid
    leaf1301InnerLogValid leaf1301CoversExact leaf1301LowerChecked

private noncomputable def leaf1302Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8), chiLo := (31/128), chiHi := (1/4) }

private noncomputable def leaf1302Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435703/268435456) }, vSqrt := { lower := (32765/32768), upper := (4581232913/4581097472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (453268215/268435456) }, upper := { exponent := 0, mantissa := (55/32) } }, logOuter := sk110LogOuterCertificate, logK := sk110LogKCertificate, logChi := chi122LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (9162330385/9162194944) } }, logDArg := sk110LogDArgCertificate }

private noncomputable def leaf1302InnerLog : WideLogData :=
  innerPair68Data

set_option maxRecDepth 1000000 in
private theorem leaf1302LocalValidity :
    LeafFacts leaf1302Box leaf1302Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1302Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4581232913/4581097472) }) = true
      norm_num [leaf1302Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1302CertificateValid :
    WideCertificateValid leaf1302Box leaf1302Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk110ValidityFacts chi122ValidityFacts
    leaf1302LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1302CoverageChecked :
    coverageCheck (innerAD leaf1302Box) leaf1302InnerLog = true := by
  rfl'

private theorem leaf1302InnerLogValid :
    leaf1302InnerLog.Valid 8 (innerAD leaf1302Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint62PositiveFacts.valid leaf1302CoverageChecked

private noncomputable def leaf1302InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629329/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1302InputLogOnePlusV_eq :
    leaf1302InputLogOnePlusV = outerEnclosure 24
      (leaf1302Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1302RoundedFacts : LeafRoundedFacts 8
    leaf1302Certificate.logOnePlusV leaf1302InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1302InputLogOnePlusV_eq }

private noncomputable def leaf1302Inputs : Inputs :=
  inputsOfCaches globalInput sk110RoundedInputs
    chi122InputQChi innerPair68Input
    leaf1302InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1302LowerChecked :
    lowerCheck 24 leaf1302Box leaf1302Inputs = true := by
  rfl'

private theorem leaf1302CoversExact : CoversExact 8
    leaf1302Box leaf1302Certificate leaf1302InnerLog leaf1302Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk110RoundedFacts chi122RoundedFacts
    innerPair68RoundedFacts leaf1302RoundedFacts (by rfl)

private theorem leaf1302FlatSound : Sound leaf1302Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1302CertificateValid
    leaf1302InnerLogValid leaf1302CoversExact leaf1302LowerChecked

private noncomputable def leaf1303Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32), chiLo := (7/32), chiHi := (29/128) }

private noncomputable def leaf1303Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435699/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716715008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (437212879/268435456) }, upper := { exponent := 0, mantissa := (6793/4096) } }, logOuter := sk111LogOuterCertificate, logK := sk111LogKCertificate, logChi := chi119LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435208703/137433430016) } }, logDArg := sk111LogDArgCertificate }

private noncomputable def leaf1303InnerLog : WideLogData :=
  innerPair63Data

set_option maxRecDepth 1000000 in
private theorem leaf1303LocalValidity :
    LeafFacts leaf1303Box leaf1303Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1303Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716715008) }) = true
      norm_num [leaf1303Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1303CertificateValid :
    WideCertificateValid leaf1303Box leaf1303Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk111ValidityFacts chi119ValidityFacts
    leaf1303LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1303CoverageChecked :
    coverageCheck (innerAD leaf1303Box) leaf1303InnerLog = true := by
  rfl'

private theorem leaf1303InnerLogValid :
    leaf1303InnerLog.Valid 8 (innerAD leaf1303Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint134PositiveFacts.valid leaf1303CoverageChecked

private noncomputable def leaf1303InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814649/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1303InputLogOnePlusV_eq :
    leaf1303InputLogOnePlusV = outerEnclosure 24
      (leaf1303Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1303RoundedFacts : LeafRoundedFacts 8
    leaf1303Certificate.logOnePlusV leaf1303InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1303InputLogOnePlusV_eq }

private noncomputable def leaf1303Inputs : Inputs :=
  inputsOfCaches globalInput sk111RoundedInputs
    chi119InputQChi innerPair63Input
    leaf1303InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1303LowerChecked :
    lowerCheck 24 leaf1303Box leaf1303Inputs = true := by
  rfl'

private theorem leaf1303CoversExact : CoversExact 8
    leaf1303Box leaf1303Certificate leaf1303InnerLog leaf1303Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk111RoundedFacts chi119RoundedFacts
    innerPair63RoundedFacts leaf1303RoundedFacts (by rfl)

private theorem leaf1303FlatSound : Sound leaf1303Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1303CertificateValid
    leaf1303InnerLogValid leaf1303CoversExact leaf1303LowerChecked

private noncomputable def leaf1304Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32), chiLo := (29/128), chiHi := (15/64) }

private noncomputable def leaf1304Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435701/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716619776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (443241821/268435456) }, upper := { exponent := 0, mantissa := (3443/2048) } }, logOuter := sk111LogOuterCertificate, logK := sk111LogKCertificate, logChi := chi120LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435113471/137433239552) } }, logDArg := sk111LogDArgCertificate }

private noncomputable def leaf1304InnerLog : WideLogData :=
  innerPair425Data

set_option maxRecDepth 1000000 in
private theorem leaf1304LocalValidity :
    LeafFacts leaf1304Box leaf1304Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1304Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716619776) }) = true
      norm_num [leaf1304Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1304CertificateValid :
    WideCertificateValid leaf1304Box leaf1304Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk111ValidityFacts chi120ValidityFacts
    leaf1304LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1304CoverageChecked :
    coverageCheck (innerAD leaf1304Box) leaf1304InnerLog = true := by
  rfl'

private theorem leaf1304InnerLogValid :
    leaf1304InnerLog.Valid 8 (innerAD leaf1304Box) :=
  wideLogDataValid_of_cachedCheck endpoint135PositiveFacts
    endpoint58PositiveFacts.valid leaf1304CoverageChecked

private noncomputable def leaf1304InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814655/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1304InputLogOnePlusV_eq :
    leaf1304InputLogOnePlusV = outerEnclosure 24
      (leaf1304Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1304RoundedFacts : LeafRoundedFacts 8
    leaf1304Certificate.logOnePlusV leaf1304InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1304InputLogOnePlusV_eq }

private noncomputable def leaf1304Inputs : Inputs :=
  inputsOfCaches globalInput sk111RoundedInputs
    chi120InputQChi innerPair425Input
    leaf1304InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1304LowerChecked :
    lowerCheck 24 leaf1304Box leaf1304Inputs = true := by
  rfl'

private theorem leaf1304CoversExact : CoversExact 8
    leaf1304Box leaf1304Certificate leaf1304InnerLog leaf1304Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk111RoundedFacts chi120RoundedFacts
    innerPair425RoundedFacts leaf1304RoundedFacts (by rfl)

private theorem leaf1304FlatSound : Sound leaf1304Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1304CertificateValid
    leaf1304InnerLogValid leaf1304CoversExact leaf1304LowerChecked

private noncomputable def leaf1305Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (187/64), chiLo := (7/32), chiHi := (29/128) }

private noncomputable def leaf1305Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871343/536870912) }, vSqrt := { lower := (32765/32768), upper := (9162461457/9162226688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (878128371/536870912) }, upper := { exponent := 0, mantissa := (13615/8192) } }, logOuter := sk119LogOuterCertificate, logK := sk119LogKCertificate, logChi := chi119LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (18324688145/18324453376) } }, logDArg := sk119LogDArgCertificate }

private noncomputable def leaf1305InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf1305LocalValidity :
    LeafFacts leaf1305Box leaf1305Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1305Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (9162461457/9162226688) }) = true
      norm_num [leaf1305Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1305CertificateValid :
    WideCertificateValid leaf1305Box leaf1305Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk119ValidityFacts chi119ValidityFacts
    leaf1305LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1305CoverageChecked :
    coverageCheck (innerAD leaf1305Box) leaf1305InnerLog = true := by
  rfl'

private theorem leaf1305InnerLogValid :
    leaf1305InnerLog.Valid 8 (innerAD leaf1305Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf1305CoverageChecked

private noncomputable def leaf1305InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (726831/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf1305InputLogOnePlusV_eq :
    leaf1305InputLogOnePlusV = outerEnclosure 24
      (leaf1305Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1305RoundedFacts : LeafRoundedFacts 8
    leaf1305Certificate.logOnePlusV leaf1305InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1305InputLogOnePlusV_eq }

private noncomputable def leaf1305Inputs : Inputs :=
  inputsOfCaches globalInput sk119RoundedInputs
    chi119InputQChi innerPair56Input
    leaf1305InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1305LowerChecked :
    lowerCheck 24 leaf1305Box leaf1305Inputs = true := by
  rfl'

private theorem leaf1305CoversExact : CoversExact 8
    leaf1305Box leaf1305Certificate leaf1305InnerLog leaf1305Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk119RoundedFacts chi119RoundedFacts
    innerPair56RoundedFacts leaf1305RoundedFacts (by rfl)

private theorem leaf1305FlatSound : Sound leaf1305Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1305CertificateValid
    leaf1305InnerLogValid leaf1305CoversExact leaf1305LowerChecked

private noncomputable def leaf1306Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (187/64), kHi := (47/16), chiLo := (7/32), chiHi := (29/128) }

private noncomputable def leaf1306Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871345/536870912) }, vSqrt := { lower := (32765/32768), upper := (137436921855/137433370624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (879963265/536870912) }, upper := { exponent := 0, mantissa := (3411/2048) } }, logOuter := sk120LogOuterCertificate, logK := sk120LogKCertificate, logChi := chi119LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (274870292479/274866741248) } }, logDArg := sk120LogDArgCertificate }

private noncomputable def leaf1306InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf1306LocalValidity :
    LeafFacts leaf1306Box leaf1306Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1306Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (137436921855/137433370624) }) = true
      norm_num [leaf1306Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1306CertificateValid :
    WideCertificateValid leaf1306Box leaf1306Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk120ValidityFacts chi119ValidityFacts
    leaf1306LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1306CoverageChecked :
    coverageCheck (innerAD leaf1306Box) leaf1306InnerLog = true := by
  rfl'

private theorem leaf1306InnerLogValid :
    leaf1306InnerLog.Valid 8 (innerAD leaf1306Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf1306CoverageChecked

private noncomputable def leaf1306InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814649/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1306InputLogOnePlusV_eq :
    leaf1306InputLogOnePlusV = outerEnclosure 24
      (leaf1306Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1306RoundedFacts : LeafRoundedFacts 8
    leaf1306Certificate.logOnePlusV leaf1306InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1306InputLogOnePlusV_eq }

private noncomputable def leaf1306Inputs : Inputs :=
  inputsOfCaches globalInput sk120RoundedInputs
    chi119InputQChi innerPair56Input
    leaf1306InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1306LowerChecked :
    lowerCheck 24 leaf1306Box leaf1306Inputs = true := by
  rfl'

private theorem leaf1306CoversExact : CoversExact 8
    leaf1306Box leaf1306Certificate leaf1306InnerLog leaf1306Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk120RoundedFacts chi119RoundedFacts
    innerPair56RoundedFacts leaf1306RoundedFacts (by rfl)

private theorem leaf1306FlatSound : Sound leaf1306Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1306CertificateValid
    leaf1306InnerLogValid leaf1306CoversExact leaf1306LowerChecked

private noncomputable def leaf1307Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (187/64), chiLo := (29/128), chiHi := (15/64) }

private noncomputable def leaf1307Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871345/536870912) }, vSqrt := { lower := (32765/32768), upper := (137436921855/137433208832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (890317321/536870912) }, upper := { exponent := 0, mantissa := (6901/4096) } }, logOuter := sk119LogOuterCertificate, logK := sk119LogKCertificate, logChi := chi120LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (274870130687/274866417664) } }, logDArg := sk119LogDArgCertificate }

private noncomputable def leaf1307InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf1307LocalValidity :
    LeafFacts leaf1307Box leaf1307Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1307Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (137436921855/137433208832) }) = true
      norm_num [leaf1307Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1307CertificateValid :
    WideCertificateValid leaf1307Box leaf1307Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk119ValidityFacts chi120ValidityFacts
    leaf1307LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1307CoverageChecked :
    coverageCheck (innerAD leaf1307Box) leaf1307InnerLog = true := by
  rfl'

private theorem leaf1307InnerLogValid :
    leaf1307InnerLog.Valid 8 (innerAD leaf1307Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf1307CoverageChecked

private noncomputable def leaf1307InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629307/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1307InputLogOnePlusV_eq :
    leaf1307InputLogOnePlusV = outerEnclosure 24
      (leaf1307Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1307RoundedFacts : LeafRoundedFacts 8
    leaf1307Certificate.logOnePlusV leaf1307InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1307InputLogOnePlusV_eq }

private noncomputable def leaf1307Inputs : Inputs :=
  inputsOfCaches globalInput sk119RoundedInputs
    chi120InputQChi innerPair56Input
    leaf1307InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1307LowerChecked :
    lowerCheck 24 leaf1307Box leaf1307Inputs = true := by
  rfl'

private theorem leaf1307CoversExact : CoversExact 8
    leaf1307Box leaf1307Certificate leaf1307InnerLog leaf1307Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk119RoundedFacts chi120RoundedFacts
    innerPair56RoundedFacts leaf1307RoundedFacts (by rfl)

private theorem leaf1307FlatSound : Sound leaf1307Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1307CertificateValid
    leaf1307InnerLogValid leaf1307CoversExact leaf1307LowerChecked

private noncomputable def leaf1308Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (187/64), kHi := (47/16), chiLo := (29/128), chiHi := (15/64) }

private noncomputable def leaf1308Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871347/536870912) }, vSqrt := { lower := (32765/32768), upper := (137436921855/137433178112) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (892217747/536870912) }, upper := { exponent := 0, mantissa := (1729/1024) } }, logOuter := sk120LogOuterCertificate, logK := sk120LogKCertificate, logChi := chi120LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (274870099967/274866356224) } }, logDArg := sk120LogDArgCertificate }

private noncomputable def leaf1308InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf1308LocalValidity :
    LeafFacts leaf1308Box leaf1308Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1308Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (137436921855/137433178112) }) = true
      norm_num [leaf1308Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1308CertificateValid :
    WideCertificateValid leaf1308Box leaf1308Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk120ValidityFacts chi120ValidityFacts
    leaf1308LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1308CoverageChecked :
    coverageCheck (innerAD leaf1308Box) leaf1308InnerLog = true := by
  rfl'

private theorem leaf1308InnerLogValid :
    leaf1308InnerLog.Valid 8 (innerAD leaf1308Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf1308CoverageChecked

private noncomputable def leaf1308InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629309/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1308InputLogOnePlusV_eq :
    leaf1308InputLogOnePlusV = outerEnclosure 24
      (leaf1308Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1308RoundedFacts : LeafRoundedFacts 8
    leaf1308Certificate.logOnePlusV leaf1308InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1308InputLogOnePlusV_eq }

private noncomputable def leaf1308Inputs : Inputs :=
  inputsOfCaches globalInput sk120RoundedInputs
    chi120InputQChi innerPair57Input
    leaf1308InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1308LowerChecked :
    lowerCheck 24 leaf1308Box leaf1308Inputs = true := by
  rfl'

private theorem leaf1308CoversExact : CoversExact 8
    leaf1308Box leaf1308Certificate leaf1308InnerLog leaf1308Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk120RoundedFacts chi120RoundedFacts
    innerPair57RoundedFacts leaf1308RoundedFacts (by rfl)

private theorem leaf1308FlatSound : Sound leaf1308Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1308CertificateValid
    leaf1308InnerLogValid leaf1308CoversExact leaf1308LowerChecked

private noncomputable def leaf1309Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32), chiLo := (15/64), chiHi := (31/128) }

private noncomputable def leaf1309Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435703/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716524544) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (449270763/268435456) }, upper := { exponent := 0, mantissa := (6979/4096) } }, logOuter := sk111LogOuterCertificate, logK := sk111LogKCertificate, logChi := chi121LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435018239/137433049088) } }, logDArg := sk111LogDArgCertificate }

private noncomputable def leaf1309InnerLog : WideLogData :=
  innerPair422Data

set_option maxRecDepth 1000000 in
private theorem leaf1309LocalValidity :
    LeafFacts leaf1309Box leaf1309Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1309Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716524544) }) = true
      norm_num [leaf1309Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1309CertificateValid :
    WideCertificateValid leaf1309Box leaf1309Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk111ValidityFacts chi121ValidityFacts
    leaf1309LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1309CoverageChecked :
    coverageCheck (innerAD leaf1309Box) leaf1309InnerLog = true := by
  rfl'

private theorem leaf1309InnerLogValid :
    leaf1309InnerLog.Valid 8 (innerAD leaf1309Box) :=
  wideLogDataValid_of_cachedCheck endpoint133PositiveFacts
    endpoint136PositiveFacts.valid leaf1309CoverageChecked

private noncomputable def leaf1309InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629321/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1309InputLogOnePlusV_eq :
    leaf1309InputLogOnePlusV = outerEnclosure 24
      (leaf1309Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1309RoundedFacts : LeafRoundedFacts 8
    leaf1309Certificate.logOnePlusV leaf1309InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1309InputLogOnePlusV_eq }

private noncomputable def leaf1309Inputs : Inputs :=
  inputsOfCaches globalInput sk111RoundedInputs
    chi121InputQChi innerPair422Input
    leaf1309InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1309LowerChecked :
    lowerCheck 24 leaf1309Box leaf1309Inputs = true := by
  rfl'

private theorem leaf1309CoversExact : CoversExact 8
    leaf1309Box leaf1309Certificate leaf1309InnerLog leaf1309Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk111RoundedFacts chi121RoundedFacts
    innerPair422RoundedFacts leaf1309RoundedFacts (by rfl)

private theorem leaf1309FlatSound : Sound leaf1309Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1309CertificateValid
    leaf1309InnerLogValid leaf1309CoversExact leaf1309LowerChecked

private noncomputable def leaf1310Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32), chiLo := (31/128), chiHi := (1/4) }

private noncomputable def leaf1310Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435705/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716429312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (455299705/268435456) }, upper := { exponent := 0, mantissa := (221/128) } }, logOuter := sk111LogOuterCertificate, logK := sk111LogKCertificate, logChi := chi122LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434923007/137432858624) } }, logDArg := sk111LogDArgCertificate }

private noncomputable def leaf1310InnerLog : WideLogData :=
  innerPair428Data

set_option maxRecDepth 1000000 in
private theorem leaf1310LocalValidity :
    LeafFacts leaf1310Box leaf1310Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1310Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716429312) }) = true
      norm_num [leaf1310Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1310CertificateValid :
    WideCertificateValid leaf1310Box leaf1310Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk111ValidityFacts chi122ValidityFacts
    leaf1310LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1310CoverageChecked :
    coverageCheck (innerAD leaf1310Box) leaf1310InnerLog = true := by
  rfl'

private theorem leaf1310InnerLogValid :
    leaf1310InnerLog.Valid 8 (innerAD leaf1310Box) :=
  wideLogDataValid_of_cachedCheck endpoint137PositiveFacts
    endpoint138PositiveFacts.valid leaf1310CoverageChecked

private noncomputable def leaf1310InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629333/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1310InputLogOnePlusV_eq :
    leaf1310InputLogOnePlusV = outerEnclosure 24
      (leaf1310Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1310RoundedFacts : LeafRoundedFacts 8
    leaf1310Certificate.logOnePlusV leaf1310InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1310InputLogOnePlusV_eq }

private noncomputable def leaf1310Inputs : Inputs :=
  inputsOfCaches globalInput sk111RoundedInputs
    chi122InputQChi innerPair428Input
    leaf1310InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1310LowerChecked :
    lowerCheck 24 leaf1310Box leaf1310Inputs = true := by
  rfl'

private theorem leaf1310CoversExact : CoversExact 8
    leaf1310Box leaf1310Certificate leaf1310InnerLog leaf1310Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk111RoundedFacts chi122RoundedFacts
    innerPair428RoundedFacts leaf1310RoundedFacts (by rfl)

private theorem leaf1310FlatSound : Sound leaf1310Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1310CertificateValid
    leaf1310InnerLogValid leaf1310CoversExact leaf1310LowerChecked

private noncomputable def leaf1311Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (187/64), chiLo := (15/64), chiHi := (31/128) }

private noncomputable def leaf1311Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871347/536870912) }, vSqrt := { lower := (32765/32768), upper := (137436921855/137433017344) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (902506271/536870912) }, upper := { exponent := 0, mantissa := (13989/8192) } }, logOuter := sk119LogOuterCertificate, logK := sk119LogKCertificate, logChi := chi121LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (274869939199/274866034688) } }, logDArg := sk119LogDArgCertificate }

private noncomputable def leaf1311InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf1311LocalValidity :
    LeafFacts leaf1311Box leaf1311Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1311Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (137436921855/137433017344) }) = true
      norm_num [leaf1311Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1311CertificateValid :
    WideCertificateValid leaf1311Box leaf1311Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk119ValidityFacts chi121ValidityFacts
    leaf1311LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1311CoverageChecked :
    coverageCheck (innerAD leaf1311Box) leaf1311InnerLog = true := by
  rfl'

private theorem leaf1311InnerLogValid :
    leaf1311InnerLog.Valid 8 (innerAD leaf1311Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf1311CoverageChecked

private noncomputable def leaf1311InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629319/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1311InputLogOnePlusV_eq :
    leaf1311InputLogOnePlusV = outerEnclosure 24
      (leaf1311Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1311RoundedFacts : LeafRoundedFacts 8
    leaf1311Certificate.logOnePlusV leaf1311InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1311InputLogOnePlusV_eq }

private noncomputable def leaf1311Inputs : Inputs :=
  inputsOfCaches globalInput sk119RoundedInputs
    chi121InputQChi innerPair57Input
    leaf1311InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1311LowerChecked :
    lowerCheck 24 leaf1311Box leaf1311Inputs = true := by
  rfl'

private theorem leaf1311CoversExact : CoversExact 8
    leaf1311Box leaf1311Certificate leaf1311InnerLog leaf1311Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk119RoundedFacts chi121RoundedFacts
    innerPair57RoundedFacts leaf1311RoundedFacts (by rfl)

private theorem leaf1311FlatSound : Sound leaf1311Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1311CertificateValid
    leaf1311InnerLogValid leaf1311CoversExact leaf1311LowerChecked

private noncomputable def leaf1312Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (187/64), kHi := (47/16), chiLo := (15/64), chiHi := (31/128) }

private noncomputable def leaf1312Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871349/536870912) }, vSqrt := { lower := (32765/32768), upper := (9162461457/9162199040) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (904472229/536870912) }, upper := { exponent := 0, mantissa := (3505/2048) } }, logOuter := sk120LogOuterCertificate, logK := sk120LogKCertificate, logChi := chi121LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (18324660497/18324398080) } }, logDArg := sk120LogDArgCertificate }

private noncomputable def leaf1312InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf1312LocalValidity :
    LeafFacts leaf1312Box leaf1312Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1312Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (9162461457/9162199040) }) = true
      norm_num [leaf1312Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1312CertificateValid :
    WideCertificateValid leaf1312Box leaf1312Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk120ValidityFacts chi121ValidityFacts
    leaf1312LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1312CoverageChecked :
    coverageCheck (innerAD leaf1312Box) leaf1312InnerLog = true := by
  rfl'

private theorem leaf1312InnerLogValid :
    leaf1312InnerLog.Valid 8 (innerAD leaf1312Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf1312CoverageChecked

private noncomputable def leaf1312InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629321/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1312InputLogOnePlusV_eq :
    leaf1312InputLogOnePlusV = outerEnclosure 24
      (leaf1312Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1312RoundedFacts : LeafRoundedFacts 8
    leaf1312Certificate.logOnePlusV leaf1312InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1312InputLogOnePlusV_eq }

private noncomputable def leaf1312Inputs : Inputs :=
  inputsOfCaches globalInput sk120RoundedInputs
    chi121InputQChi innerPair57Input
    leaf1312InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1312LowerChecked :
    lowerCheck 24 leaf1312Box leaf1312Inputs = true := by
  rfl'

private theorem leaf1312CoversExact : CoversExact 8
    leaf1312Box leaf1312Certificate leaf1312InnerLog leaf1312Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk120RoundedFacts chi121RoundedFacts
    innerPair57RoundedFacts leaf1312RoundedFacts (by rfl)

private theorem leaf1312FlatSound : Sound leaf1312Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1312CertificateValid
    leaf1312InnerLogValid leaf1312CoversExact leaf1312LowerChecked

private noncomputable def leaf1313Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16), chiLo := (31/128), chiHi := (1/4) }

private noncomputable def leaf1313Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435707/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716396544) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (457331195/268435456) }, upper := { exponent := 0, mantissa := (111/64) } }, logOuter := sk112LogOuterCertificate, logK := sk112LogKCertificate, logChi := chi122LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434890239/137432793088) } }, logDArg := sk112LogDArgCertificate }

private noncomputable def leaf1313InnerLog : WideLogData :=
  innerPair90Data

set_option maxRecDepth 1000000 in
private theorem leaf1313LocalValidity :
    LeafFacts leaf1313Box leaf1313Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1313Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716396544) }) = true
      norm_num [leaf1313Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1313CertificateValid :
    WideCertificateValid leaf1313Box leaf1313Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk112ValidityFacts chi122ValidityFacts
    leaf1313LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1313CoverageChecked :
    coverageCheck (innerAD leaf1313Box) leaf1313InnerLog = true := by
  rfl'

private theorem leaf1313InnerLogValid :
    leaf1313InnerLog.Valid 8 (innerAD leaf1313Box) :=
  wideLogDataValid_of_cachedCheck endpoint20PositiveFacts
    endpoint139PositiveFacts.valid leaf1313CoverageChecked

private noncomputable def leaf1313InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629337/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1313InputLogOnePlusV_eq :
    leaf1313InputLogOnePlusV = outerEnclosure 24
      (leaf1313Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1313RoundedFacts : LeafRoundedFacts 8
    leaf1313Certificate.logOnePlusV leaf1313InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1313InputLogOnePlusV_eq }

private noncomputable def leaf1313Inputs : Inputs :=
  inputsOfCaches globalInput sk112RoundedInputs
    chi122InputQChi innerPair90Input
    leaf1313InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1313LowerChecked :
    lowerCheck 24 leaf1313Box leaf1313Inputs = true := by
  rfl'

private theorem leaf1313CoversExact : CoversExact 8
    leaf1313Box leaf1313Certificate leaf1313InnerLog leaf1313Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk112RoundedFacts chi122RoundedFacts
    innerPair90RoundedFacts leaf1313RoundedFacts (by rfl)

private theorem leaf1313FlatSound : Sound leaf1313Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1313CertificateValid
    leaf1313InnerLogValid leaf1313CoversExact leaf1313LowerChecked

private noncomputable def leaf1314Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (189/64), chiLo := (7/32), chiHi := (29/128) }

private noncomputable def leaf1314Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871347/536870912) }, vSqrt := { lower := (32765/32768), upper := (137436921855/137433340928) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (881798159/536870912) }, upper := { exponent := 0, mantissa := (13673/8192) } }, logOuter := sk115LogOuterCertificate, logK := sk115LogKCertificate, logChi := chi119LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (274870262783/274866681856) } }, logDArg := sk115LogDArgCertificate }

private noncomputable def leaf1314InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf1314LocalValidity :
    LeafFacts leaf1314Box leaf1314Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1314Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (137436921855/137433340928) }) = true
      norm_num [leaf1314Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1314CertificateValid :
    WideCertificateValid leaf1314Box leaf1314Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk115ValidityFacts chi119ValidityFacts
    leaf1314LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1314CoverageChecked :
    coverageCheck (innerAD leaf1314Box) leaf1314InnerLog = true := by
  rfl'

private theorem leaf1314InnerLogValid :
    leaf1314InnerLog.Valid 8 (innerAD leaf1314Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf1314CoverageChecked

private noncomputable def leaf1314InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629299/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1314InputLogOnePlusV_eq :
    leaf1314InputLogOnePlusV = outerEnclosure 24
      (leaf1314Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1314RoundedFacts : LeafRoundedFacts 8
    leaf1314Certificate.logOnePlusV leaf1314InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1314InputLogOnePlusV_eq }

private noncomputable def leaf1314Inputs : Inputs :=
  inputsOfCaches globalInput sk115RoundedInputs
    chi119InputQChi innerPair56Input
    leaf1314InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1314LowerChecked :
    lowerCheck 24 leaf1314Box leaf1314Inputs = true := by
  rfl'

private theorem leaf1314CoversExact : CoversExact 8
    leaf1314Box leaf1314Certificate leaf1314InnerLog leaf1314Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk115RoundedFacts chi119RoundedFacts
    innerPair56RoundedFacts leaf1314RoundedFacts (by rfl)

private theorem leaf1314FlatSound : Sound leaf1314Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1314CertificateValid
    leaf1314InnerLogValid leaf1314CoversExact leaf1314LowerChecked

private noncomputable def leaf1315Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (189/64), kHi := (95/32), chiLo := (7/32), chiHi := (29/128) }

private noncomputable def leaf1315Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871349/536870912) }, vSqrt := { lower := (32765/32768), upper := (45812307285/45811103744) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (883633053/536870912) }, upper := { exponent := 0, mantissa := (6851/4096) } }, logOuter := sk116LogOuterCertificate, logK := sk116LogKCertificate, logChi := chi119LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (91623411029/91622207488) } }, logDArg := sk116LogDArgCertificate }

private noncomputable def leaf1315InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf1315LocalValidity :
    LeafFacts leaf1315Box leaf1315Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1315Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (45812307285/45811103744) }) = true
      norm_num [leaf1315Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1315CertificateValid :
    WideCertificateValid leaf1315Box leaf1315Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk116ValidityFacts chi119ValidityFacts
    leaf1315LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1315CoverageChecked :
    coverageCheck (innerAD leaf1315Box) leaf1315InnerLog = true := by
  rfl'

private theorem leaf1315InnerLogValid :
    leaf1315InnerLog.Valid 8 (innerAD leaf1315Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf1315CoverageChecked

private noncomputable def leaf1315InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629301/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1315InputLogOnePlusV_eq :
    leaf1315InputLogOnePlusV = outerEnclosure 24
      (leaf1315Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1315RoundedFacts : LeafRoundedFacts 8
    leaf1315Certificate.logOnePlusV leaf1315InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1315InputLogOnePlusV_eq }

private noncomputable def leaf1315Inputs : Inputs :=
  inputsOfCaches globalInput sk116RoundedInputs
    chi119InputQChi innerPair56Input
    leaf1315InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1315LowerChecked :
    lowerCheck 24 leaf1315Box leaf1315Inputs = true := by
  rfl'

private theorem leaf1315CoversExact : CoversExact 8
    leaf1315Box leaf1315Certificate leaf1315InnerLog leaf1315Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk116RoundedFacts chi119RoundedFacts
    innerPair56RoundedFacts leaf1315RoundedFacts (by rfl)

private theorem leaf1315FlatSound : Sound leaf1315Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1315CertificateValid
    leaf1315InnerLogValid leaf1315CoversExact leaf1315LowerChecked

private noncomputable def leaf1316Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (189/64), chiLo := (29/128), chiHi := (15/64) }

private noncomputable def leaf1316Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871349/536870912) }, vSqrt := { lower := (32765/32768), upper := (137436921855/137433147392) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (894118173/536870912) }, upper := { exponent := 0, mantissa := (6931/4096) } }, logOuter := sk115LogOuterCertificate, logK := sk115LogKCertificate, logChi := chi120LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (274870069247/274866294784) } }, logDArg := sk115LogDArgCertificate }

private noncomputable def leaf1316InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf1316LocalValidity :
    LeafFacts leaf1316Box leaf1316Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1316Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (137436921855/137433147392) }) = true
      norm_num [leaf1316Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1316CertificateValid :
    WideCertificateValid leaf1316Box leaf1316Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk115ValidityFacts chi120ValidityFacts
    leaf1316LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1316CoverageChecked :
    coverageCheck (innerAD leaf1316Box) leaf1316InnerLog = true := by
  rfl'

private theorem leaf1316InnerLogValid :
    leaf1316InnerLog.Valid 8 (innerAD leaf1316Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf1316CoverageChecked

private noncomputable def leaf1316InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629311/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1316InputLogOnePlusV_eq :
    leaf1316InputLogOnePlusV = outerEnclosure 24
      (leaf1316Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1316RoundedFacts : LeafRoundedFacts 8
    leaf1316Certificate.logOnePlusV leaf1316InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1316InputLogOnePlusV_eq }

private noncomputable def leaf1316Inputs : Inputs :=
  inputsOfCaches globalInput sk115RoundedInputs
    chi120InputQChi innerPair57Input
    leaf1316InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1316LowerChecked :
    lowerCheck 24 leaf1316Box leaf1316Inputs = true := by
  rfl'

private theorem leaf1316CoversExact : CoversExact 8
    leaf1316Box leaf1316Certificate leaf1316InnerLog leaf1316Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk115RoundedFacts chi120RoundedFacts
    innerPair57RoundedFacts leaf1316RoundedFacts (by rfl)

private theorem leaf1316FlatSound : Sound leaf1316Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1316CertificateValid
    leaf1316InnerLogValid leaf1316CoversExact leaf1316LowerChecked

private noncomputable def leaf1317Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (189/64), kHi := (95/32), chiLo := (29/128), chiHi := (15/64) }

private noncomputable def leaf1317Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871351/536870912) }, vSqrt := { lower := (32765/32768), upper := (137436921855/137433116672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (896018599/536870912) }, upper := { exponent := 0, mantissa := (3473/2048) } }, logOuter := sk116LogOuterCertificate, logK := sk116LogKCertificate, logChi := chi120LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (274870038527/274866233344) } }, logDArg := sk116LogDArgCertificate }

private noncomputable def leaf1317InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf1317LocalValidity :
    LeafFacts leaf1317Box leaf1317Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1317Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (137436921855/137433116672) }) = true
      norm_num [leaf1317Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1317CertificateValid :
    WideCertificateValid leaf1317Box leaf1317Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk116ValidityFacts chi120ValidityFacts
    leaf1317LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1317CoverageChecked :
    coverageCheck (innerAD leaf1317Box) leaf1317InnerLog = true := by
  rfl'

private theorem leaf1317InnerLogValid :
    leaf1317InnerLog.Valid 8 (innerAD leaf1317Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf1317CoverageChecked

private noncomputable def leaf1317InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629313/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1317InputLogOnePlusV_eq :
    leaf1317InputLogOnePlusV = outerEnclosure 24
      (leaf1317Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1317RoundedFacts : LeafRoundedFacts 8
    leaf1317Certificate.logOnePlusV leaf1317InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1317InputLogOnePlusV_eq }

private noncomputable def leaf1317Inputs : Inputs :=
  inputsOfCaches globalInput sk116RoundedInputs
    chi120InputQChi innerPair57Input
    leaf1317InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1317LowerChecked :
    lowerCheck 24 leaf1317Box leaf1317Inputs = true := by
  rfl'

private theorem leaf1317CoversExact : CoversExact 8
    leaf1317Box leaf1317Certificate leaf1317InnerLog leaf1317Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk116RoundedFacts chi120RoundedFacts
    innerPair57RoundedFacts leaf1317RoundedFacts (by rfl)

private theorem leaf1317FlatSound : Sound leaf1317Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1317CertificateValid
    leaf1317InnerLogValid leaf1317CoversExact leaf1317LowerChecked

private noncomputable def leaf1318Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (191/64), chiLo := (7/32), chiHi := (29/128) }

private noncomputable def leaf1318Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871351/536870912) }, vSqrt := { lower := (32765/32768), upper := (137436921855/137433281536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (885467947/536870912) }, upper := { exponent := 0, mantissa := (13731/8192) } }, logOuter := sk117LogOuterCertificate, logK := sk117LogKCertificate, logChi := chi119LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (274870203391/274866563072) } }, logDArg := sk117LogDArgCertificate }

private noncomputable def leaf1318InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf1318LocalValidity :
    LeafFacts leaf1318Box leaf1318Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1318Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (137436921855/137433281536) }) = true
      norm_num [leaf1318Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1318CertificateValid :
    WideCertificateValid leaf1318Box leaf1318Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk117ValidityFacts chi119ValidityFacts
    leaf1318LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1318CoverageChecked :
    coverageCheck (innerAD leaf1318Box) leaf1318InnerLog = true := by
  rfl'

private theorem leaf1318InnerLogValid :
    leaf1318InnerLog.Valid 8 (innerAD leaf1318Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf1318CoverageChecked

private noncomputable def leaf1318InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629303/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1318InputLogOnePlusV_eq :
    leaf1318InputLogOnePlusV = outerEnclosure 24
      (leaf1318Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1318RoundedFacts : LeafRoundedFacts 8
    leaf1318Certificate.logOnePlusV leaf1318InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1318InputLogOnePlusV_eq }

private noncomputable def leaf1318Inputs : Inputs :=
  inputsOfCaches globalInput sk117RoundedInputs
    chi119InputQChi innerPair56Input
    leaf1318InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1318LowerChecked :
    lowerCheck 24 leaf1318Box leaf1318Inputs = true := by
  rfl'

private theorem leaf1318CoversExact : CoversExact 8
    leaf1318Box leaf1318Certificate leaf1318InnerLog leaf1318Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk117RoundedFacts chi119RoundedFacts
    innerPair56RoundedFacts leaf1318RoundedFacts (by rfl)

private theorem leaf1318FlatSound : Sound leaf1318Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1318CertificateValid
    leaf1318InnerLogValid leaf1318CoversExact leaf1318LowerChecked

private noncomputable def leaf1319Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (191/64), kHi := (3), chiLo := (7/32), chiHi := (29/128) }

private noncomputable def leaf1319Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871353/536870912) }, vSqrt := { lower := (65529/65536), upper := (27487384371/27486650368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (887302841/536870912) }, upper := { exponent := 0, mantissa := (215/128) } }, logOuter := sk118LogOuterCertificate, logK := sk118LogKCertificate, logChi := chi119LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (54974034739/54973300736) } }, logDArg := sk118LogDArgCertificate }

private noncomputable def leaf1319InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf1319LocalValidity :
    LeafFacts leaf1319Box leaf1319Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1319Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (27487384371/27486650368) }) = true
      norm_num [leaf1319Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1319CertificateValid :
    WideCertificateValid leaf1319Box leaf1319Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk118ValidityFacts chi119ValidityFacts
    leaf1319LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1319CoverageChecked :
    coverageCheck (innerAD leaf1319Box) leaf1319InnerLog = true := by
  rfl'

private theorem leaf1319InnerLogValid :
    leaf1319InnerLog.Valid 8 (innerAD leaf1319Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf1319CoverageChecked

private noncomputable def leaf1319InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629305/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1319InputLogOnePlusV_eq :
    leaf1319InputLogOnePlusV = outerEnclosure 24
      (leaf1319Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1319RoundedFacts : LeafRoundedFacts 8
    leaf1319Certificate.logOnePlusV leaf1319InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1319InputLogOnePlusV_eq }

private noncomputable def leaf1319Inputs : Inputs :=
  inputsOfCaches globalInput sk118RoundedInputs
    chi119InputQChi innerPair56Input
    leaf1319InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1319LowerChecked :
    lowerCheck 24 leaf1319Box leaf1319Inputs = true := by
  rfl'

private theorem leaf1319CoversExact : CoversExact 8
    leaf1319Box leaf1319Certificate leaf1319InnerLog leaf1319Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk118RoundedFacts chi119RoundedFacts
    innerPair56RoundedFacts leaf1319RoundedFacts (by rfl)

private theorem leaf1319FlatSound : Sound leaf1319Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1319CertificateValid
    leaf1319InnerLogValid leaf1319CoversExact leaf1319LowerChecked

private noncomputable def leaf1320Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (191/64), chiLo := (29/128), chiHi := (15/64) }

private noncomputable def leaf1320Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871353/536870912) }, vSqrt := { lower := (32765/32768), upper := (137436921855/137433085952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (897919025/536870912) }, upper := { exponent := 0, mantissa := (6961/4096) } }, logOuter := sk117LogOuterCertificate, logK := sk117LogKCertificate, logChi := chi120LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (274870007807/274866171904) } }, logDArg := sk117LogDArgCertificate }

private noncomputable def leaf1320InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf1320LocalValidity :
    LeafFacts leaf1320Box leaf1320Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1320Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (137436921855/137433085952) }) = true
      norm_num [leaf1320Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1320CertificateValid :
    WideCertificateValid leaf1320Box leaf1320Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk117ValidityFacts chi120ValidityFacts
    leaf1320LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1320CoverageChecked :
    coverageCheck (innerAD leaf1320Box) leaf1320InnerLog = true := by
  rfl'

private theorem leaf1320InnerLogValid :
    leaf1320InnerLog.Valid 8 (innerAD leaf1320Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf1320CoverageChecked

private noncomputable def leaf1320InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629315/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1320InputLogOnePlusV_eq :
    leaf1320InputLogOnePlusV = outerEnclosure 24
      (leaf1320Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1320RoundedFacts : LeafRoundedFacts 8
    leaf1320Certificate.logOnePlusV leaf1320InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1320InputLogOnePlusV_eq }

private noncomputable def leaf1320Inputs : Inputs :=
  inputsOfCaches globalInput sk117RoundedInputs
    chi120InputQChi innerPair57Input
    leaf1320InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1320LowerChecked :
    lowerCheck 24 leaf1320Box leaf1320Inputs = true := by
  rfl'

private theorem leaf1320CoversExact : CoversExact 8
    leaf1320Box leaf1320Certificate leaf1320InnerLog leaf1320Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk117RoundedFacts chi120RoundedFacts
    innerPair57RoundedFacts leaf1320RoundedFacts (by rfl)

private theorem leaf1320FlatSound : Sound leaf1320Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1320CertificateValid
    leaf1320InnerLogValid leaf1320CoversExact leaf1320LowerChecked

private noncomputable def leaf1321Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (191/64), kHi := (3), chiLo := (29/128), chiHi := (15/64) }

private noncomputable def leaf1321Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871355/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433055232) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (899819451/536870912) }, upper := { exponent := 0, mantissa := (109/64) } }, logOuter := sk118LogOuterCertificate, logK := sk118LogKCertificate, logChi := chi120LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869977087/274866110464) } }, logDArg := sk118LogDArgCertificate }

private noncomputable def leaf1321InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf1321LocalValidity :
    LeafFacts leaf1321Box leaf1321Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1321Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433055232) }) = true
      norm_num [leaf1321Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1321CertificateValid :
    WideCertificateValid leaf1321Box leaf1321Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk118ValidityFacts chi120ValidityFacts
    leaf1321LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1321CoverageChecked :
    coverageCheck (innerAD leaf1321Box) leaf1321InnerLog = true := by
  rfl'

private theorem leaf1321InnerLogValid :
    leaf1321InnerLog.Valid 8 (innerAD leaf1321Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf1321CoverageChecked

private noncomputable def leaf1321InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629317/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1321InputLogOnePlusV_eq :
    leaf1321InputLogOnePlusV = outerEnclosure 24
      (leaf1321Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1321RoundedFacts : LeafRoundedFacts 8
    leaf1321Certificate.logOnePlusV leaf1321InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1321InputLogOnePlusV_eq }

private noncomputable def leaf1321Inputs : Inputs :=
  inputsOfCaches globalInput sk118RoundedInputs
    chi120InputQChi innerPair57Input
    leaf1321InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1321LowerChecked :
    lowerCheck 24 leaf1321Box leaf1321Inputs = true := by
  rfl'

private theorem leaf1321CoversExact : CoversExact 8
    leaf1321Box leaf1321Certificate leaf1321InnerLog leaf1321Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk118RoundedFacts chi120RoundedFacts
    innerPair57RoundedFacts leaf1321RoundedFacts (by rfl)

private theorem leaf1321FlatSound : Sound leaf1321Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1321CertificateValid
    leaf1321InnerLogValid leaf1321CoversExact leaf1321LowerChecked

private noncomputable def leaf1322Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (189/64), chiLo := (15/64), chiHi := (31/128) }

private noncomputable def leaf1322Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871351/536870912) }, vSqrt := { lower := (32765/32768), upper := (137436921855/137432953856) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (906438187/536870912) }, upper := { exponent := 0, mantissa := (14051/8192) } }, logOuter := sk115LogOuterCertificate, logK := sk115LogKCertificate, logChi := chi121LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (274869875711/274865907712) } }, logDArg := sk115LogDArgCertificate }

private noncomputable def leaf1322InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf1322LocalValidity :
    LeafFacts leaf1322Box leaf1322Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1322Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (137436921855/137432953856) }) = true
      norm_num [leaf1322Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1322CertificateValid :
    WideCertificateValid leaf1322Box leaf1322Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk115ValidityFacts chi121ValidityFacts
    leaf1322LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1322CoverageChecked :
    coverageCheck (innerAD leaf1322Box) leaf1322InnerLog = true := by
  rfl'

private theorem leaf1322InnerLogValid :
    leaf1322InnerLog.Valid 8 (innerAD leaf1322Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf1322CoverageChecked

private noncomputable def leaf1322InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629323/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1322InputLogOnePlusV_eq :
    leaf1322InputLogOnePlusV = outerEnclosure 24
      (leaf1322Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1322RoundedFacts : LeafRoundedFacts 8
    leaf1322Certificate.logOnePlusV leaf1322InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1322InputLogOnePlusV_eq }

private noncomputable def leaf1322Inputs : Inputs :=
  inputsOfCaches globalInput sk115RoundedInputs
    chi121InputQChi innerPair64Input
    leaf1322InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1322LowerChecked :
    lowerCheck 24 leaf1322Box leaf1322Inputs = true := by
  rfl'

private theorem leaf1322CoversExact : CoversExact 8
    leaf1322Box leaf1322Certificate leaf1322InnerLog leaf1322Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk115RoundedFacts chi121RoundedFacts
    innerPair64RoundedFacts leaf1322RoundedFacts (by rfl)

private theorem leaf1322FlatSound : Sound leaf1322Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1322CertificateValid
    leaf1322InnerLogValid leaf1322CoversExact leaf1322LowerChecked

private noncomputable def leaf1323Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (189/64), kHi := (95/32), chiLo := (15/64), chiHi := (31/128) }

private noncomputable def leaf1323Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871353/536870912) }, vSqrt := { lower := (32765/32768), upper := (8084524815/8084289536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (908404145/536870912) }, upper := { exponent := 0, mantissa := (7041/4096) } }, logOuter := sk116LogOuterCertificate, logK := sk116LogKCertificate, logChi := chi121LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (16168814351/16168579072) } }, logDArg := sk116LogDArgCertificate }

private noncomputable def leaf1323InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf1323LocalValidity :
    LeafFacts leaf1323Box leaf1323Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1323Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8084524815/8084289536) }) = true
      norm_num [leaf1323Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1323CertificateValid :
    WideCertificateValid leaf1323Box leaf1323Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk116ValidityFacts chi121ValidityFacts
    leaf1323LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1323CoverageChecked :
    coverageCheck (innerAD leaf1323Box) leaf1323InnerLog = true := by
  rfl'

private theorem leaf1323InnerLogValid :
    leaf1323InnerLog.Valid 8 (innerAD leaf1323Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf1323CoverageChecked

private noncomputable def leaf1323InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629325/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1323InputLogOnePlusV_eq :
    leaf1323InputLogOnePlusV = outerEnclosure 24
      (leaf1323Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1323RoundedFacts : LeafRoundedFacts 8
    leaf1323Certificate.logOnePlusV leaf1323InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1323InputLogOnePlusV_eq }

private noncomputable def leaf1323Inputs : Inputs :=
  inputsOfCaches globalInput sk116RoundedInputs
    chi121InputQChi innerPair64Input
    leaf1323InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1323LowerChecked :
    lowerCheck 24 leaf1323Box leaf1323Inputs = true := by
  rfl'

private theorem leaf1323CoversExact : CoversExact 8
    leaf1323Box leaf1323Certificate leaf1323InnerLog leaf1323Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk116RoundedFacts chi121RoundedFacts
    innerPair64RoundedFacts leaf1323RoundedFacts (by rfl)

private theorem leaf1323FlatSound : Sound leaf1323Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1323CertificateValid
    leaf1323InnerLogValid leaf1323CoversExact leaf1323LowerChecked

private noncomputable def leaf1324Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (189/64), chiLo := (31/128), chiHi := (1/4) }

private noncomputable def leaf1324Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871353/536870912) }, vSqrt := { lower := (32765/32768), upper := (27487384371/27486552064) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (918758201/536870912) }, upper := { exponent := 0, mantissa := (445/256) } }, logOuter := sk115LogOuterCertificate, logK := sk115LogKCertificate, logChi := chi122LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (54973936435/54973104128) } }, logDArg := sk115LogDArgCertificate }

private noncomputable def leaf1324InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf1324LocalValidity :
    LeafFacts leaf1324Box leaf1324Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1324Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (27487384371/27486552064) }) = true
      norm_num [leaf1324Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1324CertificateValid :
    WideCertificateValid leaf1324Box leaf1324Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk115ValidityFacts chi122ValidityFacts
    leaf1324LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1324CoverageChecked :
    coverageCheck (innerAD leaf1324Box) leaf1324InnerLog = true := by
  rfl'

private theorem leaf1324InnerLogValid :
    leaf1324InnerLog.Valid 8 (innerAD leaf1324Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf1324CoverageChecked

private noncomputable def leaf1324InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629335/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1324InputLogOnePlusV_eq :
    leaf1324InputLogOnePlusV = outerEnclosure 24
      (leaf1324Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1324RoundedFacts : LeafRoundedFacts 8
    leaf1324Certificate.logOnePlusV leaf1324InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1324InputLogOnePlusV_eq }

private noncomputable def leaf1324Inputs : Inputs :=
  inputsOfCaches globalInput sk115RoundedInputs
    chi122InputQChi innerPair64Input
    leaf1324InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1324LowerChecked :
    lowerCheck 24 leaf1324Box leaf1324Inputs = true := by
  rfl'

private theorem leaf1324CoversExact : CoversExact 8
    leaf1324Box leaf1324Certificate leaf1324InnerLog leaf1324Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk115RoundedFacts chi122RoundedFacts
    innerPair64RoundedFacts leaf1324RoundedFacts (by rfl)

private theorem leaf1324FlatSound : Sound leaf1324Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1324CertificateValid
    leaf1324InnerLogValid leaf1324CoversExact leaf1324LowerChecked

private noncomputable def leaf1325Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (189/64), kHi := (95/32), chiLo := (31/128), chiHi := (1/4) }

private noncomputable def leaf1325Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871355/536870912) }, vSqrt := { lower := (32765/32768), upper := (45812307285/45810909184) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (920789691/536870912) }, upper := { exponent := 0, mantissa := (223/128) } }, logOuter := sk116LogOuterCertificate, logK := sk116LogKCertificate, logChi := chi122LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (91623216469/91621818368) } }, logDArg := sk116LogDArgCertificate }

private noncomputable def leaf1325InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf1325LocalValidity :
    LeafFacts leaf1325Box leaf1325Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1325Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (45812307285/45810909184) }) = true
      norm_num [leaf1325Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1325CertificateValid :
    WideCertificateValid leaf1325Box leaf1325Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk116ValidityFacts chi122ValidityFacts
    leaf1325LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1325CoverageChecked :
    coverageCheck (innerAD leaf1325Box) leaf1325InnerLog = true := by
  rfl'

private theorem leaf1325InnerLogValid :
    leaf1325InnerLog.Valid 8 (innerAD leaf1325Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf1325CoverageChecked

private noncomputable def leaf1325InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629337/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1325InputLogOnePlusV_eq :
    leaf1325InputLogOnePlusV = outerEnclosure 24
      (leaf1325Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1325RoundedFacts : LeafRoundedFacts 8
    leaf1325Certificate.logOnePlusV leaf1325InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1325InputLogOnePlusV_eq }

private noncomputable def leaf1325Inputs : Inputs :=
  inputsOfCaches globalInput sk116RoundedInputs
    chi122InputQChi innerPair64Input
    leaf1325InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1325LowerChecked :
    lowerCheck 24 leaf1325Box leaf1325Inputs = true := by
  rfl'

private theorem leaf1325CoversExact : CoversExact 8
    leaf1325Box leaf1325Certificate leaf1325InnerLog leaf1325Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk116RoundedFacts chi122RoundedFacts
    innerPair64RoundedFacts leaf1325RoundedFacts (by rfl)

private theorem leaf1325FlatSound : Sound leaf1325Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1325CertificateValid
    leaf1325InnerLogValid leaf1325CoversExact leaf1325LowerChecked

private noncomputable def leaf1326Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (191/64), chiLo := (15/64), chiHi := (31/128) }

private noncomputable def leaf1326Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871355/536870912) }, vSqrt := { lower := (32765/32768), upper := (15270769095/15270321152) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (910370103/536870912) }, upper := { exponent := 0, mantissa := (14113/8192) } }, logOuter := sk117LogOuterCertificate, logK := sk117LogKCertificate, logChi := chi121LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (30541090247/30540642304) } }, logDArg := sk117LogDArgCertificate }

private noncomputable def leaf1326InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf1326LocalValidity :
    LeafFacts leaf1326Box leaf1326Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1326Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (15270769095/15270321152) }) = true
      norm_num [leaf1326Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1326CertificateValid :
    WideCertificateValid leaf1326Box leaf1326Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk117ValidityFacts chi121ValidityFacts
    leaf1326LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1326CoverageChecked :
    coverageCheck (innerAD leaf1326Box) leaf1326InnerLog = true := by
  rfl'

private theorem leaf1326InnerLogValid :
    leaf1326InnerLog.Valid 8 (innerAD leaf1326Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf1326CoverageChecked

private noncomputable def leaf1326InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629327/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1326InputLogOnePlusV_eq :
    leaf1326InputLogOnePlusV = outerEnclosure 24
      (leaf1326Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1326RoundedFacts : LeafRoundedFacts 8
    leaf1326Certificate.logOnePlusV leaf1326InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1326InputLogOnePlusV_eq }

private noncomputable def leaf1326Inputs : Inputs :=
  inputsOfCaches globalInput sk117RoundedInputs
    chi121InputQChi innerPair64Input
    leaf1326InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1326LowerChecked :
    lowerCheck 24 leaf1326Box leaf1326Inputs = true := by
  rfl'

private theorem leaf1326CoversExact : CoversExact 8
    leaf1326Box leaf1326Certificate leaf1326InnerLog leaf1326Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk117RoundedFacts chi121RoundedFacts
    innerPair64RoundedFacts leaf1326RoundedFacts (by rfl)

private theorem leaf1326FlatSound : Sound leaf1326Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1326CertificateValid
    leaf1326InnerLogValid leaf1326CoversExact leaf1326LowerChecked

private noncomputable def leaf1327Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (191/64), kHi := (3), chiLo := (15/64), chiHi := (31/128) }

private noncomputable def leaf1327Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871357/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432858624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (912336061/536870912) }, upper := { exponent := 0, mantissa := (221/128) } }, logOuter := sk118LogOuterCertificate, logK := sk118LogKCertificate, logChi := chi121LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869780479/274865717248) } }, logDArg := sk118LogDArgCertificate }

private noncomputable def leaf1327InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf1327LocalValidity :
    LeafFacts leaf1327Box leaf1327Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1327Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432858624) }) = true
      norm_num [leaf1327Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1327CertificateValid :
    WideCertificateValid leaf1327Box leaf1327Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk118ValidityFacts chi121ValidityFacts
    leaf1327LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1327CoverageChecked :
    coverageCheck (innerAD leaf1327Box) leaf1327InnerLog = true := by
  rfl'

private theorem leaf1327InnerLogValid :
    leaf1327InnerLog.Valid 8 (innerAD leaf1327Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf1327CoverageChecked

private noncomputable def leaf1327InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629329/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1327InputLogOnePlusV_eq :
    leaf1327InputLogOnePlusV = outerEnclosure 24
      (leaf1327Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1327RoundedFacts : LeafRoundedFacts 8
    leaf1327Certificate.logOnePlusV leaf1327InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1327InputLogOnePlusV_eq }

private noncomputable def leaf1327Inputs : Inputs :=
  inputsOfCaches globalInput sk118RoundedInputs
    chi121InputQChi innerPair64Input
    leaf1327InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1327LowerChecked :
    lowerCheck 24 leaf1327Box leaf1327Inputs = true := by
  rfl'

private theorem leaf1327CoversExact : CoversExact 8
    leaf1327Box leaf1327Certificate leaf1327InnerLog leaf1327Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk118RoundedFacts chi121RoundedFacts
    innerPair64RoundedFacts leaf1327RoundedFacts (by rfl)

private theorem leaf1327FlatSound : Sound leaf1327Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1327CertificateValid
    leaf1327InnerLogValid leaf1327CoversExact leaf1327LowerChecked

private noncomputable def leaf1328Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (191/64), chiLo := (31/128), chiHi := (1/4) }

private noncomputable def leaf1328Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871357/536870912) }, vSqrt := { lower := (32765/32768), upper := (137436921855/137432694784) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (922821181/536870912) }, upper := { exponent := 0, mantissa := (447/256) } }, logOuter := sk117LogOuterCertificate, logK := sk117LogKCertificate, logChi := chi122LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (274869616639/274865389568) } }, logDArg := sk117LogDArgCertificate }

private noncomputable def leaf1328InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf1328LocalValidity :
    LeafFacts leaf1328Box leaf1328Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1328Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (137436921855/137432694784) }) = true
      norm_num [leaf1328Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1328CertificateValid :
    WideCertificateValid leaf1328Box leaf1328Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk117ValidityFacts chi122ValidityFacts
    leaf1328LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1328CoverageChecked :
    coverageCheck (innerAD leaf1328Box) leaf1328InnerLog = true := by
  rfl'

private theorem leaf1328InnerLogValid :
    leaf1328InnerLog.Valid 8 (innerAD leaf1328Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf1328CoverageChecked

private noncomputable def leaf1328InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629339/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1328InputLogOnePlusV_eq :
    leaf1328InputLogOnePlusV = outerEnclosure 24
      (leaf1328Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1328RoundedFacts : LeafRoundedFacts 8
    leaf1328Certificate.logOnePlusV leaf1328InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1328InputLogOnePlusV_eq }

private noncomputable def leaf1328Inputs : Inputs :=
  inputsOfCaches globalInput sk117RoundedInputs
    chi122InputQChi innerPair64Input
    leaf1328InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1328LowerChecked :
    lowerCheck 24 leaf1328Box leaf1328Inputs = true := by
  rfl'

private theorem leaf1328CoversExact : CoversExact 8
    leaf1328Box leaf1328Certificate leaf1328InnerLog leaf1328Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk117RoundedFacts chi122RoundedFacts
    innerPair64RoundedFacts leaf1328RoundedFacts (by rfl)

private theorem leaf1328FlatSound : Sound leaf1328Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1328CertificateValid
    leaf1328InnerLogValid leaf1328CoversExact leaf1328LowerChecked

private noncomputable def leaf1329Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (191/64), kHi := (3), chiLo := (31/128), chiHi := (1/4) }

private noncomputable def leaf1329Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871359/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432662016) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (924852671/536870912) }, upper := { exponent := 0, mantissa := (7/4) } }, logOuter := sk118LogOuterCertificate, logK := sk118LogKCertificate, logChi := chi122LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869583871/274865324032) } }, logDArg := sk118LogDArgCertificate }

private noncomputable def leaf1329InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf1329LocalValidity :
    LeafFacts leaf1329Box leaf1329Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1329Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432662016) }) = true
      norm_num [leaf1329Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1329CertificateValid :
    WideCertificateValid leaf1329Box leaf1329Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk118ValidityFacts chi122ValidityFacts
    leaf1329LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1329CoverageChecked :
    coverageCheck (innerAD leaf1329Box) leaf1329InnerLog = true := by
  rfl'

private theorem leaf1329InnerLogValid :
    leaf1329InnerLog.Valid 8 (innerAD leaf1329Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf1329CoverageChecked

private noncomputable def leaf1329InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629341/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1329InputLogOnePlusV_eq :
    leaf1329InputLogOnePlusV = outerEnclosure 24
      (leaf1329Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1329RoundedFacts : LeafRoundedFacts 8
    leaf1329Certificate.logOnePlusV leaf1329InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1329InputLogOnePlusV_eq }

private noncomputable def leaf1329Inputs : Inputs :=
  inputsOfCaches globalInput sk118RoundedInputs
    chi122InputQChi innerPair64Input
    leaf1329InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1329LowerChecked :
    lowerCheck 24 leaf1329Box leaf1329Inputs = true := by
  rfl'

private theorem leaf1329CoversExact : CoversExact 8
    leaf1329Box leaf1329Certificate leaf1329InnerLog leaf1329Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk118RoundedFacts chi122RoundedFacts
    innerPair64RoundedFacts leaf1329RoundedFacts (by rfl)

private theorem leaf1329FlatSound : Sound leaf1329Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1329CertificateValid
    leaf1329InnerLogValid leaf1329CoversExact leaf1329LowerChecked

private noncomputable def component30Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component30Node0_sound : Sound component30Node0Box :=
  sound_of_literal_split component30Node0Box leaf1287Box leaf1288Box
    .chi (29/128) (by rfl) (by rfl)
    leaf1287FlatSound leaf1288FlatSound

private noncomputable def component30Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component30Node1_sound : Sound component30Node1Box :=
  sound_of_literal_split component30Node1Box leaf1289Box leaf1290Box
    .chi (29/128) (by rfl) (by rfl)
    leaf1289FlatSound leaf1290FlatSound

private noncomputable def component30Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component30Node2_sound : Sound component30Node2Box :=
  sound_of_literal_split component30Node2Box component30Node0Box component30Node1Box
    .k (89/32) (by rfl) (by rfl)
    component30Node0_sound component30Node1_sound

private noncomputable def component30Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component30Node3_sound : Sound component30Node3Box :=
  sound_of_literal_split component30Node3Box leaf1291Box leaf1292Box
    .chi (31/128) (by rfl) (by rfl)
    leaf1291FlatSound leaf1292FlatSound

private noncomputable def component30Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component30Node4_sound : Sound component30Node4Box :=
  sound_of_literal_split component30Node4Box leaf1293Box leaf1294Box
    .chi (31/128) (by rfl) (by rfl)
    leaf1293FlatSound leaf1294FlatSound

private noncomputable def component30Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component30Node5_sound : Sound component30Node5Box :=
  sound_of_literal_split component30Node5Box component30Node3Box component30Node4Box
    .k (89/32) (by rfl) (by rfl)
    component30Node3_sound component30Node4_sound

private noncomputable def component30Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (7/32), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component30Node6_sound : Sound component30Node6Box :=
  sound_of_literal_split component30Node6Box component30Node2Box component30Node5Box
    .chi (15/64) (by rfl) (by rfl)
    component30Node2_sound component30Node5_sound

private noncomputable def component30Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component30Node7_sound : Sound component30Node7Box :=
  sound_of_literal_split component30Node7Box leaf1295Box leaf1296Box
    .chi (29/128) (by rfl) (by rfl)
    leaf1295FlatSound leaf1296FlatSound

private noncomputable def component30Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component30Node8_sound : Sound component30Node8Box :=
  sound_of_literal_split component30Node8Box leaf1297Box leaf1298Box
    .chi (29/128) (by rfl) (by rfl)
    leaf1297FlatSound leaf1298FlatSound

private noncomputable def component30Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component30Node9_sound : Sound component30Node9Box :=
  sound_of_literal_split component30Node9Box component30Node7Box component30Node8Box
    .k (91/32) (by rfl) (by rfl)
    component30Node7_sound component30Node8_sound

private noncomputable def component30Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component30Node10_sound : Sound component30Node10Box :=
  sound_of_literal_split component30Node10Box leaf1299Box leaf1300Box
    .chi (31/128) (by rfl) (by rfl)
    leaf1299FlatSound leaf1300FlatSound

private noncomputable def component30Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component30Node11_sound : Sound component30Node11Box :=
  sound_of_literal_split component30Node11Box leaf1301Box leaf1302Box
    .chi (31/128) (by rfl) (by rfl)
    leaf1301FlatSound leaf1302FlatSound

private noncomputable def component30Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component30Node12_sound : Sound component30Node12Box :=
  sound_of_literal_split component30Node12Box component30Node10Box component30Node11Box
    .k (91/32) (by rfl) (by rfl)
    component30Node10_sound component30Node11_sound

private noncomputable def component30Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (7/32), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component30Node13_sound : Sound component30Node13Box :=
  sound_of_literal_split component30Node13Box component30Node9Box component30Node12Box
    .chi (15/64) (by rfl) (by rfl)
    component30Node9_sound component30Node12_sound

private noncomputable def component30Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (7/32), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component30Node14_sound : Sound component30Node14Box :=
  sound_of_literal_split component30Node14Box component30Node6Box component30Node13Box
    .k (45/16) (by rfl) (by rfl)
    component30Node6_sound component30Node13_sound

private noncomputable def component30Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component30Node15_sound : Sound component30Node15Box :=
  sound_of_literal_split component30Node15Box leaf1303Box leaf1304Box
    .chi (29/128) (by rfl) (by rfl)
    leaf1303FlatSound leaf1304FlatSound

private noncomputable def component30Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16), chiLo := (7/32), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component30Node16_sound : Sound component30Node16Box :=
  sound_of_literal_split component30Node16Box leaf1305Box leaf1306Box
    .k (187/64) (by rfl) (by rfl)
    leaf1305FlatSound leaf1306FlatSound

private noncomputable def component30Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16), chiLo := (29/128), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component30Node17_sound : Sound component30Node17Box :=
  sound_of_literal_split component30Node17Box leaf1307Box leaf1308Box
    .k (187/64) (by rfl) (by rfl)
    leaf1307FlatSound leaf1308FlatSound

private noncomputable def component30Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component30Node18_sound : Sound component30Node18Box :=
  sound_of_literal_split component30Node18Box component30Node16Box component30Node17Box
    .chi (29/128) (by rfl) (by rfl)
    component30Node16_sound component30Node17_sound

private noncomputable def component30Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component30Node19_sound : Sound component30Node19Box :=
  sound_of_literal_split component30Node19Box component30Node15Box component30Node18Box
    .k (93/32) (by rfl) (by rfl)
    component30Node15_sound component30Node18_sound

private noncomputable def component30Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component30Node20_sound : Sound component30Node20Box :=
  sound_of_literal_split component30Node20Box leaf1309Box leaf1310Box
    .chi (31/128) (by rfl) (by rfl)
    leaf1309FlatSound leaf1310FlatSound

private noncomputable def component30Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16), chiLo := (15/64), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component30Node21_sound : Sound component30Node21Box :=
  sound_of_literal_split component30Node21Box leaf1311Box leaf1312Box
    .k (187/64) (by rfl) (by rfl)
    leaf1311FlatSound leaf1312FlatSound

private noncomputable def component30Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component30Node22_sound : Sound component30Node22Box :=
  sound_of_literal_split component30Node22Box component30Node21Box leaf1313Box
    .chi (31/128) (by rfl) (by rfl)
    component30Node21_sound leaf1313FlatSound

private noncomputable def component30Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component30Node23_sound : Sound component30Node23Box :=
  sound_of_literal_split component30Node23Box component30Node20Box component30Node22Box
    .k (93/32) (by rfl) (by rfl)
    component30Node20_sound component30Node22_sound

private noncomputable def component30Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (7/32), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component30Node24_sound : Sound component30Node24Box :=
  sound_of_literal_split component30Node24Box component30Node19Box component30Node23Box
    .chi (15/64) (by rfl) (by rfl)
    component30Node19_sound component30Node23_sound

private noncomputable def component30Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (95/32), chiLo := (7/32), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component30Node25_sound : Sound component30Node25Box :=
  sound_of_literal_split component30Node25Box leaf1314Box leaf1315Box
    .k (189/64) (by rfl) (by rfl)
    leaf1314FlatSound leaf1315FlatSound

private noncomputable def component30Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (95/32), chiLo := (29/128), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component30Node26_sound : Sound component30Node26Box :=
  sound_of_literal_split component30Node26Box leaf1316Box leaf1317Box
    .k (189/64) (by rfl) (by rfl)
    leaf1316FlatSound leaf1317FlatSound

private noncomputable def component30Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (95/32), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component30Node27_sound : Sound component30Node27Box :=
  sound_of_literal_split component30Node27Box component30Node25Box component30Node26Box
    .chi (29/128) (by rfl) (by rfl)
    component30Node25_sound component30Node26_sound

private noncomputable def component30Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (7/32), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component30Node28_sound : Sound component30Node28Box :=
  sound_of_literal_split component30Node28Box leaf1318Box leaf1319Box
    .k (191/64) (by rfl) (by rfl)
    leaf1318FlatSound leaf1319FlatSound

private noncomputable def component30Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (29/128), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component30Node29_sound : Sound component30Node29Box :=
  sound_of_literal_split component30Node29Box leaf1320Box leaf1321Box
    .k (191/64) (by rfl) (by rfl)
    leaf1320FlatSound leaf1321FlatSound

private noncomputable def component30Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component30Node30_sound : Sound component30Node30Box :=
  sound_of_literal_split component30Node30Box component30Node28Box component30Node29Box
    .chi (29/128) (by rfl) (by rfl)
    component30Node28_sound component30Node29_sound

private noncomputable def component30Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component30Node31_sound : Sound component30Node31Box :=
  sound_of_literal_split component30Node31Box component30Node27Box component30Node30Box
    .k (95/32) (by rfl) (by rfl)
    component30Node27_sound component30Node30_sound

private noncomputable def component30Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (95/32), chiLo := (15/64), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component30Node32_sound : Sound component30Node32Box :=
  sound_of_literal_split component30Node32Box leaf1322Box leaf1323Box
    .k (189/64) (by rfl) (by rfl)
    leaf1322FlatSound leaf1323FlatSound

private noncomputable def component30Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (95/32), chiLo := (31/128), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component30Node33_sound : Sound component30Node33Box :=
  sound_of_literal_split component30Node33Box leaf1324Box leaf1325Box
    .k (189/64) (by rfl) (by rfl)
    leaf1324FlatSound leaf1325FlatSound

private noncomputable def component30Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (95/32), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component30Node34_sound : Sound component30Node34Box :=
  sound_of_literal_split component30Node34Box component30Node32Box component30Node33Box
    .chi (31/128) (by rfl) (by rfl)
    component30Node32_sound component30Node33_sound

private noncomputable def component30Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (15/64), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component30Node35_sound : Sound component30Node35Box :=
  sound_of_literal_split component30Node35Box leaf1326Box leaf1327Box
    .k (191/64) (by rfl) (by rfl)
    leaf1326FlatSound leaf1327FlatSound

private noncomputable def component30Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (31/128), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component30Node36_sound : Sound component30Node36Box :=
  sound_of_literal_split component30Node36Box leaf1328Box leaf1329Box
    .k (191/64) (by rfl) (by rfl)
    leaf1328FlatSound leaf1329FlatSound

private noncomputable def component30Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component30Node37_sound : Sound component30Node37Box :=
  sound_of_literal_split component30Node37Box component30Node35Box component30Node36Box
    .chi (31/128) (by rfl) (by rfl)
    component30Node35_sound component30Node36_sound

private noncomputable def component30Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component30Node38_sound : Sound component30Node38Box :=
  sound_of_literal_split component30Node38Box component30Node34Box component30Node37Box
    .k (95/32) (by rfl) (by rfl)
    component30Node34_sound component30Node37_sound

private noncomputable def component30Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (7/32), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component30Node39_sound : Sound component30Node39Box :=
  sound_of_literal_split component30Node39Box component30Node31Box component30Node38Box
    .chi (15/64) (by rfl) (by rfl)
    component30Node31_sound component30Node38_sound

private noncomputable def component30Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (7/32), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component30Node40_sound : Sound component30Node40Box :=
  sound_of_literal_split component30Node40Box component30Node24Box component30Node39Box
    .k (47/16) (by rfl) (by rfl)
    component30Node24_sound component30Node39_sound

noncomputable def component30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (3), chiLo := (7/32), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
theorem component30_sound : Sound component30Box :=
  sound_of_literal_split component30Box component30Node14Box component30Node40Box
    .k (23/8) (by rfl) (by rfl)
    component30Node14_sound component30Node40_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
