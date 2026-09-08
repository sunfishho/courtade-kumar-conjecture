import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch4
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

private noncomputable def leaf4172Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (3/8), chiHi := (49/128) }

private noncomputable def leaf4172Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435731/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357505536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (545209583/536870912) }, upper := { exponent := 1, mantissa := (8457/8192) } }, logOuter := sk107LogOuterCertificate, logK := sk107LogKCertificate, logChi := chi259LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716228095/68715011072) } }, logDArg := sk107LogDArgCertificate }

private noncomputable def leaf4172InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf4172LocalValidity :
    LeafFacts leaf4172Box leaf4172Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4172Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357505536) }) = true
      norm_num [leaf4172Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4172CertificateValid :
    WideCertificateValid leaf4172Box leaf4172Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk107ValidityFacts chi259ValidityFacts
    leaf4172LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4172CoverageChecked :
    coverageCheck (innerAD leaf4172Box) leaf4172InnerLog = true := by
  rfl'

private theorem leaf4172InnerLogValid :
    leaf4172InnerLog.Valid 8 (innerAD leaf4172Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf4172CoverageChecked

private noncomputable def leaf4172InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814689/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4172InputLogOnePlusV_eq :
    leaf4172InputLogOnePlusV = outerEnclosure 24
      (leaf4172Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4172RoundedFacts : LeafRoundedFacts 8
    leaf4172Certificate.logOnePlusV leaf4172InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4172InputLogOnePlusV_eq }

private noncomputable def leaf4172Inputs : Inputs :=
  inputsOfCaches globalInput sk107RoundedInputs
    chi259InputQChi innerPair117Input
    leaf4172InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4172LowerChecked :
    lowerCheck 24 leaf4172Box leaf4172Inputs = true := by
  rfl'

private theorem leaf4172CoversExact : CoversExact 8
    leaf4172Box leaf4172Certificate leaf4172InnerLog leaf4172Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk107RoundedFacts chi259RoundedFacts
    innerPair117RoundedFacts leaf4172RoundedFacts (by rfl)

private theorem leaf4172FlatSound : Sound leaf4172Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4172CertificateValid
    leaf4172InnerLogValid leaf4172CoversExact leaf4172LowerChecked

private noncomputable def leaf4173Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (3/8), chiHi := (49/128) }

private noncomputable def leaf4173Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435733/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357480448) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (548355117/536870912) }, upper := { exponent := 1, mantissa := (4253/4096) } }, logOuter := sk108LogOuterCertificate, logK := sk108LogKCertificate, logChi := chi259LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716203007/68714960896) } }, logDArg := sk108LogDArgCertificate }

private noncomputable def leaf4173InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf4173LocalValidity :
    LeafFacts leaf4173Box leaf4173Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4173Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357480448) }) = true
      norm_num [leaf4173Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4173CertificateValid :
    WideCertificateValid leaf4173Box leaf4173Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk108ValidityFacts chi259ValidityFacts
    leaf4173LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4173CoverageChecked :
    coverageCheck (innerAD leaf4173Box) leaf4173InnerLog = true := by
  rfl'

private theorem leaf4173InnerLogValid :
    leaf4173InnerLog.Valid 8 (innerAD leaf4173Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf4173CoverageChecked

private noncomputable def leaf4173InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453673/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf4173InputLogOnePlusV_eq :
    leaf4173InputLogOnePlusV = outerEnclosure 24
      (leaf4173Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4173RoundedFacts : LeafRoundedFacts 8
    leaf4173Certificate.logOnePlusV leaf4173InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4173InputLogOnePlusV_eq }

private noncomputable def leaf4173Inputs : Inputs :=
  inputsOfCaches globalInput sk108RoundedInputs
    chi259InputQChi innerPair117Input
    leaf4173InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4173LowerChecked :
    lowerCheck 24 leaf4173Box leaf4173Inputs = true := by
  rfl'

private theorem leaf4173CoversExact : CoversExact 8
    leaf4173Box leaf4173Certificate leaf4173InnerLog leaf4173Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk108RoundedFacts chi259RoundedFacts
    innerPair117RoundedFacts leaf4173RoundedFacts (by rfl)

private theorem leaf4173FlatSound : Sound leaf4173Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4173CertificateValid
    leaf4173InnerLogValid leaf4173CoversExact leaf4173LowerChecked

private noncomputable def leaf4174Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (49/128), chiHi := (25/64) }

private noncomputable def leaf4174Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435733/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357459968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (550976397/536870912) }, upper := { exponent := 1, mantissa := (4273/4096) } }, logOuter := sk107LogOuterCertificate, logK := sk107LogKCertificate, logChi := chi260LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716182527/68714919936) } }, logDArg := sk107LogDArgCertificate }

private noncomputable def leaf4174InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf4174LocalValidity :
    LeafFacts leaf4174Box leaf4174Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4174Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357459968) }) = true
      norm_num [leaf4174Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4174CertificateValid :
    WideCertificateValid leaf4174Box leaf4174Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk107ValidityFacts chi260ValidityFacts
    leaf4174LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4174CoverageChecked :
    coverageCheck (innerAD leaf4174Box) leaf4174InnerLog = true := by
  rfl'

private theorem leaf4174InnerLogValid :
    leaf4174InnerLog.Valid 8 (innerAD leaf4174Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf4174CoverageChecked

private noncomputable def leaf4174InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629389/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4174InputLogOnePlusV_eq :
    leaf4174InputLogOnePlusV = outerEnclosure 24
      (leaf4174Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4174RoundedFacts : LeafRoundedFacts 8
    leaf4174Certificate.logOnePlusV leaf4174InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4174InputLogOnePlusV_eq }

private noncomputable def leaf4174Inputs : Inputs :=
  inputsOfCaches globalInput sk107RoundedInputs
    chi260InputQChi innerPair117Input
    leaf4174InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4174LowerChecked :
    lowerCheck 24 leaf4174Box leaf4174Inputs = true := by
  rfl'

private theorem leaf4174CoversExact : CoversExact 8
    leaf4174Box leaf4174Certificate leaf4174InnerLog leaf4174Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk107RoundedFacts chi260RoundedFacts
    innerPair117RoundedFacts leaf4174RoundedFacts (by rfl)

private theorem leaf4174FlatSound : Sound leaf4174Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4174CertificateValid
    leaf4174InnerLogValid leaf4174CoversExact leaf4174LowerChecked

private noncomputable def leaf4175Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (49/128), chiHi := (25/64) }

private noncomputable def leaf4175Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435735/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357434368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (554187463/536870912) }, upper := { exponent := 1, mantissa := (2149/2048) } }, logOuter := sk108LogOuterCertificate, logK := sk108LogKCertificate, logChi := chi260LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716156927/68714868736) } }, logDArg := sk108LogDArgCertificate }

private noncomputable def leaf4175InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4175LocalValidity :
    LeafFacts leaf4175Box leaf4175Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4175Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357434368) }) = true
      norm_num [leaf4175Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4175CertificateValid :
    WideCertificateValid leaf4175Box leaf4175Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk108ValidityFacts chi260ValidityFacts
    leaf4175LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4175CoverageChecked :
    coverageCheck (innerAD leaf4175Box) leaf4175InnerLog = true := by
  rfl'

private theorem leaf4175InnerLogValid :
    leaf4175InnerLog.Valid 8 (innerAD leaf4175Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4175CoverageChecked

private noncomputable def leaf4175InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629395/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4175InputLogOnePlusV_eq :
    leaf4175InputLogOnePlusV = outerEnclosure 24
      (leaf4175Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4175RoundedFacts : LeafRoundedFacts 8
    leaf4175Certificate.logOnePlusV leaf4175InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4175InputLogOnePlusV_eq }

private noncomputable def leaf4175Inputs : Inputs :=
  inputsOfCaches globalInput sk108RoundedInputs
    chi260InputQChi innerPair242Input
    leaf4175InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4175LowerChecked :
    lowerCheck 24 leaf4175Box leaf4175Inputs = true := by
  rfl'

private theorem leaf4175CoversExact : CoversExact 8
    leaf4175Box leaf4175Certificate leaf4175InnerLog leaf4175Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk108RoundedFacts chi260RoundedFacts
    innerPair242RoundedFacts leaf4175RoundedFacts (by rfl)

private theorem leaf4175FlatSound : Sound leaf4175Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4175CertificateValid
    leaf4175InnerLogValid leaf4175CoversExact leaf4175LowerChecked

private noncomputable def leaf4176Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (25/64), chiHi := (51/128) }

private noncomputable def leaf4176Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435735/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357414400) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (556743211/536870912) }, upper := { exponent := 1, mantissa := (8635/8192) } }, logOuter := sk107LogOuterCertificate, logK := sk107LogKCertificate, logChi := chi261LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716136959/68714828800) } }, logDArg := sk107LogDArgCertificate }

private noncomputable def leaf4176InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4176LocalValidity :
    LeafFacts leaf4176Box leaf4176Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4176Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357414400) }) = true
      norm_num [leaf4176Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4176CertificateValid :
    WideCertificateValid leaf4176Box leaf4176Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk107ValidityFacts chi261ValidityFacts
    leaf4176LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4176CoverageChecked :
    coverageCheck (innerAD leaf4176Box) leaf4176InnerLog = true := by
  rfl'

private theorem leaf4176InnerLogValid :
    leaf4176InnerLog.Valid 8 (innerAD leaf4176Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4176CoverageChecked

private noncomputable def leaf4176InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453675/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf4176InputLogOnePlusV_eq :
    leaf4176InputLogOnePlusV = outerEnclosure 24
      (leaf4176Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4176RoundedFacts : LeafRoundedFacts 8
    leaf4176Certificate.logOnePlusV leaf4176InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4176InputLogOnePlusV_eq }

private noncomputable def leaf4176Inputs : Inputs :=
  inputsOfCaches globalInput sk107RoundedInputs
    chi261InputQChi innerPair242Input
    leaf4176InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4176LowerChecked :
    lowerCheck 24 leaf4176Box leaf4176Inputs = true := by
  rfl'

private theorem leaf4176CoversExact : CoversExact 8
    leaf4176Box leaf4176Certificate leaf4176InnerLog leaf4176Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk107RoundedFacts chi261RoundedFacts
    innerPair242RoundedFacts leaf4176RoundedFacts (by rfl)

private theorem leaf4176FlatSound : Sound leaf4176Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4176CertificateValid
    leaf4176InnerLogValid leaf4176CoversExact leaf4176LowerChecked

private noncomputable def leaf4177Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (25/64), chiHi := (51/128) }

private noncomputable def leaf4177Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435737/268435456) }, vSqrt := { lower := (32765/32768), upper := (1108345889/1108302848) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (560019809/536870912) }, upper := { exponent := 1, mantissa := (4343/4096) } }, logOuter := sk108LogOuterCertificate, logK := sk108LogKCertificate, logChi := chi261LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (2216648737/2216605696) } }, logDArg := sk108LogDArgCertificate }

private noncomputable def leaf4177InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4177LocalValidity :
    LeafFacts leaf4177Box leaf4177Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4177Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (1108345889/1108302848) }) = true
      norm_num [leaf4177Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4177CertificateValid :
    WideCertificateValid leaf4177Box leaf4177Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk108ValidityFacts chi261ValidityFacts
    leaf4177LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4177CoverageChecked :
    coverageCheck (innerAD leaf4177Box) leaf4177InnerLog = true := by
  rfl'

private theorem leaf4177InnerLogValid :
    leaf4177InnerLog.Valid 8 (innerAD leaf4177Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4177CoverageChecked

private noncomputable def leaf4177InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629407/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4177InputLogOnePlusV_eq :
    leaf4177InputLogOnePlusV = outerEnclosure 24
      (leaf4177Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4177RoundedFacts : LeafRoundedFacts 8
    leaf4177Certificate.logOnePlusV leaf4177InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4177InputLogOnePlusV_eq }

private noncomputable def leaf4177Inputs : Inputs :=
  inputsOfCaches globalInput sk108RoundedInputs
    chi261InputQChi innerPair242Input
    leaf4177InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4177LowerChecked :
    lowerCheck 24 leaf4177Box leaf4177Inputs = true := by
  rfl'

private theorem leaf4177CoversExact : CoversExact 8
    leaf4177Box leaf4177Certificate leaf4177InnerLog leaf4177Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk108RoundedFacts chi261RoundedFacts
    innerPair242RoundedFacts leaf4177RoundedFacts (by rfl)

private theorem leaf4177FlatSound : Sound leaf4177Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4177CertificateValid
    leaf4177InnerLogValid leaf4177CoversExact leaf4177LowerChecked

private noncomputable def leaf4178Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (51/128), chiHi := (13/32) }

private noncomputable def leaf4178Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435737/268435456) }, vSqrt := { lower := (32765/32768), upper := (2021101327/2021021696) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (562510025/536870912) }, upper := { exponent := 1, mantissa := (2181/2048) } }, logOuter := sk107LogOuterCertificate, logK := sk107LogKCertificate, logChi := chi262LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (4042123023/4042043392) } }, logDArg := sk107LogDArgCertificate }

private noncomputable def leaf4178InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf4178LocalValidity :
    LeafFacts leaf4178Box leaf4178Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4178Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (2021101327/2021021696) }) = true
      norm_num [leaf4178Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4178CertificateValid :
    WideCertificateValid leaf4178Box leaf4178Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk107ValidityFacts chi262ValidityFacts
    leaf4178LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4178CoverageChecked :
    coverageCheck (innerAD leaf4178Box) leaf4178InnerLog = true := by
  rfl'

private theorem leaf4178InnerLogValid :
    leaf4178InnerLog.Valid 8 (innerAD leaf4178Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf4178CoverageChecked

private noncomputable def leaf4178InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629411/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4178InputLogOnePlusV_eq :
    leaf4178InputLogOnePlusV = outerEnclosure 24
      (leaf4178Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4178RoundedFacts : LeafRoundedFacts 8
    leaf4178Certificate.logOnePlusV leaf4178InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4178InputLogOnePlusV_eq }

private noncomputable def leaf4178Inputs : Inputs :=
  inputsOfCaches globalInput sk107RoundedInputs
    chi262InputQChi innerPair243Input
    leaf4178InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4178LowerChecked :
    lowerCheck 24 leaf4178Box leaf4178Inputs = true := by
  rfl'

private theorem leaf4178CoversExact : CoversExact 8
    leaf4178Box leaf4178Certificate leaf4178InnerLog leaf4178Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk107RoundedFacts chi262RoundedFacts
    innerPair243RoundedFacts leaf4178RoundedFacts (by rfl)

private theorem leaf4178FlatSound : Sound leaf4178Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4178CertificateValid
    leaf4178InnerLogValid leaf4178CoversExact leaf4178LowerChecked

private noncomputable def leaf4179Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (51/128), chiHi := (13/32) }

private noncomputable def leaf4179Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435739/268435456) }, vSqrt := { lower := (32765/32768), upper := (4908388937/4908191744) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (565852155/536870912) }, upper := { exponent := 1, mantissa := (1097/1024) } }, logOuter := sk108LogOuterCertificate, logK := sk108LogKCertificate, logChi := chi262LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (9816580681/9816383488) } }, logDArg := sk108LogDArgCertificate }

private noncomputable def leaf4179InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf4179LocalValidity :
    LeafFacts leaf4179Box leaf4179Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4179Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4908388937/4908191744) }) = true
      norm_num [leaf4179Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4179CertificateValid :
    WideCertificateValid leaf4179Box leaf4179Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk108ValidityFacts chi262ValidityFacts
    leaf4179LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4179CoverageChecked :
    coverageCheck (innerAD leaf4179Box) leaf4179InnerLog = true := by
  rfl'

private theorem leaf4179InnerLogValid :
    leaf4179InnerLog.Valid 8 (innerAD leaf4179Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf4179CoverageChecked

private noncomputable def leaf4179InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814709/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4179InputLogOnePlusV_eq :
    leaf4179InputLogOnePlusV = outerEnclosure 24
      (leaf4179Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4179RoundedFacts : LeafRoundedFacts 8
    leaf4179Certificate.logOnePlusV leaf4179InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4179InputLogOnePlusV_eq }

private noncomputable def leaf4179Inputs : Inputs :=
  inputsOfCaches globalInput sk108RoundedInputs
    chi262InputQChi innerPair243Input
    leaf4179InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4179LowerChecked :
    lowerCheck 24 leaf4179Box leaf4179Inputs = true := by
  rfl'

private theorem leaf4179CoversExact : CoversExact 8
    leaf4179Box leaf4179Certificate leaf4179InnerLog leaf4179Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk108RoundedFacts chi262RoundedFacts
    innerPair243RoundedFacts leaf4179RoundedFacts (by rfl)

private theorem leaf4179FlatSound : Sound leaf4179Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4179CertificateValid
    leaf4179InnerLogValid leaf4179CoversExact leaf4179LowerChecked

private noncomputable def leaf4180Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32), chiLo := (3/8), chiHi := (49/128) }

private noncomputable def leaf4180Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435735/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357455360) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (551500651/536870912) }, upper := { exponent := 1, mantissa := (8555/8192) } }, logOuter := sk109LogOuterCertificate, logK := sk109LogKCertificate, logChi := chi259LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716177919/68714910720) } }, logDArg := sk109LogDArgCertificate }

private noncomputable def leaf4180InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf4180LocalValidity :
    LeafFacts leaf4180Box leaf4180Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4180Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357455360) }) = true
      norm_num [leaf4180Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4180CertificateValid :
    WideCertificateValid leaf4180Box leaf4180Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk109ValidityFacts chi259ValidityFacts
    leaf4180LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4180CoverageChecked :
    coverageCheck (innerAD leaf4180Box) leaf4180InnerLog = true := by
  rfl'

private theorem leaf4180InnerLogValid :
    leaf4180InnerLog.Valid 8 (innerAD leaf4180Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf4180CoverageChecked

private noncomputable def leaf4180InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814695/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4180InputLogOnePlusV_eq :
    leaf4180InputLogOnePlusV = outerEnclosure 24
      (leaf4180Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4180RoundedFacts : LeafRoundedFacts 8
    leaf4180Certificate.logOnePlusV leaf4180InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4180InputLogOnePlusV_eq }

private noncomputable def leaf4180Inputs : Inputs :=
  inputsOfCaches globalInput sk109RoundedInputs
    chi259InputQChi innerPair117Input
    leaf4180InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4180LowerChecked :
    lowerCheck 24 leaf4180Box leaf4180Inputs = true := by
  rfl'

private theorem leaf4180CoversExact : CoversExact 8
    leaf4180Box leaf4180Certificate leaf4180InnerLog leaf4180Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk109RoundedFacts chi259RoundedFacts
    innerPair117RoundedFacts leaf4180RoundedFacts (by rfl)

private theorem leaf4180FlatSound : Sound leaf4180Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4180CertificateValid
    leaf4180InnerLogValid leaf4180CoversExact leaf4180LowerChecked

private noncomputable def leaf4181Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8), chiLo := (3/8), chiHi := (49/128) }

private noncomputable def leaf4181Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435737/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357430272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (554646185/536870912) }, upper := { exponent := 1, mantissa := (2151/2048) } }, logOuter := sk110LogOuterCertificate, logK := sk110LogKCertificate, logChi := chi259LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716152831/68714860544) } }, logDArg := sk110LogDArgCertificate }

private noncomputable def leaf4181InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4181LocalValidity :
    LeafFacts leaf4181Box leaf4181Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4181Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357430272) }) = true
      norm_num [leaf4181Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4181CertificateValid :
    WideCertificateValid leaf4181Box leaf4181Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk110ValidityFacts chi259ValidityFacts
    leaf4181LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4181CoverageChecked :
    coverageCheck (innerAD leaf4181Box) leaf4181InnerLog = true := by
  rfl'

private theorem leaf4181InnerLogValid :
    leaf4181InnerLog.Valid 8 (innerAD leaf4181Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4181CoverageChecked

private noncomputable def leaf4181InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907349/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4181InputLogOnePlusV_eq :
    leaf4181InputLogOnePlusV = outerEnclosure 24
      (leaf4181Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4181RoundedFacts : LeafRoundedFacts 8
    leaf4181Certificate.logOnePlusV leaf4181InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4181InputLogOnePlusV_eq }

private noncomputable def leaf4181Inputs : Inputs :=
  inputsOfCaches globalInput sk110RoundedInputs
    chi259InputQChi innerPair242Input
    leaf4181InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4181LowerChecked :
    lowerCheck 24 leaf4181Box leaf4181Inputs = true := by
  rfl'

private theorem leaf4181CoversExact : CoversExact 8
    leaf4181Box leaf4181Certificate leaf4181InnerLog leaf4181Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk110RoundedFacts chi259RoundedFacts
    innerPair242RoundedFacts leaf4181RoundedFacts (by rfl)

private theorem leaf4181FlatSound : Sound leaf4181Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4181CertificateValid
    leaf4181InnerLogValid leaf4181CoversExact leaf4181LowerChecked

private noncomputable def leaf4182Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32), chiLo := (49/128), chiHi := (25/64) }

private noncomputable def leaf4182Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435737/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357408768) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (557398529/536870912) }, upper := { exponent := 1, mantissa := (4323/4096) } }, logOuter := sk109LogOuterCertificate, logK := sk109LogKCertificate, logChi := chi260LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716131327/68714817536) } }, logDArg := sk109LogDArgCertificate }

private noncomputable def leaf4182InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4182LocalValidity :
    LeafFacts leaf4182Box leaf4182Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4182Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357408768) }) = true
      norm_num [leaf4182Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4182CertificateValid :
    WideCertificateValid leaf4182Box leaf4182Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk109ValidityFacts chi260ValidityFacts
    leaf4182LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4182CoverageChecked :
    coverageCheck (innerAD leaf4182Box) leaf4182InnerLog = true := by
  rfl'

private theorem leaf4182InnerLogValid :
    leaf4182InnerLog.Valid 8 (innerAD leaf4182Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4182CoverageChecked

private noncomputable def leaf4182InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814701/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4182InputLogOnePlusV_eq :
    leaf4182InputLogOnePlusV = outerEnclosure 24
      (leaf4182Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4182RoundedFacts : LeafRoundedFacts 8
    leaf4182Certificate.logOnePlusV leaf4182InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4182InputLogOnePlusV_eq }

private noncomputable def leaf4182Inputs : Inputs :=
  inputsOfCaches globalInput sk109RoundedInputs
    chi260InputQChi innerPair242Input
    leaf4182InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4182LowerChecked :
    lowerCheck 24 leaf4182Box leaf4182Inputs = true := by
  rfl'

private theorem leaf4182CoversExact : CoversExact 8
    leaf4182Box leaf4182Certificate leaf4182InnerLog leaf4182Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk109RoundedFacts chi260RoundedFacts
    innerPair242RoundedFacts leaf4182RoundedFacts (by rfl)

private theorem leaf4182FlatSound : Sound leaf4182Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4182CertificateValid
    leaf4182InnerLogValid leaf4182CoversExact leaf4182LowerChecked

private noncomputable def leaf4183Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8), chiLo := (49/128), chiHi := (25/64) }

private noncomputable def leaf4183Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435739/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357383168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (560609595/536870912) }, upper := { exponent := 1, mantissa := (1087/1024) } }, logOuter := sk110LogOuterCertificate, logK := sk110LogKCertificate, logChi := chi260LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716105727/68714766336) } }, logDArg := sk110LogDArgCertificate }

private noncomputable def leaf4183InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4183LocalValidity :
    LeafFacts leaf4183Box leaf4183Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4183Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357383168) }) = true
      norm_num [leaf4183Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4183CertificateValid :
    WideCertificateValid leaf4183Box leaf4183Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk110ValidityFacts chi260ValidityFacts
    leaf4183LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4183CoverageChecked :
    coverageCheck (innerAD leaf4183Box) leaf4183InnerLog = true := by
  rfl'

private theorem leaf4183InnerLogValid :
    leaf4183InnerLog.Valid 8 (innerAD leaf4183Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4183CoverageChecked

private noncomputable def leaf4183InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (363419/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf4183InputLogOnePlusV_eq :
    leaf4183InputLogOnePlusV = outerEnclosure 24
      (leaf4183Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4183RoundedFacts : LeafRoundedFacts 8
    leaf4183Certificate.logOnePlusV leaf4183InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4183InputLogOnePlusV_eq }

private noncomputable def leaf4183Inputs : Inputs :=
  inputsOfCaches globalInput sk110RoundedInputs
    chi260InputQChi innerPair242Input
    leaf4183InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4183LowerChecked :
    lowerCheck 24 leaf4183Box leaf4183Inputs = true := by
  rfl'

private theorem leaf4183CoversExact : CoversExact 8
    leaf4183Box leaf4183Certificate leaf4183InnerLog leaf4183Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk110RoundedFacts chi260RoundedFacts
    innerPair242RoundedFacts leaf4183RoundedFacts (by rfl)

private theorem leaf4183FlatSound : Sound leaf4183Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4183CertificateValid
    leaf4183InnerLogValid leaf4183CoversExact leaf4183LowerChecked

private noncomputable def leaf4184Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32), chiLo := (25/64), chiHi := (51/128) }

private noncomputable def leaf4184Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435739/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357362176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (563296407/536870912) }, upper := { exponent := 1, mantissa := (8737/8192) } }, logOuter := sk109LogOuterCertificate, logK := sk109LogKCertificate, logChi := chi261LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716084735/68714724352) } }, logDArg := sk109LogDArgCertificate }

private noncomputable def leaf4184InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf4184LocalValidity :
    LeafFacts leaf4184Box leaf4184Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4184Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357362176) }) = true
      norm_num [leaf4184Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4184CertificateValid :
    WideCertificateValid leaf4184Box leaf4184Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk109ValidityFacts chi261ValidityFacts
    leaf4184LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4184CoverageChecked :
    coverageCheck (innerAD leaf4184Box) leaf4184InnerLog = true := by
  rfl'

private theorem leaf4184InnerLogValid :
    leaf4184InnerLog.Valid 8 (innerAD leaf4184Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf4184CoverageChecked

private noncomputable def leaf4184InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629413/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4184InputLogOnePlusV_eq :
    leaf4184InputLogOnePlusV = outerEnclosure 24
      (leaf4184Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4184RoundedFacts : LeafRoundedFacts 8
    leaf4184Certificate.logOnePlusV leaf4184InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4184InputLogOnePlusV_eq }

private noncomputable def leaf4184Inputs : Inputs :=
  inputsOfCaches globalInput sk109RoundedInputs
    chi261InputQChi innerPair243Input
    leaf4184InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4184LowerChecked :
    lowerCheck 24 leaf4184Box leaf4184Inputs = true := by
  rfl'

private theorem leaf4184CoversExact : CoversExact 8
    leaf4184Box leaf4184Certificate leaf4184InnerLog leaf4184Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk109RoundedFacts chi261RoundedFacts
    innerPair243RoundedFacts leaf4184RoundedFacts (by rfl)

private theorem leaf4184FlatSound : Sound leaf4184Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4184CertificateValid
    leaf4184InnerLogValid leaf4184CoversExact leaf4184LowerChecked

private noncomputable def leaf4185Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8), chiLo := (25/64), chiHi := (51/128) }

private noncomputable def leaf4185Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435741/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357336064) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (566573005/536870912) }, upper := { exponent := 1, mantissa := (2197/2048) } }, logOuter := sk110LogOuterCertificate, logK := sk110LogKCertificate, logChi := chi261LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716058623/68714672128) } }, logDArg := sk110LogDArgCertificate }

private noncomputable def leaf4185InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf4185LocalValidity :
    LeafFacts leaf4185Box leaf4185Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4185Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357336064) }) = true
      norm_num [leaf4185Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4185CertificateValid :
    WideCertificateValid leaf4185Box leaf4185Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk110ValidityFacts chi261ValidityFacts
    leaf4185LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4185CoverageChecked :
    coverageCheck (innerAD leaf4185Box) leaf4185InnerLog = true := by
  rfl'

private theorem leaf4185InnerLogValid :
    leaf4185InnerLog.Valid 8 (innerAD leaf4185Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf4185CoverageChecked

private noncomputable def leaf4185InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629419/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4185InputLogOnePlusV_eq :
    leaf4185InputLogOnePlusV = outerEnclosure 24
      (leaf4185Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4185RoundedFacts : LeafRoundedFacts 8
    leaf4185Certificate.logOnePlusV leaf4185InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4185InputLogOnePlusV_eq }

private noncomputable def leaf4185Inputs : Inputs :=
  inputsOfCaches globalInput sk110RoundedInputs
    chi261InputQChi innerPair243Input
    leaf4185InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4185LowerChecked :
    lowerCheck 24 leaf4185Box leaf4185Inputs = true := by
  rfl'

private theorem leaf4185CoversExact : CoversExact 8
    leaf4185Box leaf4185Certificate leaf4185InnerLog leaf4185Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk110RoundedFacts chi261RoundedFacts
    innerPair243RoundedFacts leaf4185RoundedFacts (by rfl)

private theorem leaf4185FlatSound : Sound leaf4185Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4185CertificateValid
    leaf4185InnerLogValid leaf4185CoversExact leaf4185LowerChecked

private noncomputable def leaf4186Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32), chiLo := (51/128), chiHi := (13/32) }

private noncomputable def leaf4186Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435741/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357315584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (569194285/536870912) }, upper := { exponent := 1, mantissa := (2207/2048) } }, logOuter := sk109LogOuterCertificate, logK := sk109LogKCertificate, logChi := chi262LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716038143/68714631168) } }, logDArg := sk109LogDArgCertificate }

private noncomputable def leaf4186InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf4186LocalValidity :
    LeafFacts leaf4186Box leaf4186Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4186Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357315584) }) = true
      norm_num [leaf4186Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4186CertificateValid :
    WideCertificateValid leaf4186Box leaf4186Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk109ValidityFacts chi262ValidityFacts
    leaf4186LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4186CoverageChecked :
    coverageCheck (innerAD leaf4186Box) leaf4186InnerLog = true := by
  rfl'

private theorem leaf4186InnerLogValid :
    leaf4186InnerLog.Valid 8 (innerAD leaf4186Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf4186CoverageChecked

private noncomputable def leaf4186InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (726839/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf4186InputLogOnePlusV_eq :
    leaf4186InputLogOnePlusV = outerEnclosure 24
      (leaf4186Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4186RoundedFacts : LeafRoundedFacts 8
    leaf4186Certificate.logOnePlusV leaf4186InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4186InputLogOnePlusV_eq }

private noncomputable def leaf4186Inputs : Inputs :=
  inputsOfCaches globalInput sk109RoundedInputs
    chi262InputQChi innerPair243Input
    leaf4186InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4186LowerChecked :
    lowerCheck 24 leaf4186Box leaf4186Inputs = true := by
  rfl'

private theorem leaf4186CoversExact : CoversExact 8
    leaf4186Box leaf4186Certificate leaf4186InnerLog leaf4186Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk109RoundedFacts chi262RoundedFacts
    innerPair243RoundedFacts leaf4186RoundedFacts (by rfl)

private theorem leaf4186FlatSound : Sound leaf4186Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4186CertificateValid
    leaf4186InnerLogValid leaf4186CoversExact leaf4186LowerChecked

private noncomputable def leaf4187Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8), chiLo := (51/128), chiHi := (13/32) }

private noncomputable def leaf4187Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435743/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357288960) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (572536415/536870912) }, upper := { exponent := 1, mantissa := (555/512) } }, logOuter := sk110LogOuterCertificate, logK := sk110LogKCertificate, logChi := chi262LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716011519/68714577920) } }, logDArg := sk110LogDArgCertificate }

private noncomputable def leaf4187InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf4187LocalValidity :
    LeafFacts leaf4187Box leaf4187Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4187Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357288960) }) = true
      norm_num [leaf4187Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4187CertificateValid :
    WideCertificateValid leaf4187Box leaf4187Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk110ValidityFacts chi262ValidityFacts
    leaf4187LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4187CoverageChecked :
    coverageCheck (innerAD leaf4187Box) leaf4187InnerLog = true := by
  rfl'

private theorem leaf4187InnerLogValid :
    leaf4187InnerLog.Valid 8 (innerAD leaf4187Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf4187CoverageChecked

private noncomputable def leaf4187InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629431/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4187InputLogOnePlusV_eq :
    leaf4187InputLogOnePlusV = outerEnclosure 24
      (leaf4187Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4187RoundedFacts : LeafRoundedFacts 8
    leaf4187Certificate.logOnePlusV leaf4187InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4187InputLogOnePlusV_eq }

private noncomputable def leaf4187Inputs : Inputs :=
  inputsOfCaches globalInput sk110RoundedInputs
    chi262InputQChi innerPair249Input
    leaf4187InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4187LowerChecked :
    lowerCheck 24 leaf4187Box leaf4187Inputs = true := by
  rfl'

private theorem leaf4187CoversExact : CoversExact 8
    leaf4187Box leaf4187Certificate leaf4187InnerLog leaf4187Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk110RoundedFacts chi262RoundedFacts
    innerPair249RoundedFacts leaf4187RoundedFacts (by rfl)

private theorem leaf4187FlatSound : Sound leaf4187Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4187CertificateValid
    leaf4187InnerLogValid leaf4187CoversExact leaf4187LowerChecked

private noncomputable def leaf4188Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (13/32), chiHi := (53/128) }

private noncomputable def leaf4188Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435739/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357323264) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (568276839/536870912) }, upper := { exponent := 1, mantissa := (8813/8192) } }, logOuter := sk107LogOuterCertificate, logK := sk107LogKCertificate, logChi := chi263LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716045823/68714646528) } }, logDArg := sk107LogDArgCertificate }

private noncomputable def leaf4188InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf4188LocalValidity :
    LeafFacts leaf4188Box leaf4188Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4188Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357323264) }) = true
      norm_num [leaf4188Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4188CertificateValid :
    WideCertificateValid leaf4188Box leaf4188Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk107ValidityFacts chi263ValidityFacts
    leaf4188LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4188CoverageChecked :
    coverageCheck (innerAD leaf4188Box) leaf4188InnerLog = true := by
  rfl'

private theorem leaf4188InnerLogValid :
    leaf4188InnerLog.Valid 8 (innerAD leaf4188Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf4188CoverageChecked

private noncomputable def leaf4188InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814711/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4188InputLogOnePlusV_eq :
    leaf4188InputLogOnePlusV = outerEnclosure 24
      (leaf4188Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4188RoundedFacts : LeafRoundedFacts 8
    leaf4188Certificate.logOnePlusV leaf4188InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4188InputLogOnePlusV_eq }

private noncomputable def leaf4188Inputs : Inputs :=
  inputsOfCaches globalInput sk107RoundedInputs
    chi263InputQChi innerPair243Input
    leaf4188InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4188LowerChecked :
    lowerCheck 24 leaf4188Box leaf4188Inputs = true := by
  rfl'

private theorem leaf4188CoversExact : CoversExact 8
    leaf4188Box leaf4188Certificate leaf4188InnerLog leaf4188Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk107RoundedFacts chi263RoundedFacts
    innerPair243RoundedFacts leaf4188RoundedFacts (by rfl)

private theorem leaf4188FlatSound : Sound leaf4188Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4188CertificateValid
    leaf4188InnerLogValid leaf4188CoversExact leaf4188LowerChecked

private noncomputable def leaf4189Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (13/32), chiHi := (53/128) }

private noncomputable def leaf4189Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435741/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357296128) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (571684501/536870912) }, upper := { exponent := 1, mantissa := (4433/4096) } }, logOuter := sk108LogOuterCertificate, logK := sk108LogKCertificate, logChi := chi263LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716018687/68714592256) } }, logDArg := sk108LogDArgCertificate }

private noncomputable def leaf4189InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf4189LocalValidity :
    LeafFacts leaf4189Box leaf4189Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4189Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357296128) }) = true
      norm_num [leaf4189Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4189CertificateValid :
    WideCertificateValid leaf4189Box leaf4189Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk108ValidityFacts chi263ValidityFacts
    leaf4189LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4189CoverageChecked :
    coverageCheck (innerAD leaf4189Box) leaf4189InnerLog = true := by
  rfl'

private theorem leaf4189InnerLogValid :
    leaf4189InnerLog.Valid 8 (innerAD leaf4189Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf4189CoverageChecked

private noncomputable def leaf4189InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629429/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4189InputLogOnePlusV_eq :
    leaf4189InputLogOnePlusV = outerEnclosure 24
      (leaf4189Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4189RoundedFacts : LeafRoundedFacts 8
    leaf4189Certificate.logOnePlusV leaf4189InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4189InputLogOnePlusV_eq }

private noncomputable def leaf4189Inputs : Inputs :=
  inputsOfCaches globalInput sk108RoundedInputs
    chi263InputQChi innerPair249Input
    leaf4189InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4189LowerChecked :
    lowerCheck 24 leaf4189Box leaf4189Inputs = true := by
  rfl'

private theorem leaf4189CoversExact : CoversExact 8
    leaf4189Box leaf4189Certificate leaf4189InnerLog leaf4189Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk108RoundedFacts chi263RoundedFacts
    innerPair249RoundedFacts leaf4189RoundedFacts (by rfl)

private theorem leaf4189FlatSound : Sound leaf4189Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4189CertificateValid
    leaf4189InnerLogValid leaf4189CoversExact leaf4189LowerChecked

private noncomputable def leaf4190Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (53/128), chiHi := (27/64) }

private noncomputable def leaf4190Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435741/268435456) }, vSqrt := { lower := (32765/32768), upper := (4908388937/4908182528) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (574043653/536870912) }, upper := { exponent := 1, mantissa := (4451/4096) } }, logOuter := sk107LogOuterCertificate, logK := sk107LogKCertificate, logChi := chi264LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (9816571465/9816365056) } }, logDArg := sk107LogDArgCertificate }

private noncomputable def leaf4190InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf4190LocalValidity :
    LeafFacts leaf4190Box leaf4190Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4190Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4908388937/4908182528) }) = true
      norm_num [leaf4190Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4190CertificateValid :
    WideCertificateValid leaf4190Box leaf4190Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk107ValidityFacts chi264ValidityFacts
    leaf4190LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4190CoverageChecked :
    coverageCheck (innerAD leaf4190Box) leaf4190InnerLog = true := by
  rfl'

private theorem leaf4190InnerLogValid :
    leaf4190InnerLog.Valid 8 (innerAD leaf4190Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf4190CoverageChecked

private noncomputable def leaf4190InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814717/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4190InputLogOnePlusV_eq :
    leaf4190InputLogOnePlusV = outerEnclosure 24
      (leaf4190Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4190RoundedFacts : LeafRoundedFacts 8
    leaf4190Certificate.logOnePlusV leaf4190InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4190InputLogOnePlusV_eq }

private noncomputable def leaf4190Inputs : Inputs :=
  inputsOfCaches globalInput sk107RoundedInputs
    chi264InputQChi innerPair249Input
    leaf4190InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4190LowerChecked :
    lowerCheck 24 leaf4190Box leaf4190Inputs = true := by
  rfl'

private theorem leaf4190CoversExact : CoversExact 8
    leaf4190Box leaf4190Certificate leaf4190InnerLog leaf4190Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk107RoundedFacts chi264RoundedFacts
    innerPair249RoundedFacts leaf4190RoundedFacts (by rfl)

private theorem leaf4190FlatSound : Sound leaf4190Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4190CertificateValid
    leaf4190InnerLogValid leaf4190CoversExact leaf4190LowerChecked

private noncomputable def leaf4191Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (53/128), chiHi := (27/64) }

private noncomputable def leaf4191Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435743/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357250048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (577516847/536870912) }, upper := { exponent := 1, mantissa := (2239/2048) } }, logOuter := sk108LogOuterCertificate, logK := sk108LogKCertificate, logChi := chi264LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715972607/68714500096) } }, logDArg := sk108LogDArgCertificate }

private noncomputable def leaf4191InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf4191LocalValidity :
    LeafFacts leaf4191Box leaf4191Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4191Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357250048) }) = true
      norm_num [leaf4191Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4191CertificateValid :
    WideCertificateValid leaf4191Box leaf4191Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk108ValidityFacts chi264ValidityFacts
    leaf4191LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4191CoverageChecked :
    coverageCheck (innerAD leaf4191Box) leaf4191InnerLog = true := by
  rfl'

private theorem leaf4191InnerLogValid :
    leaf4191InnerLog.Valid 8 (innerAD leaf4191Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf4191CoverageChecked

private noncomputable def leaf4191InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (90855/131072) }

set_option maxRecDepth 1000000 in
private theorem leaf4191InputLogOnePlusV_eq :
    leaf4191InputLogOnePlusV = outerEnclosure 24
      (leaf4191Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4191RoundedFacts : LeafRoundedFacts 8
    leaf4191Certificate.logOnePlusV leaf4191InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4191InputLogOnePlusV_eq }

private noncomputable def leaf4191Inputs : Inputs :=
  inputsOfCaches globalInput sk108RoundedInputs
    chi264InputQChi innerPair249Input
    leaf4191InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4191LowerChecked :
    lowerCheck 24 leaf4191Box leaf4191Inputs = true := by
  rfl'

private theorem leaf4191CoversExact : CoversExact 8
    leaf4191Box leaf4191Certificate leaf4191InnerLog leaf4191Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk108RoundedFacts chi264RoundedFacts
    innerPair249RoundedFacts leaf4191RoundedFacts (by rfl)

private theorem leaf4191FlatSound : Sound leaf4191Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4191CertificateValid
    leaf4191InnerLogValid leaf4191CoversExact leaf4191LowerChecked

private noncomputable def leaf4192Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (27/64), chiHi := (55/128) }

private noncomputable def leaf4192Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435743/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357232128) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (579810467/536870912) }, upper := { exponent := 1, mantissa := (8991/8192) } }, logOuter := sk107LogOuterCertificate, logK := sk107LogKCertificate, logChi := chi265LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715954687/68714464256) } }, logDArg := sk107LogDArgCertificate }

private noncomputable def leaf4192InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf4192LocalValidity :
    LeafFacts leaf4192Box leaf4192Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4192Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357232128) }) = true
      norm_num [leaf4192Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4192CertificateValid :
    WideCertificateValid leaf4192Box leaf4192Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk107ValidityFacts chi265ValidityFacts
    leaf4192LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4192CoverageChecked :
    coverageCheck (innerAD leaf4192Box) leaf4192InnerLog = true := by
  rfl'

private theorem leaf4192InnerLogValid :
    leaf4192InnerLog.Valid 8 (innerAD leaf4192Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf4192CoverageChecked

private noncomputable def leaf4192InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629445/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4192InputLogOnePlusV_eq :
    leaf4192InputLogOnePlusV = outerEnclosure 24
      (leaf4192Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4192RoundedFacts : LeafRoundedFacts 8
    leaf4192Certificate.logOnePlusV leaf4192InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4192InputLogOnePlusV_eq }

private noncomputable def leaf4192Inputs : Inputs :=
  inputsOfCaches globalInput sk107RoundedInputs
    chi265InputQChi innerPair250Input
    leaf4192InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4192LowerChecked :
    lowerCheck 24 leaf4192Box leaf4192Inputs = true := by
  rfl'

private theorem leaf4192CoversExact : CoversExact 8
    leaf4192Box leaf4192Certificate leaf4192InnerLog leaf4192Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk107RoundedFacts chi265RoundedFacts
    innerPair250RoundedFacts leaf4192RoundedFacts (by rfl)

private theorem leaf4192FlatSound : Sound leaf4192Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4192CertificateValid
    leaf4192InnerLogValid leaf4192CoversExact leaf4192LowerChecked

private noncomputable def leaf4193Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (27/64), chiHi := (55/128) }

private noncomputable def leaf4193Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435745/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357203968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (583349193/536870912) }, upper := { exponent := 1, mantissa := (4523/4096) } }, logOuter := sk108LogOuterCertificate, logK := sk108LogKCertificate, logChi := chi265LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715926527/68714407936) } }, logDArg := sk108LogDArgCertificate }

private noncomputable def leaf4193InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf4193LocalValidity :
    LeafFacts leaf4193Box leaf4193Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4193Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357203968) }) = true
      norm_num [leaf4193Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4193CertificateValid :
    WideCertificateValid leaf4193Box leaf4193Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk108ValidityFacts chi265ValidityFacts
    leaf4193LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4193CoverageChecked :
    coverageCheck (innerAD leaf4193Box) leaf4193InnerLog = true := by
  rfl'

private theorem leaf4193InnerLogValid :
    leaf4193InnerLog.Valid 8 (innerAD leaf4193Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf4193CoverageChecked

private noncomputable def leaf4193InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907363/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4193InputLogOnePlusV_eq :
    leaf4193InputLogOnePlusV = outerEnclosure 24
      (leaf4193Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4193RoundedFacts : LeafRoundedFacts 8
    leaf4193Certificate.logOnePlusV leaf4193InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4193InputLogOnePlusV_eq }

private noncomputable def leaf4193Inputs : Inputs :=
  inputsOfCaches globalInput sk108RoundedInputs
    chi265InputQChi innerPair250Input
    leaf4193InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4193LowerChecked :
    lowerCheck 24 leaf4193Box leaf4193Inputs = true := by
  rfl'

private theorem leaf4193CoversExact : CoversExact 8
    leaf4193Box leaf4193Certificate leaf4193InnerLog leaf4193Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk108RoundedFacts chi265RoundedFacts
    innerPair250RoundedFacts leaf4193RoundedFacts (by rfl)

private theorem leaf4193FlatSound : Sound leaf4193Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4193CertificateValid
    leaf4193InnerLogValid leaf4193CoversExact leaf4193LowerChecked

private noncomputable def leaf4194Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (55/128), chiHi := (7/16) }

private noncomputable def leaf4194Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435745/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357186560) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (585577281/536870912) }, upper := { exponent := 1, mantissa := (1135/1024) } }, logOuter := sk107LogOuterCertificate, logK := sk107LogKCertificate, logChi := chi266LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715909119/68714373120) } }, logDArg := sk107LogDArgCertificate }

private noncomputable def leaf4194InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf4194LocalValidity :
    LeafFacts leaf4194Box leaf4194Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4194Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357186560) }) = true
      norm_num [leaf4194Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4194CertificateValid :
    WideCertificateValid leaf4194Box leaf4194Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk107ValidityFacts chi266ValidityFacts
    leaf4194LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4194CoverageChecked :
    coverageCheck (innerAD leaf4194Box) leaf4194InnerLog = true := by
  rfl'

private theorem leaf4194InnerLogValid :
    leaf4194InnerLog.Valid 8 (innerAD leaf4194Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf4194CoverageChecked

private noncomputable def leaf4194InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (726841/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf4194InputLogOnePlusV_eq :
    leaf4194InputLogOnePlusV = outerEnclosure 24
      (leaf4194Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4194RoundedFacts : LeafRoundedFacts 8
    leaf4194Certificate.logOnePlusV leaf4194InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4194InputLogOnePlusV_eq }

private noncomputable def leaf4194Inputs : Inputs :=
  inputsOfCaches globalInput sk107RoundedInputs
    chi266InputQChi innerPair250Input
    leaf4194InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4194LowerChecked :
    lowerCheck 24 leaf4194Box leaf4194Inputs = true := by
  rfl'

private theorem leaf4194CoversExact : CoversExact 8
    leaf4194Box leaf4194Certificate leaf4194InnerLog leaf4194Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk107RoundedFacts chi266RoundedFacts
    innerPair250RoundedFacts leaf4194RoundedFacts (by rfl)

private theorem leaf4194FlatSound : Sound leaf4194Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4194CertificateValid
    leaf4194InnerLogValid leaf4194CoversExact leaf4194LowerChecked

private noncomputable def leaf4195Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (55/128), chiHi := (7/16) }

private noncomputable def leaf4195Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435747/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357157888) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (589181539/536870912) }, upper := { exponent := 1, mantissa := (571/512) } }, logOuter := sk108LogOuterCertificate, logK := sk108LogKCertificate, logChi := chi266LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715880447/68714315776) } }, logDArg := sk108LogDArgCertificate }

private noncomputable def leaf4195InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf4195LocalValidity :
    LeafFacts leaf4195Box leaf4195Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4195Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357157888) }) = true
      norm_num [leaf4195Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4195CertificateValid :
    WideCertificateValid leaf4195Box leaf4195Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk108ValidityFacts chi266ValidityFacts
    leaf4195LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4195CoverageChecked :
    coverageCheck (innerAD leaf4195Box) leaf4195InnerLog = true := by
  rfl'

private theorem leaf4195InnerLogValid :
    leaf4195InnerLog.Valid 8 (innerAD leaf4195Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf4195CoverageChecked

private noncomputable def leaf4195InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629463/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4195InputLogOnePlusV_eq :
    leaf4195InputLogOnePlusV = outerEnclosure 24
      (leaf4195Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4195RoundedFacts : LeafRoundedFacts 8
    leaf4195Certificate.logOnePlusV leaf4195InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4195InputLogOnePlusV_eq }

private noncomputable def leaf4195Inputs : Inputs :=
  inputsOfCaches globalInput sk108RoundedInputs
    chi266InputQChi innerPair256Input
    leaf4195InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4195LowerChecked :
    lowerCheck 24 leaf4195Box leaf4195Inputs = true := by
  rfl'

private theorem leaf4195CoversExact : CoversExact 8
    leaf4195Box leaf4195Certificate leaf4195InnerLog leaf4195Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk108RoundedFacts chi266RoundedFacts
    innerPair256RoundedFacts leaf4195RoundedFacts (by rfl)

private theorem leaf4195FlatSound : Sound leaf4195Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4195CertificateValid
    leaf4195InnerLogValid leaf4195CoversExact leaf4195LowerChecked

private noncomputable def leaf4196Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32), chiLo := (13/32), chiHi := (53/128) }

private noncomputable def leaf4196Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435743/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357268992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (575092163/536870912) }, upper := { exponent := 1, mantissa := (8919/8192) } }, logOuter := sk109LogOuterCertificate, logK := sk109LogKCertificate, logChi := chi263LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715991551/68714537984) } }, logDArg := sk109LogDArgCertificate }

private noncomputable def leaf4196InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf4196LocalValidity :
    LeafFacts leaf4196Box leaf4196Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4196Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357268992) }) = true
      norm_num [leaf4196Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4196CertificateValid :
    WideCertificateValid leaf4196Box leaf4196Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk109ValidityFacts chi263ValidityFacts
    leaf4196LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4196CoverageChecked :
    coverageCheck (innerAD leaf4196Box) leaf4196InnerLog = true := by
  rfl'

private theorem leaf4196InnerLogValid :
    leaf4196InnerLog.Valid 8 (innerAD leaf4196Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf4196CoverageChecked

private noncomputable def leaf4196InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907359/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4196InputLogOnePlusV_eq :
    leaf4196InputLogOnePlusV = outerEnclosure 24
      (leaf4196Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4196RoundedFacts : LeafRoundedFacts 8
    leaf4196Certificate.logOnePlusV leaf4196InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4196InputLogOnePlusV_eq }

private noncomputable def leaf4196Inputs : Inputs :=
  inputsOfCaches globalInput sk109RoundedInputs
    chi263InputQChi innerPair249Input
    leaf4196InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4196LowerChecked :
    lowerCheck 24 leaf4196Box leaf4196Inputs = true := by
  rfl'

private theorem leaf4196CoversExact : CoversExact 8
    leaf4196Box leaf4196Certificate leaf4196InnerLog leaf4196Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk109RoundedFacts chi263RoundedFacts
    innerPair249RoundedFacts leaf4196RoundedFacts (by rfl)

private theorem leaf4196FlatSound : Sound leaf4196Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4196CertificateValid
    leaf4196InnerLogValid leaf4196CoversExact leaf4196LowerChecked

private noncomputable def leaf4197Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8), chiLo := (13/32), chiHi := (53/128) }

private noncomputable def leaf4197Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435745/268435456) }, vSqrt := { lower := (32765/32768), upper := (4908388937/4908177408) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (578499825/536870912) }, upper := { exponent := 1, mantissa := (2243/2048) } }, logOuter := sk110LogOuterCertificate, logK := sk110LogKCertificate, logChi := chi263LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (9816566345/9816354816) } }, logDArg := sk110LogDArgCertificate }

private noncomputable def leaf4197InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf4197LocalValidity :
    LeafFacts leaf4197Box leaf4197Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4197Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4908388937/4908177408) }) = true
      norm_num [leaf4197Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4197CertificateValid :
    WideCertificateValid leaf4197Box leaf4197Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk110ValidityFacts chi263ValidityFacts
    leaf4197LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4197CoverageChecked :
    coverageCheck (innerAD leaf4197Box) leaf4197InnerLog = true := by
  rfl'

private theorem leaf4197InnerLogValid :
    leaf4197InnerLog.Valid 8 (innerAD leaf4197Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf4197CoverageChecked

private noncomputable def leaf4197InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814721/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4197InputLogOnePlusV_eq :
    leaf4197InputLogOnePlusV = outerEnclosure 24
      (leaf4197Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4197RoundedFacts : LeafRoundedFacts 8
    leaf4197Certificate.logOnePlusV leaf4197InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4197InputLogOnePlusV_eq }

private noncomputable def leaf4197Inputs : Inputs :=
  inputsOfCaches globalInput sk110RoundedInputs
    chi263InputQChi innerPair250Input
    leaf4197InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4197LowerChecked :
    lowerCheck 24 leaf4197Box leaf4197Inputs = true := by
  rfl'

private theorem leaf4197CoversExact : CoversExact 8
    leaf4197Box leaf4197Certificate leaf4197InnerLog leaf4197Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk110RoundedFacts chi263RoundedFacts
    innerPair250RoundedFacts leaf4197RoundedFacts (by rfl)

private theorem leaf4197FlatSound : Sound leaf4197Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4197CertificateValid
    leaf4197InnerLogValid leaf4197CoversExact leaf4197LowerChecked

private noncomputable def leaf4198Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32), chiLo := (53/128), chiHi := (27/64) }

private noncomputable def leaf4198Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435745/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357222400) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (580990041/536870912) }, upper := { exponent := 1, mantissa := (4505/4096) } }, logOuter := sk109LogOuterCertificate, logK := sk109LogKCertificate, logChi := chi264LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715944959/68714444800) } }, logDArg := sk109LogDArgCertificate }

private noncomputable def leaf4198InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf4198LocalValidity :
    LeafFacts leaf4198Box leaf4198Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4198Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357222400) }) = true
      norm_num [leaf4198Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4198CertificateValid :
    WideCertificateValid leaf4198Box leaf4198Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk109ValidityFacts chi264ValidityFacts
    leaf4198LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4198CoverageChecked :
    coverageCheck (innerAD leaf4198Box) leaf4198InnerLog = true := by
  rfl'

private theorem leaf4198InnerLogValid :
    leaf4198InnerLog.Valid 8 (innerAD leaf4198Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf4198CoverageChecked

private noncomputable def leaf4198InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629447/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4198InputLogOnePlusV_eq :
    leaf4198InputLogOnePlusV = outerEnclosure 24
      (leaf4198Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4198RoundedFacts : LeafRoundedFacts 8
    leaf4198Certificate.logOnePlusV leaf4198InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4198InputLogOnePlusV_eq }

private noncomputable def leaf4198Inputs : Inputs :=
  inputsOfCaches globalInput sk109RoundedInputs
    chi264InputQChi innerPair250Input
    leaf4198InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4198LowerChecked :
    lowerCheck 24 leaf4198Box leaf4198Inputs = true := by
  rfl'

private theorem leaf4198CoversExact : CoversExact 8
    leaf4198Box leaf4198Certificate leaf4198InnerLog leaf4198Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk109RoundedFacts chi264RoundedFacts
    innerPair250RoundedFacts leaf4198RoundedFacts (by rfl)

private theorem leaf4198FlatSound : Sound leaf4198Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4198CertificateValid
    leaf4198InnerLogValid leaf4198CoversExact leaf4198LowerChecked

private noncomputable def leaf4199Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8), chiLo := (53/128), chiHi := (27/64) }

private noncomputable def leaf4199Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435747/268435456) }, vSqrt := { lower := (32765/32768), upper := (2021101327/2021011456) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (584463235/536870912) }, upper := { exponent := 1, mantissa := (1133/1024) } }, logOuter := sk110LogOuterCertificate, logK := sk110LogKCertificate, logChi := chi264LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (4042112783/4042022912) } }, logDArg := sk110LogDArgCertificate }

private noncomputable def leaf4199InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf4199LocalValidity :
    LeafFacts leaf4199Box leaf4199Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4199Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (2021101327/2021011456) }) = true
      norm_num [leaf4199Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4199CertificateValid :
    WideCertificateValid leaf4199Box leaf4199Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk110ValidityFacts chi264ValidityFacts
    leaf4199LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4199CoverageChecked :
    coverageCheck (innerAD leaf4199Box) leaf4199InnerLog = true := by
  rfl'

private theorem leaf4199InnerLogValid :
    leaf4199InnerLog.Valid 8 (innerAD leaf4199Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf4199CoverageChecked

private noncomputable def leaf4199InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814727/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4199InputLogOnePlusV_eq :
    leaf4199InputLogOnePlusV = outerEnclosure 24
      (leaf4199Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4199RoundedFacts : LeafRoundedFacts 8
    leaf4199Certificate.logOnePlusV leaf4199InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4199InputLogOnePlusV_eq }

private noncomputable def leaf4199Inputs : Inputs :=
  inputsOfCaches globalInput sk110RoundedInputs
    chi264InputQChi innerPair250Input
    leaf4199InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4199LowerChecked :
    lowerCheck 24 leaf4199Box leaf4199Inputs = true := by
  rfl'

private theorem leaf4199CoversExact : CoversExact 8
    leaf4199Box leaf4199Certificate leaf4199InnerLog leaf4199Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk110RoundedFacts chi264RoundedFacts
    innerPair250RoundedFacts leaf4199RoundedFacts (by rfl)

private theorem leaf4199FlatSound : Sound leaf4199Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4199CertificateValid
    leaf4199InnerLogValid leaf4199CoversExact leaf4199LowerChecked

private noncomputable def leaf4200Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32), chiLo := (27/64), chiHi := (55/128) }

private noncomputable def leaf4200Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435747/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357175808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (586887919/536870912) }, upper := { exponent := 1, mantissa := (9101/8192) } }, logOuter := sk109LogOuterCertificate, logK := sk109LogKCertificate, logChi := chi265LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715898367/68714351616) } }, logDArg := sk109LogDArgCertificate }

private noncomputable def leaf4200InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf4200LocalValidity :
    LeafFacts leaf4200Box leaf4200Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4200Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357175808) }) = true
      norm_num [leaf4200Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4200CertificateValid :
    WideCertificateValid leaf4200Box leaf4200Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk109ValidityFacts chi265ValidityFacts
    leaf4200LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4200CoverageChecked :
    coverageCheck (innerAD leaf4200Box) leaf4200InnerLog = true := by
  rfl'

private theorem leaf4200InnerLogValid :
    leaf4200InnerLog.Valid 8 (innerAD leaf4200Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf4200CoverageChecked

private noncomputable def leaf4200InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814729/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4200InputLogOnePlusV_eq :
    leaf4200InputLogOnePlusV = outerEnclosure 24
      (leaf4200Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4200RoundedFacts : LeafRoundedFacts 8
    leaf4200Certificate.logOnePlusV leaf4200InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4200InputLogOnePlusV_eq }

private noncomputable def leaf4200Inputs : Inputs :=
  inputsOfCaches globalInput sk109RoundedInputs
    chi265InputQChi innerPair250Input
    leaf4200InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4200LowerChecked :
    lowerCheck 24 leaf4200Box leaf4200Inputs = true := by
  rfl'

private theorem leaf4200CoversExact : CoversExact 8
    leaf4200Box leaf4200Certificate leaf4200InnerLog leaf4200Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk109RoundedFacts chi265RoundedFacts
    innerPair250RoundedFacts leaf4200RoundedFacts (by rfl)

private theorem leaf4200FlatSound : Sound leaf4200Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4200CertificateValid
    leaf4200InnerLogValid leaf4200CoversExact leaf4200LowerChecked

private noncomputable def leaf4201Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8), chiLo := (27/64), chiHi := (55/128) }

private noncomputable def leaf4201Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435749/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357147648) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (590426645/536870912) }, upper := { exponent := 1, mantissa := (2289/2048) } }, logOuter := sk110LogOuterCertificate, logK := sk110LogKCertificate, logChi := chi265LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715870207/68714295296) } }, logDArg := sk110LogDArgCertificate }

private noncomputable def leaf4201InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf4201LocalValidity :
    LeafFacts leaf4201Box leaf4201Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4201Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357147648) }) = true
      norm_num [leaf4201Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4201CertificateValid :
    WideCertificateValid leaf4201Box leaf4201Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk110ValidityFacts chi265ValidityFacts
    leaf4201LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4201CoverageChecked :
    coverageCheck (innerAD leaf4201Box) leaf4201InnerLog = true := by
  rfl'

private theorem leaf4201InnerLogValid :
    leaf4201InnerLog.Valid 8 (innerAD leaf4201Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf4201CoverageChecked

private noncomputable def leaf4201InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629465/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4201InputLogOnePlusV_eq :
    leaf4201InputLogOnePlusV = outerEnclosure 24
      (leaf4201Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4201RoundedFacts : LeafRoundedFacts 8
    leaf4201Certificate.logOnePlusV leaf4201InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4201InputLogOnePlusV_eq }

private noncomputable def leaf4201Inputs : Inputs :=
  inputsOfCaches globalInput sk110RoundedInputs
    chi265InputQChi innerPair256Input
    leaf4201InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4201LowerChecked :
    lowerCheck 24 leaf4201Box leaf4201Inputs = true := by
  rfl'

private theorem leaf4201CoversExact : CoversExact 8
    leaf4201Box leaf4201Certificate leaf4201InnerLog leaf4201Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk110RoundedFacts chi265RoundedFacts
    innerPair256RoundedFacts leaf4201RoundedFacts (by rfl)

private theorem leaf4201FlatSound : Sound leaf4201Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4201CertificateValid
    leaf4201InnerLogValid leaf4201CoversExact leaf4201LowerChecked

private noncomputable def leaf4202Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32), chiLo := (55/128), chiHi := (7/16) }

private noncomputable def leaf4202Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435749/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357129216) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (592785797/536870912) }, upper := { exponent := 1, mantissa := (1149/1024) } }, logOuter := sk109LogOuterCertificate, logK := sk109LogKCertificate, logChi := chi266LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715851775/68714258432) } }, logDArg := sk109LogDArgCertificate }

private noncomputable def leaf4202InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf4202LocalValidity :
    LeafFacts leaf4202Box leaf4202Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4202Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357129216) }) = true
      norm_num [leaf4202Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4202CertificateValid :
    WideCertificateValid leaf4202Box leaf4202Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk109ValidityFacts chi266ValidityFacts
    leaf4202LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4202CoverageChecked :
    coverageCheck (innerAD leaf4202Box) leaf4202InnerLog = true := by
  rfl'

private theorem leaf4202InnerLogValid :
    leaf4202InnerLog.Valid 8 (innerAD leaf4202Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf4202CoverageChecked

private noncomputable def leaf4202InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814735/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4202InputLogOnePlusV_eq :
    leaf4202InputLogOnePlusV = outerEnclosure 24
      (leaf4202Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4202RoundedFacts : LeafRoundedFacts 8
    leaf4202Certificate.logOnePlusV leaf4202InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4202InputLogOnePlusV_eq }

private noncomputable def leaf4202Inputs : Inputs :=
  inputsOfCaches globalInput sk109RoundedInputs
    chi266InputQChi innerPair256Input
    leaf4202InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4202LowerChecked :
    lowerCheck 24 leaf4202Box leaf4202Inputs = true := by
  rfl'

private theorem leaf4202CoversExact : CoversExact 8
    leaf4202Box leaf4202Certificate leaf4202InnerLog leaf4202Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk109RoundedFacts chi266RoundedFacts
    innerPair256RoundedFacts leaf4202RoundedFacts (by rfl)

private theorem leaf4202FlatSound : Sound leaf4202Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4202CertificateValid
    leaf4202InnerLogValid leaf4202CoversExact leaf4202LowerChecked

private noncomputable def leaf4203Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8), chiLo := (55/128), chiHi := (7/16) }

private noncomputable def leaf4203Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435751/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357100544) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (596390055/536870912) }, upper := { exponent := 1, mantissa := (289/256) } }, logOuter := sk110LogOuterCertificate, logK := sk110LogKCertificate, logChi := chi266LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715823103/68714201088) } }, logDArg := sk110LogDArgCertificate }

private noncomputable def leaf4203InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf4203LocalValidity :
    LeafFacts leaf4203Box leaf4203Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4203Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357100544) }) = true
      norm_num [leaf4203Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4203CertificateValid :
    WideCertificateValid leaf4203Box leaf4203Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk110ValidityFacts chi266ValidityFacts
    leaf4203LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4203CoverageChecked :
    coverageCheck (innerAD leaf4203Box) leaf4203InnerLog = true := by
  rfl'

private theorem leaf4203InnerLogValid :
    leaf4203InnerLog.Valid 8 (innerAD leaf4203Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf4203CoverageChecked

private noncomputable def leaf4203InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629477/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4203InputLogOnePlusV_eq :
    leaf4203InputLogOnePlusV = outerEnclosure 24
      (leaf4203Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4203RoundedFacts : LeafRoundedFacts 8
    leaf4203Certificate.logOnePlusV leaf4203InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4203InputLogOnePlusV_eq }

private noncomputable def leaf4203Inputs : Inputs :=
  inputsOfCaches globalInput sk110RoundedInputs
    chi266InputQChi innerPair257Input
    leaf4203InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4203LowerChecked :
    lowerCheck 24 leaf4203Box leaf4203Inputs = true := by
  rfl'

private theorem leaf4203CoversExact : CoversExact 8
    leaf4203Box leaf4203Certificate leaf4203InnerLog leaf4203Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk110RoundedFacts chi266RoundedFacts
    innerPair257RoundedFacts leaf4203RoundedFacts (by rfl)

private theorem leaf4203FlatSound : Sound leaf4203Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4203CertificateValid
    leaf4203InnerLogValid leaf4203CoversExact leaf4203LowerChecked

private noncomputable def leaf4204Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32), chiLo := (3/8), chiHi := (49/128) }

private noncomputable def leaf4204Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435739/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357405184) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (557791719/536870912) }, upper := { exponent := 1, mantissa := (8653/8192) } }, logOuter := sk111LogOuterCertificate, logK := sk111LogKCertificate, logChi := chi259LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716127743/68714810368) } }, logDArg := sk111LogDArgCertificate }

private noncomputable def leaf4204InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4204LocalValidity :
    LeafFacts leaf4204Box leaf4204Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4204Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357405184) }) = true
      norm_num [leaf4204Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4204CertificateValid :
    WideCertificateValid leaf4204Box leaf4204Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk111ValidityFacts chi259ValidityFacts
    leaf4204LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4204CoverageChecked :
    coverageCheck (innerAD leaf4204Box) leaf4204InnerLog = true := by
  rfl'

private theorem leaf4204InnerLogValid :
    leaf4204InnerLog.Valid 8 (innerAD leaf4204Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4204CoverageChecked

private noncomputable def leaf4204InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814701/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4204InputLogOnePlusV_eq :
    leaf4204InputLogOnePlusV = outerEnclosure 24
      (leaf4204Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4204RoundedFacts : LeafRoundedFacts 8
    leaf4204Certificate.logOnePlusV leaf4204InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4204InputLogOnePlusV_eq }

private noncomputable def leaf4204Inputs : Inputs :=
  inputsOfCaches globalInput sk111RoundedInputs
    chi259InputQChi innerPair242Input
    leaf4204InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4204LowerChecked :
    lowerCheck 24 leaf4204Box leaf4204Inputs = true := by
  rfl'

private theorem leaf4204CoversExact : CoversExact 8
    leaf4204Box leaf4204Certificate leaf4204InnerLog leaf4204Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk111RoundedFacts chi259RoundedFacts
    innerPair242RoundedFacts leaf4204RoundedFacts (by rfl)

private theorem leaf4204FlatSound : Sound leaf4204Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4204CertificateValid
    leaf4204InnerLogValid leaf4204CoversExact leaf4204LowerChecked

private noncomputable def leaf4205Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16), chiLo := (3/8), chiHi := (49/128) }

private noncomputable def leaf4205Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435741/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357380096) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (560937253/536870912) }, upper := { exponent := 1, mantissa := (4351/4096) } }, logOuter := sk112LogOuterCertificate, logK := sk112LogKCertificate, logChi := chi259LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716102655/68714760192) } }, logDArg := sk112LogDArgCertificate }

private noncomputable def leaf4205InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4205LocalValidity :
    LeafFacts leaf4205Box leaf4205Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4205Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357380096) }) = true
      norm_num [leaf4205Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4205CertificateValid :
    WideCertificateValid leaf4205Box leaf4205Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk112ValidityFacts chi259ValidityFacts
    leaf4205LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4205CoverageChecked :
    coverageCheck (innerAD leaf4205Box) leaf4205InnerLog = true := by
  rfl'

private theorem leaf4205InnerLogValid :
    leaf4205InnerLog.Valid 8 (innerAD leaf4205Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4205CoverageChecked

private noncomputable def leaf4205InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629409/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4205InputLogOnePlusV_eq :
    leaf4205InputLogOnePlusV = outerEnclosure 24
      (leaf4205Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4205RoundedFacts : LeafRoundedFacts 8
    leaf4205Certificate.logOnePlusV leaf4205InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4205InputLogOnePlusV_eq }

private noncomputable def leaf4205Inputs : Inputs :=
  inputsOfCaches globalInput sk112RoundedInputs
    chi259InputQChi innerPair242Input
    leaf4205InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4205LowerChecked :
    lowerCheck 24 leaf4205Box leaf4205Inputs = true := by
  rfl'

private theorem leaf4205CoversExact : CoversExact 8
    leaf4205Box leaf4205Certificate leaf4205InnerLog leaf4205Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk112RoundedFacts chi259RoundedFacts
    innerPair242RoundedFacts leaf4205RoundedFacts (by rfl)

private theorem leaf4205FlatSound : Sound leaf4205Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4205CertificateValid
    leaf4205InnerLogValid leaf4205CoversExact leaf4205LowerChecked

private noncomputable def leaf4206Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32), chiLo := (49/128), chiHi := (25/64) }

private noncomputable def leaf4206Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435741/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357357568) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (563820661/536870912) }, upper := { exponent := 1, mantissa := (4373/4096) } }, logOuter := sk111LogOuterCertificate, logK := sk111LogKCertificate, logChi := chi260LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716080127/68714715136) } }, logDArg := sk111LogDArgCertificate }

private noncomputable def leaf4206InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf4206LocalValidity :
    LeafFacts leaf4206Box leaf4206Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4206Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357357568) }) = true
      norm_num [leaf4206Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4206CertificateValid :
    WideCertificateValid leaf4206Box leaf4206Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk111ValidityFacts chi260ValidityFacts
    leaf4206LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4206CoverageChecked :
    coverageCheck (innerAD leaf4206Box) leaf4206InnerLog = true := by
  rfl'

private theorem leaf4206InnerLogValid :
    leaf4206InnerLog.Valid 8 (innerAD leaf4206Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf4206CoverageChecked

private noncomputable def leaf4206InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814707/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4206InputLogOnePlusV_eq :
    leaf4206InputLogOnePlusV = outerEnclosure 24
      (leaf4206Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4206RoundedFacts : LeafRoundedFacts 8
    leaf4206Certificate.logOnePlusV leaf4206InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4206InputLogOnePlusV_eq }

private noncomputable def leaf4206Inputs : Inputs :=
  inputsOfCaches globalInput sk111RoundedInputs
    chi260InputQChi innerPair243Input
    leaf4206InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4206LowerChecked :
    lowerCheck 24 leaf4206Box leaf4206Inputs = true := by
  rfl'

private theorem leaf4206CoversExact : CoversExact 8
    leaf4206Box leaf4206Certificate leaf4206InnerLog leaf4206Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk111RoundedFacts chi260RoundedFacts
    innerPair243RoundedFacts leaf4206RoundedFacts (by rfl)

private theorem leaf4206FlatSound : Sound leaf4206Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4206CertificateValid
    leaf4206InnerLogValid leaf4206CoversExact leaf4206LowerChecked

private noncomputable def leaf4207Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16), chiLo := (49/128), chiHi := (25/64) }

private noncomputable def leaf4207Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435743/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357331968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (567031727/536870912) }, upper := { exponent := 1, mantissa := (2199/2048) } }, logOuter := sk112LogOuterCertificate, logK := sk112LogKCertificate, logChi := chi260LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716054527/68714663936) } }, logDArg := sk112LogDArgCertificate }

private noncomputable def leaf4207InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf4207LocalValidity :
    LeafFacts leaf4207Box leaf4207Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4207Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357331968) }) = true
      norm_num [leaf4207Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4207CertificateValid :
    WideCertificateValid leaf4207Box leaf4207Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk112ValidityFacts chi260ValidityFacts
    leaf4207LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4207CoverageChecked :
    coverageCheck (innerAD leaf4207Box) leaf4207InnerLog = true := by
  rfl'

private theorem leaf4207InnerLogValid :
    leaf4207InnerLog.Valid 8 (innerAD leaf4207Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf4207CoverageChecked

private noncomputable def leaf4207InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907355/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4207InputLogOnePlusV_eq :
    leaf4207InputLogOnePlusV = outerEnclosure 24
      (leaf4207Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4207RoundedFacts : LeafRoundedFacts 8
    leaf4207Certificate.logOnePlusV leaf4207InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4207InputLogOnePlusV_eq }

private noncomputable def leaf4207Inputs : Inputs :=
  inputsOfCaches globalInput sk112RoundedInputs
    chi260InputQChi innerPair243Input
    leaf4207InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4207LowerChecked :
    lowerCheck 24 leaf4207Box leaf4207Inputs = true := by
  rfl'

private theorem leaf4207CoversExact : CoversExact 8
    leaf4207Box leaf4207Certificate leaf4207InnerLog leaf4207Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk112RoundedFacts chi260RoundedFacts
    innerPair243RoundedFacts leaf4207RoundedFacts (by rfl)

private theorem leaf4207FlatSound : Sound leaf4207Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4207CertificateValid
    leaf4207InnerLogValid leaf4207CoversExact leaf4207LowerChecked

private noncomputable def leaf4208Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32), chiLo := (25/64), chiHi := (51/128) }

private noncomputable def leaf4208Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435743/268435456) }, vSqrt := { lower := (32765/32768), upper := (4908388937/4908187136) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (569849603/536870912) }, upper := { exponent := 1, mantissa := (8839/8192) } }, logOuter := sk111LogOuterCertificate, logK := sk111LogKCertificate, logChi := chi261LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (9816576073/9816374272) } }, logDArg := sk111LogDArgCertificate }

private noncomputable def leaf4208InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf4208LocalValidity :
    LeafFacts leaf4208Box leaf4208Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4208Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4908388937/4908187136) }) = true
      norm_num [leaf4208Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4208CertificateValid :
    WideCertificateValid leaf4208Box leaf4208Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk111ValidityFacts chi261ValidityFacts
    leaf4208LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4208CoverageChecked :
    coverageCheck (innerAD leaf4208Box) leaf4208InnerLog = true := by
  rfl'

private theorem leaf4208InnerLogValid :
    leaf4208InnerLog.Valid 8 (innerAD leaf4208Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf4208CoverageChecked

private noncomputable def leaf4208InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814713/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4208InputLogOnePlusV_eq :
    leaf4208InputLogOnePlusV = outerEnclosure 24
      (leaf4208Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4208RoundedFacts : LeafRoundedFacts 8
    leaf4208Certificate.logOnePlusV leaf4208InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4208InputLogOnePlusV_eq }

private noncomputable def leaf4208Inputs : Inputs :=
  inputsOfCaches globalInput sk111RoundedInputs
    chi261InputQChi innerPair243Input
    leaf4208InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4208LowerChecked :
    lowerCheck 24 leaf4208Box leaf4208Inputs = true := by
  rfl'

private theorem leaf4208CoversExact : CoversExact 8
    leaf4208Box leaf4208Certificate leaf4208InnerLog leaf4208Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk111RoundedFacts chi261RoundedFacts
    innerPair243RoundedFacts leaf4208RoundedFacts (by rfl)

private theorem leaf4208FlatSound : Sound leaf4208Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4208CertificateValid
    leaf4208InnerLogValid leaf4208CoversExact leaf4208LowerChecked

private noncomputable def leaf4209Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16), chiLo := (25/64), chiHi := (51/128) }

private noncomputable def leaf4209Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435745/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357283840) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (573126201/536870912) }, upper := { exponent := 1, mantissa := (4445/4096) } }, logOuter := sk112LogOuterCertificate, logK := sk112LogKCertificate, logChi := chi261LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716006399/68714567680) } }, logDArg := sk112LogDArgCertificate }

private noncomputable def leaf4209InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf4209LocalValidity :
    LeafFacts leaf4209Box leaf4209Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4209Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357283840) }) = true
      norm_num [leaf4209Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4209CertificateValid :
    WideCertificateValid leaf4209Box leaf4209Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk112ValidityFacts chi261ValidityFacts
    leaf4209LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4209CoverageChecked :
    coverageCheck (innerAD leaf4209Box) leaf4209InnerLog = true := by
  rfl'

private theorem leaf4209InnerLogValid :
    leaf4209InnerLog.Valid 8 (innerAD leaf4209Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf4209CoverageChecked

private noncomputable def leaf4209InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453679/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf4209InputLogOnePlusV_eq :
    leaf4209InputLogOnePlusV = outerEnclosure 24
      (leaf4209Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4209RoundedFacts : LeafRoundedFacts 8
    leaf4209Certificate.logOnePlusV leaf4209InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4209InputLogOnePlusV_eq }

private noncomputable def leaf4209Inputs : Inputs :=
  inputsOfCaches globalInput sk112RoundedInputs
    chi261InputQChi innerPair249Input
    leaf4209InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4209LowerChecked :
    lowerCheck 24 leaf4209Box leaf4209Inputs = true := by
  rfl'

private theorem leaf4209CoversExact : CoversExact 8
    leaf4209Box leaf4209Certificate leaf4209InnerLog leaf4209Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk112RoundedFacts chi261RoundedFacts
    innerPair249RoundedFacts leaf4209RoundedFacts (by rfl)

private theorem leaf4209FlatSound : Sound leaf4209Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4209CertificateValid
    leaf4209InnerLogValid leaf4209CoversExact leaf4209LowerChecked

private noncomputable def leaf4210Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32), chiLo := (51/128), chiHi := (13/32) }

private noncomputable def leaf4210Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435745/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357262336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (575878545/536870912) }, upper := { exponent := 1, mantissa := (2233/2048) } }, logOuter := sk111LogOuterCertificate, logK := sk111LogKCertificate, logChi := chi262LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715984895/68714524672) } }, logDArg := sk111LogDArgCertificate }

private noncomputable def leaf4210InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf4210LocalValidity :
    LeafFacts leaf4210Box leaf4210Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4210Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357262336) }) = true
      norm_num [leaf4210Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4210CertificateValid :
    WideCertificateValid leaf4210Box leaf4210Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk111ValidityFacts chi262ValidityFacts
    leaf4210LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4210CoverageChecked :
    coverageCheck (innerAD leaf4210Box) leaf4210InnerLog = true := by
  rfl'

private theorem leaf4210InnerLogValid :
    leaf4210InnerLog.Valid 8 (innerAD leaf4210Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf4210CoverageChecked

private noncomputable def leaf4210InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629437/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4210InputLogOnePlusV_eq :
    leaf4210InputLogOnePlusV = outerEnclosure 24
      (leaf4210Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4210RoundedFacts : LeafRoundedFacts 8
    leaf4210Certificate.logOnePlusV leaf4210InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4210InputLogOnePlusV_eq }

private noncomputable def leaf4210Inputs : Inputs :=
  inputsOfCaches globalInput sk111RoundedInputs
    chi262InputQChi innerPair249Input
    leaf4210InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4210LowerChecked :
    lowerCheck 24 leaf4210Box leaf4210Inputs = true := by
  rfl'

private theorem leaf4210CoversExact : CoversExact 8
    leaf4210Box leaf4210Certificate leaf4210InnerLog leaf4210Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk111RoundedFacts chi262RoundedFacts
    innerPair249RoundedFacts leaf4210RoundedFacts (by rfl)

private theorem leaf4210FlatSound : Sound leaf4210Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4210CertificateValid
    leaf4210InnerLogValid leaf4210CoversExact leaf4210LowerChecked

private noncomputable def leaf4211Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16), chiLo := (51/128), chiHi := (13/32) }

private noncomputable def leaf4211Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435747/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357235712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (579220675/536870912) }, upper := { exponent := 1, mantissa := (1123/1024) } }, logOuter := sk112LogOuterCertificate, logK := sk112LogKCertificate, logChi := chi262LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715958271/68714471424) } }, logDArg := sk112LogDArgCertificate }

private noncomputable def leaf4211InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf4211LocalValidity :
    LeafFacts leaf4211Box leaf4211Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4211Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357235712) }) = true
      norm_num [leaf4211Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4211CertificateValid :
    WideCertificateValid leaf4211Box leaf4211Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk112ValidityFacts chi262ValidityFacts
    leaf4211LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4211CoverageChecked :
    coverageCheck (innerAD leaf4211Box) leaf4211InnerLog = true := by
  rfl'

private theorem leaf4211InnerLogValid :
    leaf4211InnerLog.Valid 8 (innerAD leaf4211Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf4211CoverageChecked

private noncomputable def leaf4211InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907361/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4211InputLogOnePlusV_eq :
    leaf4211InputLogOnePlusV = outerEnclosure 24
      (leaf4211Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4211RoundedFacts : LeafRoundedFacts 8
    leaf4211Certificate.logOnePlusV leaf4211InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4211InputLogOnePlusV_eq }

private noncomputable def leaf4211Inputs : Inputs :=
  inputsOfCaches globalInput sk112RoundedInputs
    chi262InputQChi innerPair250Input
    leaf4211InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4211LowerChecked :
    lowerCheck 24 leaf4211Box leaf4211Inputs = true := by
  rfl'

private theorem leaf4211CoversExact : CoversExact 8
    leaf4211Box leaf4211Certificate leaf4211InnerLog leaf4211Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk112RoundedFacts chi262RoundedFacts
    innerPair250RoundedFacts leaf4211RoundedFacts (by rfl)

private theorem leaf4211FlatSound : Sound leaf4211Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4211CertificateValid
    leaf4211InnerLogValid leaf4211CoversExact leaf4211LowerChecked

private noncomputable def leaf4212Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (95/32), chiLo := (3/8), chiHi := (49/128) }

private noncomputable def leaf4212Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435743/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357355008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (564082787/536870912) }, upper := { exponent := 1, mantissa := (8751/8192) } }, logOuter := sk113LogOuterCertificate, logK := sk113LogKCertificate, logChi := chi259LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716077567/68714710016) } }, logDArg := sk113LogDArgCertificate }

private noncomputable def leaf4212InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf4212LocalValidity :
    LeafFacts leaf4212Box leaf4212Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4212Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357355008) }) = true
      norm_num [leaf4212Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4212CertificateValid :
    WideCertificateValid leaf4212Box leaf4212Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk113ValidityFacts chi259ValidityFacts
    leaf4212LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4212CoverageChecked :
    coverageCheck (innerAD leaf4212Box) leaf4212InnerLog = true := by
  rfl'

private theorem leaf4212InnerLogValid :
    leaf4212InnerLog.Valid 8 (innerAD leaf4212Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf4212CoverageChecked

private noncomputable def leaf4212InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629415/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4212InputLogOnePlusV_eq :
    leaf4212InputLogOnePlusV = outerEnclosure 24
      (leaf4212Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4212RoundedFacts : LeafRoundedFacts 8
    leaf4212Certificate.logOnePlusV leaf4212InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4212InputLogOnePlusV_eq }

private noncomputable def leaf4212Inputs : Inputs :=
  inputsOfCaches globalInput sk113RoundedInputs
    chi259InputQChi innerPair243Input
    leaf4212InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4212LowerChecked :
    lowerCheck 24 leaf4212Box leaf4212Inputs = true := by
  rfl'

private theorem leaf4212CoversExact : CoversExact 8
    leaf4212Box leaf4212Certificate leaf4212InnerLog leaf4212Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk113RoundedFacts chi259RoundedFacts
    innerPair243RoundedFacts leaf4212RoundedFacts (by rfl)

private theorem leaf4212FlatSound : Sound leaf4212Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4212CertificateValid
    leaf4212InnerLogValid leaf4212CoversExact leaf4212LowerChecked

private noncomputable def leaf4213Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (3/8), chiHi := (49/128) }

private noncomputable def leaf4213Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435745/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357329920) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (567228321/536870912) }, upper := { exponent := 1, mantissa := (275/256) } }, logOuter := sk114LogOuterCertificate, logK := sk114LogKCertificate, logChi := chi259LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716052479/68714659840) } }, logDArg := sk114LogDArgCertificate }

private noncomputable def leaf4213InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf4213LocalValidity :
    LeafFacts leaf4213Box leaf4213Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4213Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357329920) }) = true
      norm_num [leaf4213Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4213CertificateValid :
    WideCertificateValid leaf4213Box leaf4213Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk114ValidityFacts chi259ValidityFacts
    leaf4213LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4213CoverageChecked :
    coverageCheck (innerAD leaf4213Box) leaf4213InnerLog = true := by
  rfl'

private theorem leaf4213InnerLogValid :
    leaf4213InnerLog.Valid 8 (innerAD leaf4213Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf4213CoverageChecked

private noncomputable def leaf4213InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629421/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4213InputLogOnePlusV_eq :
    leaf4213InputLogOnePlusV = outerEnclosure 24
      (leaf4213Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4213RoundedFacts : LeafRoundedFacts 8
    leaf4213Certificate.logOnePlusV leaf4213InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4213InputLogOnePlusV_eq }

private noncomputable def leaf4213Inputs : Inputs :=
  inputsOfCaches globalInput sk114RoundedInputs
    chi259InputQChi innerPair243Input
    leaf4213InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4213LowerChecked :
    lowerCheck 24 leaf4213Box leaf4213Inputs = true := by
  rfl'

private theorem leaf4213CoversExact : CoversExact 8
    leaf4213Box leaf4213Certificate leaf4213InnerLog leaf4213Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk114RoundedFacts chi259RoundedFacts
    innerPair243RoundedFacts leaf4213RoundedFacts (by rfl)

private theorem leaf4213FlatSound : Sound leaf4213Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4213CertificateValid
    leaf4213InnerLogValid leaf4213CoversExact leaf4213LowerChecked

private noncomputable def leaf4214Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (95/32), chiLo := (49/128), chiHi := (25/64) }

private noncomputable def leaf4214Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435745/268435456) }, vSqrt := { lower := (32765/32768), upper := (4908388937/4908186624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (570242793/536870912) }, upper := { exponent := 1, mantissa := (4423/4096) } }, logOuter := sk113LogOuterCertificate, logK := sk113LogKCertificate, logChi := chi260LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (9816575561/9816373248) } }, logDArg := sk113LogDArgCertificate }

private noncomputable def leaf4214InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf4214LocalValidity :
    LeafFacts leaf4214Box leaf4214Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4214Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4908388937/4908186624) }) = true
      norm_num [leaf4214Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4214CertificateValid :
    WideCertificateValid leaf4214Box leaf4214Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk113ValidityFacts chi260ValidityFacts
    leaf4214LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4214CoverageChecked :
    coverageCheck (innerAD leaf4214Box) leaf4214InnerLog = true := by
  rfl'

private theorem leaf4214InnerLogValid :
    leaf4214InnerLog.Valid 8 (innerAD leaf4214Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf4214CoverageChecked

private noncomputable def leaf4214InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629427/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4214InputLogOnePlusV_eq :
    leaf4214InputLogOnePlusV = outerEnclosure 24
      (leaf4214Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4214RoundedFacts : LeafRoundedFacts 8
    leaf4214Certificate.logOnePlusV leaf4214InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4214InputLogOnePlusV_eq }

private noncomputable def leaf4214Inputs : Inputs :=
  inputsOfCaches globalInput sk113RoundedInputs
    chi260InputQChi innerPair243Input
    leaf4214InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4214LowerChecked :
    lowerCheck 24 leaf4214Box leaf4214Inputs = true := by
  rfl'

private theorem leaf4214CoversExact : CoversExact 8
    leaf4214Box leaf4214Certificate leaf4214InnerLog leaf4214Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk113RoundedFacts chi260RoundedFacts
    innerPair243RoundedFacts leaf4214RoundedFacts (by rfl)

private theorem leaf4214FlatSound : Sound leaf4214Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4214CertificateValid
    leaf4214InnerLogValid leaf4214CoversExact leaf4214LowerChecked

private noncomputable def leaf4215Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (49/128), chiHi := (25/64) }

private noncomputable def leaf4215Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435747/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357280768) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (573453859/536870912) }, upper := { exponent := 1, mantissa := (139/128) } }, logOuter := sk114LogOuterCertificate, logK := sk114LogKCertificate, logChi := chi260LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716003327/68714561536) } }, logDArg := sk114LogDArgCertificate }

private noncomputable def leaf4215InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf4215LocalValidity :
    LeafFacts leaf4215Box leaf4215Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4215Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357280768) }) = true
      norm_num [leaf4215Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4215CertificateValid :
    WideCertificateValid leaf4215Box leaf4215Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk114ValidityFacts chi260ValidityFacts
    leaf4215LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4215CoverageChecked :
    coverageCheck (innerAD leaf4215Box) leaf4215InnerLog = true := by
  rfl'

private theorem leaf4215InnerLogValid :
    leaf4215InnerLog.Valid 8 (innerAD leaf4215Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf4215CoverageChecked

private noncomputable def leaf4215InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629433/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4215InputLogOnePlusV_eq :
    leaf4215InputLogOnePlusV = outerEnclosure 24
      (leaf4215Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4215RoundedFacts : LeafRoundedFacts 8
    leaf4215Certificate.logOnePlusV leaf4215InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4215InputLogOnePlusV_eq }

private noncomputable def leaf4215Inputs : Inputs :=
  inputsOfCaches globalInput sk114RoundedInputs
    chi260InputQChi innerPair249Input
    leaf4215InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4215LowerChecked :
    lowerCheck 24 leaf4215Box leaf4215Inputs = true := by
  rfl'

private theorem leaf4215CoversExact : CoversExact 8
    leaf4215Box leaf4215Certificate leaf4215InnerLog leaf4215Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk114RoundedFacts chi260RoundedFacts
    innerPair249RoundedFacts leaf4215RoundedFacts (by rfl)

private theorem leaf4215FlatSound : Sound leaf4215Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4215CertificateValid
    leaf4215InnerLogValid leaf4215CoversExact leaf4215LowerChecked

private noncomputable def leaf4216Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (95/32), chiLo := (25/64), chiHi := (51/128) }

private noncomputable def leaf4216Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435747/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357257728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (576402799/536870912) }, upper := { exponent := 1, mantissa := (8941/8192) } }, logOuter := sk113LogOuterCertificate, logK := sk113LogKCertificate, logChi := chi261LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715980287/68714515456) } }, logDArg := sk113LogDArgCertificate }

private noncomputable def leaf4216InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf4216LocalValidity :
    LeafFacts leaf4216Box leaf4216Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4216Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357257728) }) = true
      norm_num [leaf4216Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4216CertificateValid :
    WideCertificateValid leaf4216Box leaf4216Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk113ValidityFacts chi261ValidityFacts
    leaf4216LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4216CoverageChecked :
    coverageCheck (innerAD leaf4216Box) leaf4216InnerLog = true := by
  rfl'

private theorem leaf4216InnerLogValid :
    leaf4216InnerLog.Valid 8 (innerAD leaf4216Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf4216CoverageChecked

private noncomputable def leaf4216InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814719/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4216InputLogOnePlusV_eq :
    leaf4216InputLogOnePlusV = outerEnclosure 24
      (leaf4216Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4216RoundedFacts : LeafRoundedFacts 8
    leaf4216Certificate.logOnePlusV leaf4216InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4216InputLogOnePlusV_eq }

private noncomputable def leaf4216Inputs : Inputs :=
  inputsOfCaches globalInput sk113RoundedInputs
    chi261InputQChi innerPair249Input
    leaf4216InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4216LowerChecked :
    lowerCheck 24 leaf4216Box leaf4216Inputs = true := by
  rfl'

private theorem leaf4216CoversExact : CoversExact 8
    leaf4216Box leaf4216Certificate leaf4216InnerLog leaf4216Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk113RoundedFacts chi261RoundedFacts
    innerPair249RoundedFacts leaf4216RoundedFacts (by rfl)

private theorem leaf4216FlatSound : Sound leaf4216Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4216CertificateValid
    leaf4216InnerLogValid leaf4216CoversExact leaf4216LowerChecked

private noncomputable def leaf4217Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (25/64), chiHi := (51/128) }

private noncomputable def leaf4217Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435749/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357231616) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (579679397/536870912) }, upper := { exponent := 1, mantissa := (281/256) } }, logOuter := sk114LogOuterCertificate, logK := sk114LogKCertificate, logChi := chi261LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715954175/68714463232) } }, logDArg := sk114LogDArgCertificate }

private noncomputable def leaf4217InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf4217LocalValidity :
    LeafFacts leaf4217Box leaf4217Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4217Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357231616) }) = true
      norm_num [leaf4217Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4217CertificateValid :
    WideCertificateValid leaf4217Box leaf4217Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk114ValidityFacts chi261ValidityFacts
    leaf4217LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4217CoverageChecked :
    coverageCheck (innerAD leaf4217Box) leaf4217InnerLog = true := by
  rfl'

private theorem leaf4217InnerLogValid :
    leaf4217InnerLog.Valid 8 (innerAD leaf4217Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf4217CoverageChecked

private noncomputable def leaf4217InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629445/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4217InputLogOnePlusV_eq :
    leaf4217InputLogOnePlusV = outerEnclosure 24
      (leaf4217Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4217RoundedFacts : LeafRoundedFacts 8
    leaf4217Certificate.logOnePlusV leaf4217InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4217InputLogOnePlusV_eq }

private noncomputable def leaf4217Inputs : Inputs :=
  inputsOfCaches globalInput sk114RoundedInputs
    chi261InputQChi innerPair250Input
    leaf4217InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4217LowerChecked :
    lowerCheck 24 leaf4217Box leaf4217Inputs = true := by
  rfl'

private theorem leaf4217CoversExact : CoversExact 8
    leaf4217Box leaf4217Certificate leaf4217InnerLog leaf4217Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk114RoundedFacts chi261RoundedFacts
    innerPair250RoundedFacts leaf4217RoundedFacts (by rfl)

private theorem leaf4217FlatSound : Sound leaf4217Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4217CertificateValid
    leaf4217InnerLogValid leaf4217CoversExact leaf4217LowerChecked

private noncomputable def leaf4218Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (95/32), chiLo := (51/128), chiHi := (13/32) }

private noncomputable def leaf4218Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435749/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357209088) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (582562805/536870912) }, upper := { exponent := 1, mantissa := (2259/2048) } }, logOuter := sk113LogOuterCertificate, logK := sk113LogKCertificate, logChi := chi262LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715931647/68714418176) } }, logDArg := sk113LogDArgCertificate }

private noncomputable def leaf4218InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf4218LocalValidity :
    LeafFacts leaf4218Box leaf4218Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4218Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357209088) }) = true
      norm_num [leaf4218Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4218CertificateValid :
    WideCertificateValid leaf4218Box leaf4218Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk113ValidityFacts chi262ValidityFacts
    leaf4218LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4218CoverageChecked :
    coverageCheck (innerAD leaf4218Box) leaf4218InnerLog = true := by
  rfl'

private theorem leaf4218InnerLogValid :
    leaf4218InnerLog.Valid 8 (innerAD leaf4218Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf4218CoverageChecked

private noncomputable def leaf4218InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814725/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4218InputLogOnePlusV_eq :
    leaf4218InputLogOnePlusV = outerEnclosure 24
      (leaf4218Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4218RoundedFacts : LeafRoundedFacts 8
    leaf4218Certificate.logOnePlusV leaf4218InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4218InputLogOnePlusV_eq }

private noncomputable def leaf4218Inputs : Inputs :=
  inputsOfCaches globalInput sk113RoundedInputs
    chi262InputQChi innerPair250Input
    leaf4218InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4218LowerChecked :
    lowerCheck 24 leaf4218Box leaf4218Inputs = true := by
  rfl'

private theorem leaf4218CoversExact : CoversExact 8
    leaf4218Box leaf4218Certificate leaf4218InnerLog leaf4218Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk113RoundedFacts chi262RoundedFacts
    innerPair250RoundedFacts leaf4218RoundedFacts (by rfl)

private theorem leaf4218FlatSound : Sound leaf4218Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4218CertificateValid
    leaf4218InnerLogValid leaf4218CoversExact leaf4218LowerChecked

private noncomputable def leaf4219Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (51/128), chiHi := (13/32) }

private noncomputable def leaf4219Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435751/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357182464) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (585904935/536870912) }, upper := { exponent := 1, mantissa := (71/64) } }, logOuter := sk114LogOuterCertificate, logK := sk114LogKCertificate, logChi := chi262LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715905023/68714364928) } }, logDArg := sk114LogDArgCertificate }

private noncomputable def leaf4219InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf4219LocalValidity :
    LeafFacts leaf4219Box leaf4219Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4219Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357182464) }) = true
      norm_num [leaf4219Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4219CertificateValid :
    WideCertificateValid leaf4219Box leaf4219Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk114ValidityFacts chi262ValidityFacts
    leaf4219LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4219CoverageChecked :
    coverageCheck (innerAD leaf4219Box) leaf4219InnerLog = true := by
  rfl'

private theorem leaf4219InnerLogValid :
    leaf4219InnerLog.Valid 8 (innerAD leaf4219Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf4219CoverageChecked

private noncomputable def leaf4219InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629457/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4219InputLogOnePlusV_eq :
    leaf4219InputLogOnePlusV = outerEnclosure 24
      (leaf4219Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4219RoundedFacts : LeafRoundedFacts 8
    leaf4219Certificate.logOnePlusV leaf4219InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4219InputLogOnePlusV_eq }

private noncomputable def leaf4219Inputs : Inputs :=
  inputsOfCaches globalInput sk114RoundedInputs
    chi262InputQChi innerPair250Input
    leaf4219InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4219LowerChecked :
    lowerCheck 24 leaf4219Box leaf4219Inputs = true := by
  rfl'

private theorem leaf4219CoversExact : CoversExact 8
    leaf4219Box leaf4219Certificate leaf4219InnerLog leaf4219Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk114RoundedFacts chi262RoundedFacts
    innerPair250RoundedFacts leaf4219RoundedFacts (by rfl)

private theorem leaf4219FlatSound : Sound leaf4219Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4219CertificateValid
    leaf4219InnerLogValid leaf4219CoversExact leaf4219LowerChecked

private noncomputable def leaf4220Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32), chiLo := (13/32), chiHi := (53/128) }

private noncomputable def leaf4220Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435747/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357214720) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (581907487/536870912) }, upper := { exponent := 1, mantissa := (9025/8192) } }, logOuter := sk111LogOuterCertificate, logK := sk111LogKCertificate, logChi := chi263LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715937279/68714429440) } }, logDArg := sk111LogDArgCertificate }

private noncomputable def leaf4220InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf4220LocalValidity :
    LeafFacts leaf4220Box leaf4220Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4220Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357214720) }) = true
      norm_num [leaf4220Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4220CertificateValid :
    WideCertificateValid leaf4220Box leaf4220Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk111ValidityFacts chi263ValidityFacts
    leaf4220LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4220CoverageChecked :
    coverageCheck (innerAD leaf4220Box) leaf4220InnerLog = true := by
  rfl'

private theorem leaf4220InnerLogValid :
    leaf4220InnerLog.Valid 8 (innerAD leaf4220Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf4220CoverageChecked

private noncomputable def leaf4220InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629449/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4220InputLogOnePlusV_eq :
    leaf4220InputLogOnePlusV = outerEnclosure 24
      (leaf4220Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4220RoundedFacts : LeafRoundedFacts 8
    leaf4220Certificate.logOnePlusV leaf4220InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4220InputLogOnePlusV_eq }

private noncomputable def leaf4220Inputs : Inputs :=
  inputsOfCaches globalInput sk111RoundedInputs
    chi263InputQChi innerPair250Input
    leaf4220InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4220LowerChecked :
    lowerCheck 24 leaf4220Box leaf4220Inputs = true := by
  rfl'

private theorem leaf4220CoversExact : CoversExact 8
    leaf4220Box leaf4220Certificate leaf4220InnerLog leaf4220Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk111RoundedFacts chi263RoundedFacts
    innerPair250RoundedFacts leaf4220RoundedFacts (by rfl)

private theorem leaf4220FlatSound : Sound leaf4220Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4220CertificateValid
    leaf4220InnerLogValid leaf4220CoversExact leaf4220LowerChecked

private noncomputable def leaf4221Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16), chiLo := (13/32), chiHi := (53/128) }

private noncomputable def leaf4221Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435749/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357187584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (585315149/536870912) }, upper := { exponent := 1, mantissa := (4539/4096) } }, logOuter := sk112LogOuterCertificate, logK := sk112LogKCertificate, logChi := chi263LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715910143/68714375168) } }, logDArg := sk112LogDArgCertificate }

private noncomputable def leaf4221InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf4221LocalValidity :
    LeafFacts leaf4221Box leaf4221Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4221Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357187584) }) = true
      norm_num [leaf4221Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4221CertificateValid :
    WideCertificateValid leaf4221Box leaf4221Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk112ValidityFacts chi263ValidityFacts
    leaf4221LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4221CoverageChecked :
    coverageCheck (innerAD leaf4221Box) leaf4221InnerLog = true := by
  rfl'

private theorem leaf4221InnerLogValid :
    leaf4221InnerLog.Valid 8 (innerAD leaf4221Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf4221CoverageChecked

private noncomputable def leaf4221InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (726841/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf4221InputLogOnePlusV_eq :
    leaf4221InputLogOnePlusV = outerEnclosure 24
      (leaf4221Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4221RoundedFacts : LeafRoundedFacts 8
    leaf4221Certificate.logOnePlusV leaf4221InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4221InputLogOnePlusV_eq }

private noncomputable def leaf4221Inputs : Inputs :=
  inputsOfCaches globalInput sk112RoundedInputs
    chi263InputQChi innerPair250Input
    leaf4221InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4221LowerChecked :
    lowerCheck 24 leaf4221Box leaf4221Inputs = true := by
  rfl'

private theorem leaf4221CoversExact : CoversExact 8
    leaf4221Box leaf4221Certificate leaf4221InnerLog leaf4221Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk112RoundedFacts chi263RoundedFacts
    innerPair250RoundedFacts leaf4221RoundedFacts (by rfl)

private theorem leaf4221FlatSound : Sound leaf4221Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4221CertificateValid
    leaf4221InnerLogValid leaf4221CoversExact leaf4221LowerChecked

private noncomputable def leaf4222Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32), chiLo := (53/128), chiHi := (27/64) }

private noncomputable def leaf4222Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435749/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357167104) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (587936429/536870912) }, upper := { exponent := 1, mantissa := (4559/4096) } }, logOuter := sk111LogOuterCertificate, logK := sk111LogKCertificate, logChi := chi264LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715889663/68714334208) } }, logDArg := sk111LogDArgCertificate }

private noncomputable def leaf4222InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf4222LocalValidity :
    LeafFacts leaf4222Box leaf4222Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4222Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357167104) }) = true
      norm_num [leaf4222Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4222CertificateValid :
    WideCertificateValid leaf4222Box leaf4222Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk111ValidityFacts chi264ValidityFacts
    leaf4222LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4222CoverageChecked :
    coverageCheck (innerAD leaf4222Box) leaf4222InnerLog = true := by
  rfl'

private theorem leaf4222InnerLogValid :
    leaf4222InnerLog.Valid 8 (innerAD leaf4222Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf4222CoverageChecked

private noncomputable def leaf4222InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629461/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4222InputLogOnePlusV_eq :
    leaf4222InputLogOnePlusV = outerEnclosure 24
      (leaf4222Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4222RoundedFacts : LeafRoundedFacts 8
    leaf4222Certificate.logOnePlusV leaf4222InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4222InputLogOnePlusV_eq }

private noncomputable def leaf4222Inputs : Inputs :=
  inputsOfCaches globalInput sk111RoundedInputs
    chi264InputQChi innerPair256Input
    leaf4222InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4222LowerChecked :
    lowerCheck 24 leaf4222Box leaf4222Inputs = true := by
  rfl'

private theorem leaf4222CoversExact : CoversExact 8
    leaf4222Box leaf4222Certificate leaf4222InnerLog leaf4222Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk111RoundedFacts chi264RoundedFacts
    innerPair256RoundedFacts leaf4222RoundedFacts (by rfl)

private theorem leaf4222FlatSound : Sound leaf4222Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4222CertificateValid
    leaf4222InnerLogValid leaf4222CoversExact leaf4222LowerChecked

private noncomputable def leaf4223Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16), chiLo := (53/128), chiHi := (27/64) }

private noncomputable def leaf4223Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435751/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357139456) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (591409623/536870912) }, upper := { exponent := 1, mantissa := (2293/2048) } }, logOuter := sk112LogOuterCertificate, logK := sk112LogKCertificate, logChi := chi264LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715862015/68714278912) } }, logDArg := sk112LogDArgCertificate }

private noncomputable def leaf4223InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf4223LocalValidity :
    LeafFacts leaf4223Box leaf4223Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4223Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357139456) }) = true
      norm_num [leaf4223Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4223CertificateValid :
    WideCertificateValid leaf4223Box leaf4223Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk112ValidityFacts chi264ValidityFacts
    leaf4223LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4223CoverageChecked :
    coverageCheck (innerAD leaf4223Box) leaf4223InnerLog = true := by
  rfl'

private theorem leaf4223InnerLogValid :
    leaf4223InnerLog.Valid 8 (innerAD leaf4223Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf4223CoverageChecked

private noncomputable def leaf4223InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629467/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4223InputLogOnePlusV_eq :
    leaf4223InputLogOnePlusV = outerEnclosure 24
      (leaf4223Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4223RoundedFacts : LeafRoundedFacts 8
    leaf4223Certificate.logOnePlusV leaf4223InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4223InputLogOnePlusV_eq }

private noncomputable def leaf4223Inputs : Inputs :=
  inputsOfCaches globalInput sk112RoundedInputs
    chi264InputQChi innerPair256Input
    leaf4223InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4223LowerChecked :
    lowerCheck 24 leaf4223Box leaf4223Inputs = true := by
  rfl'

private theorem leaf4223CoversExact : CoversExact 8
    leaf4223Box leaf4223Certificate leaf4223InnerLog leaf4223Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk112RoundedFacts chi264RoundedFacts
    innerPair256RoundedFacts leaf4223RoundedFacts (by rfl)

private theorem leaf4223FlatSound : Sound leaf4223Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4223CertificateValid
    leaf4223InnerLogValid leaf4223CoversExact leaf4223LowerChecked

private noncomputable def leaf4224Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32), chiLo := (27/64), chiHi := (55/128) }

private noncomputable def leaf4224Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435751/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357119488) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (593965371/536870912) }, upper := { exponent := 1, mantissa := (9211/8192) } }, logOuter := sk111LogOuterCertificate, logK := sk111LogKCertificate, logChi := chi265LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715842047/68714238976) } }, logDArg := sk111LogDArgCertificate }

private noncomputable def leaf4224InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf4224LocalValidity :
    LeafFacts leaf4224Box leaf4224Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4224Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357119488) }) = true
      norm_num [leaf4224Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4224CertificateValid :
    WideCertificateValid leaf4224Box leaf4224Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk111ValidityFacts chi265ValidityFacts
    leaf4224LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4224CoverageChecked :
    coverageCheck (innerAD leaf4224Box) leaf4224InnerLog = true := by
  rfl'

private theorem leaf4224InnerLogValid :
    leaf4224InnerLog.Valid 8 (innerAD leaf4224Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf4224CoverageChecked

private noncomputable def leaf4224InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (363421/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf4224InputLogOnePlusV_eq :
    leaf4224InputLogOnePlusV = outerEnclosure 24
      (leaf4224Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4224RoundedFacts : LeafRoundedFacts 8
    leaf4224Certificate.logOnePlusV leaf4224InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4224InputLogOnePlusV_eq }

private noncomputable def leaf4224Inputs : Inputs :=
  inputsOfCaches globalInput sk111RoundedInputs
    chi265InputQChi innerPair256Input
    leaf4224InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4224LowerChecked :
    lowerCheck 24 leaf4224Box leaf4224Inputs = true := by
  rfl'

private theorem leaf4224CoversExact : CoversExact 8
    leaf4224Box leaf4224Certificate leaf4224InnerLog leaf4224Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk111RoundedFacts chi265RoundedFacts
    innerPair256RoundedFacts leaf4224RoundedFacts (by rfl)

private theorem leaf4224FlatSound : Sound leaf4224Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4224CertificateValid
    leaf4224InnerLogValid leaf4224CoversExact leaf4224LowerChecked

private noncomputable def leaf4225Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16), chiLo := (27/64), chiHi := (55/128) }

private noncomputable def leaf4225Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435753/268435456) }, vSqrt := { lower := (32765/32768), upper := (4908388937/4908155904) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (597504097/536870912) }, upper := { exponent := 1, mantissa := (4633/4096) } }, logOuter := sk112LogOuterCertificate, logK := sk112LogKCertificate, logChi := chi265LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (9816544841/9816311808) } }, logDArg := sk112LogDArgCertificate }

private noncomputable def leaf4225InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf4225LocalValidity :
    LeafFacts leaf4225Box leaf4225Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4225Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4908388937/4908155904) }) = true
      norm_num [leaf4225Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4225CertificateValid :
    WideCertificateValid leaf4225Box leaf4225Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk112ValidityFacts chi265ValidityFacts
    leaf4225LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4225CoverageChecked :
    coverageCheck (innerAD leaf4225Box) leaf4225InnerLog = true := by
  rfl'

private theorem leaf4225InnerLogValid :
    leaf4225InnerLog.Valid 8 (innerAD leaf4225Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf4225CoverageChecked

private noncomputable def leaf4225InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629479/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4225InputLogOnePlusV_eq :
    leaf4225InputLogOnePlusV = outerEnclosure 24
      (leaf4225Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4225RoundedFacts : LeafRoundedFacts 8
    leaf4225Certificate.logOnePlusV leaf4225InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4225InputLogOnePlusV_eq }

private noncomputable def leaf4225Inputs : Inputs :=
  inputsOfCaches globalInput sk112RoundedInputs
    chi265InputQChi innerPair257Input
    leaf4225InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4225LowerChecked :
    lowerCheck 24 leaf4225Box leaf4225Inputs = true := by
  rfl'

private theorem leaf4225CoversExact : CoversExact 8
    leaf4225Box leaf4225Certificate leaf4225InnerLog leaf4225Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk112RoundedFacts chi265RoundedFacts
    innerPair257RoundedFacts leaf4225RoundedFacts (by rfl)

private theorem leaf4225FlatSound : Sound leaf4225Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4225CertificateValid
    leaf4225InnerLogValid leaf4225CoversExact leaf4225LowerChecked

private noncomputable def leaf4226Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32), chiLo := (55/128), chiHi := (7/16) }

private noncomputable def leaf4226Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435753/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357071872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (599994313/536870912) }, upper := { exponent := 1, mantissa := (1163/1024) } }, logOuter := sk111LogOuterCertificate, logK := sk111LogKCertificate, logChi := chi266LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715794431/68714143744) } }, logDArg := sk111LogDArgCertificate }

private noncomputable def leaf4226InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf4226LocalValidity :
    LeafFacts leaf4226Box leaf4226Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4226Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357071872) }) = true
      norm_num [leaf4226Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4226CertificateValid :
    WideCertificateValid leaf4226Box leaf4226Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk111ValidityFacts chi266ValidityFacts
    leaf4226LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4226CoverageChecked :
    coverageCheck (innerAD leaf4226Box) leaf4226InnerLog = true := by
  rfl'

private theorem leaf4226InnerLogValid :
    leaf4226InnerLog.Valid 8 (innerAD leaf4226Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf4226CoverageChecked

private noncomputable def leaf4226InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907371/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4226InputLogOnePlusV_eq :
    leaf4226InputLogOnePlusV = outerEnclosure 24
      (leaf4226Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4226RoundedFacts : LeafRoundedFacts 8
    leaf4226Certificate.logOnePlusV leaf4226InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4226InputLogOnePlusV_eq }

private noncomputable def leaf4226Inputs : Inputs :=
  inputsOfCaches globalInput sk111RoundedInputs
    chi266InputQChi innerPair257Input
    leaf4226InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4226LowerChecked :
    lowerCheck 24 leaf4226Box leaf4226Inputs = true := by
  rfl'

private theorem leaf4226CoversExact : CoversExact 8
    leaf4226Box leaf4226Certificate leaf4226InnerLog leaf4226Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk111RoundedFacts chi266RoundedFacts
    innerPair257RoundedFacts leaf4226RoundedFacts (by rfl)

private theorem leaf4226FlatSound : Sound leaf4226Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4226CertificateValid
    leaf4226InnerLogValid leaf4226CoversExact leaf4226LowerChecked

private noncomputable def leaf4227Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16), chiLo := (55/128), chiHi := (7/16) }

private noncomputable def leaf4227Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435755/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357043200) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (603598571/536870912) }, upper := { exponent := 1, mantissa := (585/512) } }, logOuter := sk112LogOuterCertificate, logK := sk112LogKCertificate, logChi := chi266LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715765759/68714086400) } }, logDArg := sk112LogDArgCertificate }

private noncomputable def leaf4227InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf4227LocalValidity :
    LeafFacts leaf4227Box leaf4227Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4227Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357043200) }) = true
      norm_num [leaf4227Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4227CertificateValid :
    WideCertificateValid leaf4227Box leaf4227Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk112ValidityFacts chi266ValidityFacts
    leaf4227LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4227CoverageChecked :
    coverageCheck (innerAD leaf4227Box) leaf4227InnerLog = true := by
  rfl'

private theorem leaf4227InnerLogValid :
    leaf4227InnerLog.Valid 8 (innerAD leaf4227Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf4227CoverageChecked

private noncomputable def leaf4227InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629491/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4227InputLogOnePlusV_eq :
    leaf4227InputLogOnePlusV = outerEnclosure 24
      (leaf4227Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4227RoundedFacts : LeafRoundedFacts 8
    leaf4227Certificate.logOnePlusV leaf4227InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4227InputLogOnePlusV_eq }

private noncomputable def leaf4227Inputs : Inputs :=
  inputsOfCaches globalInput sk112RoundedInputs
    chi266InputQChi innerPair257Input
    leaf4227InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4227LowerChecked :
    lowerCheck 24 leaf4227Box leaf4227Inputs = true := by
  rfl'

private theorem leaf4227CoversExact : CoversExact 8
    leaf4227Box leaf4227Certificate leaf4227InnerLog leaf4227Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk112RoundedFacts chi266RoundedFacts
    innerPair257RoundedFacts leaf4227RoundedFacts (by rfl)

private theorem leaf4227FlatSound : Sound leaf4227Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4227CertificateValid
    leaf4227InnerLogValid leaf4227CoversExact leaf4227LowerChecked

private noncomputable def leaf4228Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (95/32), chiLo := (13/32), chiHi := (53/128) }

private noncomputable def leaf4228Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435751/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357160448) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (588722811/536870912) }, upper := { exponent := 1, mantissa := (9131/8192) } }, logOuter := sk113LogOuterCertificate, logK := sk113LogKCertificate, logChi := chi263LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715883007/68714320896) } }, logDArg := sk113LogDArgCertificate }

private noncomputable def leaf4228InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf4228LocalValidity :
    LeafFacts leaf4228Box leaf4228Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4228Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357160448) }) = true
      norm_num [leaf4228Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4228CertificateValid :
    WideCertificateValid leaf4228Box leaf4228Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk113ValidityFacts chi263ValidityFacts
    leaf4228LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4228CoverageChecked :
    coverageCheck (innerAD leaf4228Box) leaf4228InnerLog = true := by
  rfl'

private theorem leaf4228InnerLogValid :
    leaf4228InnerLog.Valid 8 (innerAD leaf4228Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf4228CoverageChecked

private noncomputable def leaf4228InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814731/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4228InputLogOnePlusV_eq :
    leaf4228InputLogOnePlusV = outerEnclosure 24
      (leaf4228Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4228RoundedFacts : LeafRoundedFacts 8
    leaf4228Certificate.logOnePlusV leaf4228InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4228InputLogOnePlusV_eq }

private noncomputable def leaf4228Inputs : Inputs :=
  inputsOfCaches globalInput sk113RoundedInputs
    chi263InputQChi innerPair256Input
    leaf4228InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4228LowerChecked :
    lowerCheck 24 leaf4228Box leaf4228Inputs = true := by
  rfl'

private theorem leaf4228CoversExact : CoversExact 8
    leaf4228Box leaf4228Certificate leaf4228InnerLog leaf4228Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk113RoundedFacts chi263RoundedFacts
    innerPair256RoundedFacts leaf4228RoundedFacts (by rfl)

private theorem leaf4228FlatSound : Sound leaf4228Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4228CertificateValid
    leaf4228InnerLogValid leaf4228CoversExact leaf4228LowerChecked

private noncomputable def leaf4229Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (13/32), chiHi := (53/128) }

private noncomputable def leaf4229Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435753/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357133312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (592130473/536870912) }, upper := { exponent := 1, mantissa := (287/256) } }, logOuter := sk114LogOuterCertificate, logK := sk114LogKCertificate, logChi := chi263LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715855871/68714266624) } }, logDArg := sk114LogDArgCertificate }

private noncomputable def leaf4229InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf4229LocalValidity :
    LeafFacts leaf4229Box leaf4229Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4229Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357133312) }) = true
      norm_num [leaf4229Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4229CertificateValid :
    WideCertificateValid leaf4229Box leaf4229Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk114ValidityFacts chi263ValidityFacts
    leaf4229LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4229CoverageChecked :
    coverageCheck (innerAD leaf4229Box) leaf4229InnerLog = true := by
  rfl'

private theorem leaf4229InnerLogValid :
    leaf4229InnerLog.Valid 8 (innerAD leaf4229Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf4229CoverageChecked

private noncomputable def leaf4229InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629469/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4229InputLogOnePlusV_eq :
    leaf4229InputLogOnePlusV = outerEnclosure 24
      (leaf4229Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4229RoundedFacts : LeafRoundedFacts 8
    leaf4229Certificate.logOnePlusV leaf4229InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4229InputLogOnePlusV_eq }

private noncomputable def leaf4229Inputs : Inputs :=
  inputsOfCaches globalInput sk114RoundedInputs
    chi263InputQChi innerPair256Input
    leaf4229InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4229LowerChecked :
    lowerCheck 24 leaf4229Box leaf4229Inputs = true := by
  rfl'

private theorem leaf4229CoversExact : CoversExact 8
    leaf4229Box leaf4229Certificate leaf4229InnerLog leaf4229Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk114RoundedFacts chi263RoundedFacts
    innerPair256RoundedFacts leaf4229RoundedFacts (by rfl)

private theorem leaf4229FlatSound : Sound leaf4229Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4229CertificateValid
    leaf4229InnerLogValid leaf4229CoversExact leaf4229LowerChecked

private noncomputable def leaf4230Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (95/32), chiLo := (53/128), chiHi := (27/64) }

private noncomputable def leaf4230Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435753/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357111808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (594882817/536870912) }, upper := { exponent := 1, mantissa := (4613/4096) } }, logOuter := sk113LogOuterCertificate, logK := sk113LogKCertificate, logChi := chi264LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715834367/68714223616) } }, logDArg := sk113LogDArgCertificate }

private noncomputable def leaf4230InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf4230LocalValidity :
    LeafFacts leaf4230Box leaf4230Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4230Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357111808) }) = true
      norm_num [leaf4230Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4230CertificateValid :
    WideCertificateValid leaf4230Box leaf4230Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk113ValidityFacts chi264ValidityFacts
    leaf4230LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4230CoverageChecked :
    coverageCheck (innerAD leaf4230Box) leaf4230InnerLog = true := by
  rfl'

private theorem leaf4230InnerLogValid :
    leaf4230InnerLog.Valid 8 (innerAD leaf4230Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf4230CoverageChecked

private noncomputable def leaf4230InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814737/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4230InputLogOnePlusV_eq :
    leaf4230InputLogOnePlusV = outerEnclosure 24
      (leaf4230Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4230RoundedFacts : LeafRoundedFacts 8
    leaf4230Certificate.logOnePlusV leaf4230InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4230InputLogOnePlusV_eq }

private noncomputable def leaf4230Inputs : Inputs :=
  inputsOfCaches globalInput sk113RoundedInputs
    chi264InputQChi innerPair257Input
    leaf4230InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4230LowerChecked :
    lowerCheck 24 leaf4230Box leaf4230Inputs = true := by
  rfl'

private theorem leaf4230CoversExact : CoversExact 8
    leaf4230Box leaf4230Certificate leaf4230InnerLog leaf4230Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk113RoundedFacts chi264RoundedFacts
    innerPair257RoundedFacts leaf4230RoundedFacts (by rfl)

private theorem leaf4230FlatSound : Sound leaf4230Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4230CertificateValid
    leaf4230InnerLogValid leaf4230CoversExact leaf4230LowerChecked

private noncomputable def leaf4231Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (53/128), chiHi := (27/64) }

private noncomputable def leaf4231Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435755/268435456) }, vSqrt := { lower := (65529/65536), upper := (4908388937/4908154880) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (598356011/536870912) }, upper := { exponent := 1, mantissa := (145/128) } }, logOuter := sk114LogOuterCertificate, logK := sk114LogKCertificate, logChi := chi264LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9816543817/9816309760) } }, logDArg := sk114LogDArgCertificate }

private noncomputable def leaf4231InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf4231LocalValidity :
    LeafFacts leaf4231Box leaf4231Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4231Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4908388937/4908154880) }) = true
      norm_num [leaf4231Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4231CertificateValid :
    WideCertificateValid leaf4231Box leaf4231Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk114ValidityFacts chi264ValidityFacts
    leaf4231LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4231CoverageChecked :
    coverageCheck (innerAD leaf4231Box) leaf4231InnerLog = true := by
  rfl'

private theorem leaf4231InnerLogValid :
    leaf4231InnerLog.Valid 8 (innerAD leaf4231Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf4231CoverageChecked

private noncomputable def leaf4231InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629481/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4231InputLogOnePlusV_eq :
    leaf4231InputLogOnePlusV = outerEnclosure 24
      (leaf4231Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4231RoundedFacts : LeafRoundedFacts 8
    leaf4231Certificate.logOnePlusV leaf4231InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4231InputLogOnePlusV_eq }

private noncomputable def leaf4231Inputs : Inputs :=
  inputsOfCaches globalInput sk114RoundedInputs
    chi264InputQChi innerPair257Input
    leaf4231InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4231LowerChecked :
    lowerCheck 24 leaf4231Box leaf4231Inputs = true := by
  rfl'

private theorem leaf4231CoversExact : CoversExact 8
    leaf4231Box leaf4231Certificate leaf4231InnerLog leaf4231Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk114RoundedFacts chi264RoundedFacts
    innerPair257RoundedFacts leaf4231RoundedFacts (by rfl)

private theorem leaf4231FlatSound : Sound leaf4231Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4231CertificateValid
    leaf4231InnerLogValid leaf4231CoversExact leaf4231LowerChecked

private noncomputable def leaf4232Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (95/32), chiLo := (27/64), chiHi := (55/128) }

private noncomputable def leaf4232Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435755/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357063168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (601042823/536870912) }, upper := { exponent := 1, mantissa := (9321/8192) } }, logOuter := sk113LogOuterCertificate, logK := sk113LogKCertificate, logChi := chi265LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715785727/68714126336) } }, logDArg := sk113LogDArgCertificate }

private noncomputable def leaf4232InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf4232LocalValidity :
    LeafFacts leaf4232Box leaf4232Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4232Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357063168) }) = true
      norm_num [leaf4232Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4232CertificateValid :
    WideCertificateValid leaf4232Box leaf4232Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk113ValidityFacts chi265ValidityFacts
    leaf4232LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4232CoverageChecked :
    coverageCheck (innerAD leaf4232Box) leaf4232InnerLog = true := by
  rfl'

private theorem leaf4232InnerLogValid :
    leaf4232InnerLog.Valid 8 (innerAD leaf4232Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf4232CoverageChecked

private noncomputable def leaf4232InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814743/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4232InputLogOnePlusV_eq :
    leaf4232InputLogOnePlusV = outerEnclosure 24
      (leaf4232Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4232RoundedFacts : LeafRoundedFacts 8
    leaf4232Certificate.logOnePlusV leaf4232InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4232InputLogOnePlusV_eq }

private noncomputable def leaf4232Inputs : Inputs :=
  inputsOfCaches globalInput sk113RoundedInputs
    chi265InputQChi innerPair257Input
    leaf4232InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4232LowerChecked :
    lowerCheck 24 leaf4232Box leaf4232Inputs = true := by
  rfl'

private theorem leaf4232CoversExact : CoversExact 8
    leaf4232Box leaf4232Certificate leaf4232InnerLog leaf4232Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk113RoundedFacts chi265RoundedFacts
    innerPair257RoundedFacts leaf4232RoundedFacts (by rfl)

private theorem leaf4232FlatSound : Sound leaf4232Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4232CertificateValid
    leaf4232InnerLogValid leaf4232CoversExact leaf4232LowerChecked

private noncomputable def leaf4233Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (27/64), chiHi := (55/128) }

private noncomputable def leaf4233Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435757/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357035008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (604581549/536870912) }, upper := { exponent := 1, mantissa := (293/256) } }, logOuter := sk114LogOuterCertificate, logK := sk114LogKCertificate, logChi := chi265LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715757567/68714070016) } }, logDArg := sk114LogDArgCertificate }

private noncomputable def leaf4233InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf4233LocalValidity :
    LeafFacts leaf4233Box leaf4233Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4233Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357035008) }) = true
      norm_num [leaf4233Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4233CertificateValid :
    WideCertificateValid leaf4233Box leaf4233Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk114ValidityFacts chi265ValidityFacts
    leaf4233LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4233CoverageChecked :
    coverageCheck (innerAD leaf4233Box) leaf4233InnerLog = true := by
  rfl'

private theorem leaf4233InnerLogValid :
    leaf4233InnerLog.Valid 8 (innerAD leaf4233Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf4233CoverageChecked

private noncomputable def leaf4233InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629493/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4233InputLogOnePlusV_eq :
    leaf4233InputLogOnePlusV = outerEnclosure 24
      (leaf4233Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4233RoundedFacts : LeafRoundedFacts 8
    leaf4233Certificate.logOnePlusV leaf4233InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4233InputLogOnePlusV_eq }

private noncomputable def leaf4233Inputs : Inputs :=
  inputsOfCaches globalInput sk114RoundedInputs
    chi265InputQChi innerPair264Input
    leaf4233InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4233LowerChecked :
    lowerCheck 24 leaf4233Box leaf4233Inputs = true := by
  rfl'

private theorem leaf4233CoversExact : CoversExact 8
    leaf4233Box leaf4233Certificate leaf4233InnerLog leaf4233Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk114RoundedFacts chi265RoundedFacts
    innerPair264RoundedFacts leaf4233RoundedFacts (by rfl)

private theorem leaf4233FlatSound : Sound leaf4233Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4233CertificateValid
    leaf4233InnerLogValid leaf4233CoversExact leaf4233LowerChecked

private noncomputable def leaf4234Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (95/32), chiLo := (55/128), chiHi := (7/16) }

private noncomputable def leaf4234Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435757/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357014528) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (607202829/536870912) }, upper := { exponent := 1, mantissa := (1177/1024) } }, logOuter := sk113LogOuterCertificate, logK := sk113LogKCertificate, logChi := chi266LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715737087/68714029056) } }, logDArg := sk113LogDArgCertificate }

private noncomputable def leaf4234InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf4234LocalValidity :
    LeafFacts leaf4234Box leaf4234Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4234Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357014528) }) = true
      norm_num [leaf4234Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4234CertificateValid :
    WideCertificateValid leaf4234Box leaf4234Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk113ValidityFacts chi266ValidityFacts
    leaf4234LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4234CoverageChecked :
    coverageCheck (innerAD leaf4234Box) leaf4234InnerLog = true := by
  rfl'

private theorem leaf4234InnerLogValid :
    leaf4234InnerLog.Valid 8 (innerAD leaf4234Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf4234CoverageChecked

private noncomputable def leaf4234InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814749/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4234InputLogOnePlusV_eq :
    leaf4234InputLogOnePlusV = outerEnclosure 24
      (leaf4234Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4234RoundedFacts : LeafRoundedFacts 8
    leaf4234Certificate.logOnePlusV leaf4234InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4234InputLogOnePlusV_eq }

private noncomputable def leaf4234Inputs : Inputs :=
  inputsOfCaches globalInput sk113RoundedInputs
    chi266InputQChi innerPair264Input
    leaf4234InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4234LowerChecked :
    lowerCheck 24 leaf4234Box leaf4234Inputs = true := by
  rfl'

private theorem leaf4234CoversExact : CoversExact 8
    leaf4234Box leaf4234Certificate leaf4234InnerLog leaf4234Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk113RoundedFacts chi266RoundedFacts
    innerPair264RoundedFacts leaf4234RoundedFacts (by rfl)

private theorem leaf4234FlatSound : Sound leaf4234Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4234CertificateValid
    leaf4234InnerLogValid leaf4234CoversExact leaf4234LowerChecked

private noncomputable def leaf4235Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (55/128), chiHi := (7/16) }

private noncomputable def leaf4235Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435759/268435456) }, vSqrt := { lower := (65529/65536), upper := (2021101327/2020999168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (610807087/536870912) }, upper := { exponent := 1, mantissa := (37/32) } }, logOuter := sk114LogOuterCertificate, logK := sk114LogKCertificate, logChi := chi266LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (4042100495/4041998336) } }, logDArg := sk114LogDArgCertificate }

private noncomputable def leaf4235InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf4235LocalValidity :
    LeafFacts leaf4235Box leaf4235Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4235Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (2021101327/2020999168) }) = true
      norm_num [leaf4235Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4235CertificateValid :
    WideCertificateValid leaf4235Box leaf4235Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk114ValidityFacts chi266ValidityFacts
    leaf4235LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4235CoverageChecked :
    coverageCheck (innerAD leaf4235Box) leaf4235InnerLog = true := by
  rfl'

private theorem leaf4235InnerLogValid :
    leaf4235InnerLog.Valid 8 (innerAD leaf4235Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf4235CoverageChecked

private noncomputable def leaf4235InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629505/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4235InputLogOnePlusV_eq :
    leaf4235InputLogOnePlusV = outerEnclosure 24
      (leaf4235Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4235RoundedFacts : LeafRoundedFacts 8
    leaf4235Certificate.logOnePlusV leaf4235InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4235InputLogOnePlusV_eq }

private noncomputable def leaf4235Inputs : Inputs :=
  inputsOfCaches globalInput sk114RoundedInputs
    chi266InputQChi innerPair264Input
    leaf4235InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4235LowerChecked :
    lowerCheck 24 leaf4235Box leaf4235Inputs = true := by
  rfl'

private theorem leaf4235CoversExact : CoversExact 8
    leaf4235Box leaf4235Certificate leaf4235InnerLog leaf4235Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk114RoundedFacts chi266RoundedFacts
    innerPair264RoundedFacts leaf4235RoundedFacts (by rfl)

private theorem leaf4235FlatSound : Sound leaf4235Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4235CertificateValid
    leaf4235InnerLogValid leaf4235CoversExact leaf4235LowerChecked

private noncomputable def component86Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (3/8), chiHi := (49/128) }

set_option maxRecDepth 1000000 in
private theorem component86Node0_sound : Sound component86Node0Box :=
  sound_of_literal_split component86Node0Box leaf4172Box leaf4173Box
    .k (89/32) (by rfl) (by rfl)
    leaf4172FlatSound leaf4173FlatSound

private noncomputable def component86Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (49/128), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component86Node1_sound : Sound component86Node1Box :=
  sound_of_literal_split component86Node1Box leaf4174Box leaf4175Box
    .k (89/32) (by rfl) (by rfl)
    leaf4174FlatSound leaf4175FlatSound

private noncomputable def component86Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (3/8), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component86Node2_sound : Sound component86Node2Box :=
  sound_of_literal_split component86Node2Box component86Node0Box component86Node1Box
    .chi (49/128) (by rfl) (by rfl)
    component86Node0_sound component86Node1_sound

private noncomputable def component86Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (25/64), chiHi := (51/128) }

set_option maxRecDepth 1000000 in
private theorem component86Node3_sound : Sound component86Node3Box :=
  sound_of_literal_split component86Node3Box leaf4176Box leaf4177Box
    .k (89/32) (by rfl) (by rfl)
    leaf4176FlatSound leaf4177FlatSound

private noncomputable def component86Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (51/128), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component86Node4_sound : Sound component86Node4Box :=
  sound_of_literal_split component86Node4Box leaf4178Box leaf4179Box
    .k (89/32) (by rfl) (by rfl)
    leaf4178FlatSound leaf4179FlatSound

private noncomputable def component86Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (25/64), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component86Node5_sound : Sound component86Node5Box :=
  sound_of_literal_split component86Node5Box component86Node3Box component86Node4Box
    .chi (51/128) (by rfl) (by rfl)
    component86Node3_sound component86Node4_sound

private noncomputable def component86Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (3/8), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component86Node6_sound : Sound component86Node6Box :=
  sound_of_literal_split component86Node6Box component86Node2Box component86Node5Box
    .chi (25/64) (by rfl) (by rfl)
    component86Node2_sound component86Node5_sound

private noncomputable def component86Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (3/8), chiHi := (49/128) }

set_option maxRecDepth 1000000 in
private theorem component86Node7_sound : Sound component86Node7Box :=
  sound_of_literal_split component86Node7Box leaf4180Box leaf4181Box
    .k (91/32) (by rfl) (by rfl)
    leaf4180FlatSound leaf4181FlatSound

private noncomputable def component86Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (49/128), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component86Node8_sound : Sound component86Node8Box :=
  sound_of_literal_split component86Node8Box leaf4182Box leaf4183Box
    .k (91/32) (by rfl) (by rfl)
    leaf4182FlatSound leaf4183FlatSound

private noncomputable def component86Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (3/8), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component86Node9_sound : Sound component86Node9Box :=
  sound_of_literal_split component86Node9Box component86Node7Box component86Node8Box
    .chi (49/128) (by rfl) (by rfl)
    component86Node7_sound component86Node8_sound

private noncomputable def component86Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (25/64), chiHi := (51/128) }

set_option maxRecDepth 1000000 in
private theorem component86Node10_sound : Sound component86Node10Box :=
  sound_of_literal_split component86Node10Box leaf4184Box leaf4185Box
    .k (91/32) (by rfl) (by rfl)
    leaf4184FlatSound leaf4185FlatSound

private noncomputable def component86Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (51/128), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component86Node11_sound : Sound component86Node11Box :=
  sound_of_literal_split component86Node11Box leaf4186Box leaf4187Box
    .k (91/32) (by rfl) (by rfl)
    leaf4186FlatSound leaf4187FlatSound

private noncomputable def component86Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (25/64), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component86Node12_sound : Sound component86Node12Box :=
  sound_of_literal_split component86Node12Box component86Node10Box component86Node11Box
    .chi (51/128) (by rfl) (by rfl)
    component86Node10_sound component86Node11_sound

private noncomputable def component86Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (3/8), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component86Node13_sound : Sound component86Node13Box :=
  sound_of_literal_split component86Node13Box component86Node9Box component86Node12Box
    .chi (25/64) (by rfl) (by rfl)
    component86Node9_sound component86Node12_sound

private noncomputable def component86Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (3/8), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component86Node14_sound : Sound component86Node14Box :=
  sound_of_literal_split component86Node14Box component86Node6Box component86Node13Box
    .k (45/16) (by rfl) (by rfl)
    component86Node6_sound component86Node13_sound

private noncomputable def component86Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (13/32), chiHi := (53/128) }

set_option maxRecDepth 1000000 in
private theorem component86Node15_sound : Sound component86Node15Box :=
  sound_of_literal_split component86Node15Box leaf4188Box leaf4189Box
    .k (89/32) (by rfl) (by rfl)
    leaf4188FlatSound leaf4189FlatSound

private noncomputable def component86Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (53/128), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component86Node16_sound : Sound component86Node16Box :=
  sound_of_literal_split component86Node16Box leaf4190Box leaf4191Box
    .k (89/32) (by rfl) (by rfl)
    leaf4190FlatSound leaf4191FlatSound

private noncomputable def component86Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (13/32), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component86Node17_sound : Sound component86Node17Box :=
  sound_of_literal_split component86Node17Box component86Node15Box component86Node16Box
    .chi (53/128) (by rfl) (by rfl)
    component86Node15_sound component86Node16_sound

private noncomputable def component86Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (27/64), chiHi := (55/128) }

set_option maxRecDepth 1000000 in
private theorem component86Node18_sound : Sound component86Node18Box :=
  sound_of_literal_split component86Node18Box leaf4192Box leaf4193Box
    .k (89/32) (by rfl) (by rfl)
    leaf4192FlatSound leaf4193FlatSound

private noncomputable def component86Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (55/128), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component86Node19_sound : Sound component86Node19Box :=
  sound_of_literal_split component86Node19Box leaf4194Box leaf4195Box
    .k (89/32) (by rfl) (by rfl)
    leaf4194FlatSound leaf4195FlatSound

private noncomputable def component86Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (27/64), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component86Node20_sound : Sound component86Node20Box :=
  sound_of_literal_split component86Node20Box component86Node18Box component86Node19Box
    .chi (55/128) (by rfl) (by rfl)
    component86Node18_sound component86Node19_sound

private noncomputable def component86Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (13/32), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component86Node21_sound : Sound component86Node21Box :=
  sound_of_literal_split component86Node21Box component86Node17Box component86Node20Box
    .chi (27/64) (by rfl) (by rfl)
    component86Node17_sound component86Node20_sound

private noncomputable def component86Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (13/32), chiHi := (53/128) }

set_option maxRecDepth 1000000 in
private theorem component86Node22_sound : Sound component86Node22Box :=
  sound_of_literal_split component86Node22Box leaf4196Box leaf4197Box
    .k (91/32) (by rfl) (by rfl)
    leaf4196FlatSound leaf4197FlatSound

private noncomputable def component86Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (53/128), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component86Node23_sound : Sound component86Node23Box :=
  sound_of_literal_split component86Node23Box leaf4198Box leaf4199Box
    .k (91/32) (by rfl) (by rfl)
    leaf4198FlatSound leaf4199FlatSound

private noncomputable def component86Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (13/32), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component86Node24_sound : Sound component86Node24Box :=
  sound_of_literal_split component86Node24Box component86Node22Box component86Node23Box
    .chi (53/128) (by rfl) (by rfl)
    component86Node22_sound component86Node23_sound

private noncomputable def component86Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (27/64), chiHi := (55/128) }

set_option maxRecDepth 1000000 in
private theorem component86Node25_sound : Sound component86Node25Box :=
  sound_of_literal_split component86Node25Box leaf4200Box leaf4201Box
    .k (91/32) (by rfl) (by rfl)
    leaf4200FlatSound leaf4201FlatSound

private noncomputable def component86Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (55/128), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component86Node26_sound : Sound component86Node26Box :=
  sound_of_literal_split component86Node26Box leaf4202Box leaf4203Box
    .k (91/32) (by rfl) (by rfl)
    leaf4202FlatSound leaf4203FlatSound

private noncomputable def component86Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (27/64), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component86Node27_sound : Sound component86Node27Box :=
  sound_of_literal_split component86Node27Box component86Node25Box component86Node26Box
    .chi (55/128) (by rfl) (by rfl)
    component86Node25_sound component86Node26_sound

private noncomputable def component86Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (13/32), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component86Node28_sound : Sound component86Node28Box :=
  sound_of_literal_split component86Node28Box component86Node24Box component86Node27Box
    .chi (27/64) (by rfl) (by rfl)
    component86Node24_sound component86Node27_sound

private noncomputable def component86Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (13/32), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component86Node29_sound : Sound component86Node29Box :=
  sound_of_literal_split component86Node29Box component86Node21Box component86Node28Box
    .k (45/16) (by rfl) (by rfl)
    component86Node21_sound component86Node28_sound

private noncomputable def component86Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (3/8), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component86Node30_sound : Sound component86Node30Box :=
  sound_of_literal_split component86Node30Box component86Node14Box component86Node29Box
    .chi (13/32) (by rfl) (by rfl)
    component86Node14_sound component86Node29_sound

private noncomputable def component86Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (3/8), chiHi := (49/128) }

set_option maxRecDepth 1000000 in
private theorem component86Node31_sound : Sound component86Node31Box :=
  sound_of_literal_split component86Node31Box leaf4204Box leaf4205Box
    .k (93/32) (by rfl) (by rfl)
    leaf4204FlatSound leaf4205FlatSound

private noncomputable def component86Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (49/128), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component86Node32_sound : Sound component86Node32Box :=
  sound_of_literal_split component86Node32Box leaf4206Box leaf4207Box
    .k (93/32) (by rfl) (by rfl)
    leaf4206FlatSound leaf4207FlatSound

private noncomputable def component86Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (3/8), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component86Node33_sound : Sound component86Node33Box :=
  sound_of_literal_split component86Node33Box component86Node31Box component86Node32Box
    .chi (49/128) (by rfl) (by rfl)
    component86Node31_sound component86Node32_sound

private noncomputable def component86Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (25/64), chiHi := (51/128) }

set_option maxRecDepth 1000000 in
private theorem component86Node34_sound : Sound component86Node34Box :=
  sound_of_literal_split component86Node34Box leaf4208Box leaf4209Box
    .k (93/32) (by rfl) (by rfl)
    leaf4208FlatSound leaf4209FlatSound

private noncomputable def component86Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (51/128), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component86Node35_sound : Sound component86Node35Box :=
  sound_of_literal_split component86Node35Box leaf4210Box leaf4211Box
    .k (93/32) (by rfl) (by rfl)
    leaf4210FlatSound leaf4211FlatSound

private noncomputable def component86Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (25/64), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component86Node36_sound : Sound component86Node36Box :=
  sound_of_literal_split component86Node36Box component86Node34Box component86Node35Box
    .chi (51/128) (by rfl) (by rfl)
    component86Node34_sound component86Node35_sound

private noncomputable def component86Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (3/8), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component86Node37_sound : Sound component86Node37Box :=
  sound_of_literal_split component86Node37Box component86Node33Box component86Node36Box
    .chi (25/64) (by rfl) (by rfl)
    component86Node33_sound component86Node36_sound

private noncomputable def component86Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (3/8), chiHi := (49/128) }

set_option maxRecDepth 1000000 in
private theorem component86Node38_sound : Sound component86Node38Box :=
  sound_of_literal_split component86Node38Box leaf4212Box leaf4213Box
    .k (95/32) (by rfl) (by rfl)
    leaf4212FlatSound leaf4213FlatSound

private noncomputable def component86Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (49/128), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component86Node39_sound : Sound component86Node39Box :=
  sound_of_literal_split component86Node39Box leaf4214Box leaf4215Box
    .k (95/32) (by rfl) (by rfl)
    leaf4214FlatSound leaf4215FlatSound

private noncomputable def component86Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (3/8), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component86Node40_sound : Sound component86Node40Box :=
  sound_of_literal_split component86Node40Box component86Node38Box component86Node39Box
    .chi (49/128) (by rfl) (by rfl)
    component86Node38_sound component86Node39_sound

private noncomputable def component86Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (25/64), chiHi := (51/128) }

set_option maxRecDepth 1000000 in
private theorem component86Node41_sound : Sound component86Node41Box :=
  sound_of_literal_split component86Node41Box leaf4216Box leaf4217Box
    .k (95/32) (by rfl) (by rfl)
    leaf4216FlatSound leaf4217FlatSound

private noncomputable def component86Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (51/128), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component86Node42_sound : Sound component86Node42Box :=
  sound_of_literal_split component86Node42Box leaf4218Box leaf4219Box
    .k (95/32) (by rfl) (by rfl)
    leaf4218FlatSound leaf4219FlatSound

private noncomputable def component86Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (25/64), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component86Node43_sound : Sound component86Node43Box :=
  sound_of_literal_split component86Node43Box component86Node41Box component86Node42Box
    .chi (51/128) (by rfl) (by rfl)
    component86Node41_sound component86Node42_sound

private noncomputable def component86Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (3/8), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component86Node44_sound : Sound component86Node44Box :=
  sound_of_literal_split component86Node44Box component86Node40Box component86Node43Box
    .chi (25/64) (by rfl) (by rfl)
    component86Node40_sound component86Node43_sound

private noncomputable def component86Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (3/8), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component86Node45_sound : Sound component86Node45Box :=
  sound_of_literal_split component86Node45Box component86Node37Box component86Node44Box
    .k (47/16) (by rfl) (by rfl)
    component86Node37_sound component86Node44_sound

private noncomputable def component86Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (13/32), chiHi := (53/128) }

set_option maxRecDepth 1000000 in
private theorem component86Node46_sound : Sound component86Node46Box :=
  sound_of_literal_split component86Node46Box leaf4220Box leaf4221Box
    .k (93/32) (by rfl) (by rfl)
    leaf4220FlatSound leaf4221FlatSound

private noncomputable def component86Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (53/128), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component86Node47_sound : Sound component86Node47Box :=
  sound_of_literal_split component86Node47Box leaf4222Box leaf4223Box
    .k (93/32) (by rfl) (by rfl)
    leaf4222FlatSound leaf4223FlatSound

private noncomputable def component86Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (13/32), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component86Node48_sound : Sound component86Node48Box :=
  sound_of_literal_split component86Node48Box component86Node46Box component86Node47Box
    .chi (53/128) (by rfl) (by rfl)
    component86Node46_sound component86Node47_sound

private noncomputable def component86Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (27/64), chiHi := (55/128) }

set_option maxRecDepth 1000000 in
private theorem component86Node49_sound : Sound component86Node49Box :=
  sound_of_literal_split component86Node49Box leaf4224Box leaf4225Box
    .k (93/32) (by rfl) (by rfl)
    leaf4224FlatSound leaf4225FlatSound

private noncomputable def component86Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (55/128), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component86Node50_sound : Sound component86Node50Box :=
  sound_of_literal_split component86Node50Box leaf4226Box leaf4227Box
    .k (93/32) (by rfl) (by rfl)
    leaf4226FlatSound leaf4227FlatSound

private noncomputable def component86Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (27/64), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component86Node51_sound : Sound component86Node51Box :=
  sound_of_literal_split component86Node51Box component86Node49Box component86Node50Box
    .chi (55/128) (by rfl) (by rfl)
    component86Node49_sound component86Node50_sound

private noncomputable def component86Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (13/32), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component86Node52_sound : Sound component86Node52Box :=
  sound_of_literal_split component86Node52Box component86Node48Box component86Node51Box
    .chi (27/64) (by rfl) (by rfl)
    component86Node48_sound component86Node51_sound

private noncomputable def component86Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (13/32), chiHi := (53/128) }

set_option maxRecDepth 1000000 in
private theorem component86Node53_sound : Sound component86Node53Box :=
  sound_of_literal_split component86Node53Box leaf4228Box leaf4229Box
    .k (95/32) (by rfl) (by rfl)
    leaf4228FlatSound leaf4229FlatSound

private noncomputable def component86Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (53/128), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component86Node54_sound : Sound component86Node54Box :=
  sound_of_literal_split component86Node54Box leaf4230Box leaf4231Box
    .k (95/32) (by rfl) (by rfl)
    leaf4230FlatSound leaf4231FlatSound

private noncomputable def component86Node55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (13/32), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component86Node55_sound : Sound component86Node55Box :=
  sound_of_literal_split component86Node55Box component86Node53Box component86Node54Box
    .chi (53/128) (by rfl) (by rfl)
    component86Node53_sound component86Node54_sound

private noncomputable def component86Node56Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (27/64), chiHi := (55/128) }

set_option maxRecDepth 1000000 in
private theorem component86Node56_sound : Sound component86Node56Box :=
  sound_of_literal_split component86Node56Box leaf4232Box leaf4233Box
    .k (95/32) (by rfl) (by rfl)
    leaf4232FlatSound leaf4233FlatSound

private noncomputable def component86Node57Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (55/128), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component86Node57_sound : Sound component86Node57Box :=
  sound_of_literal_split component86Node57Box leaf4234Box leaf4235Box
    .k (95/32) (by rfl) (by rfl)
    leaf4234FlatSound leaf4235FlatSound

private noncomputable def component86Node58Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (27/64), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component86Node58_sound : Sound component86Node58Box :=
  sound_of_literal_split component86Node58Box component86Node56Box component86Node57Box
    .chi (55/128) (by rfl) (by rfl)
    component86Node56_sound component86Node57_sound

private noncomputable def component86Node59Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (13/32), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component86Node59_sound : Sound component86Node59Box :=
  sound_of_literal_split component86Node59Box component86Node55Box component86Node58Box
    .chi (27/64) (by rfl) (by rfl)
    component86Node55_sound component86Node58_sound

private noncomputable def component86Node60Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (13/32), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component86Node60_sound : Sound component86Node60Box :=
  sound_of_literal_split component86Node60Box component86Node52Box component86Node59Box
    .k (47/16) (by rfl) (by rfl)
    component86Node52_sound component86Node59_sound

private noncomputable def component86Node61Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (3/8), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component86Node61_sound : Sound component86Node61Box :=
  sound_of_literal_split component86Node61Box component86Node45Box component86Node60Box
    .chi (13/32) (by rfl) (by rfl)
    component86Node45_sound component86Node60_sound

noncomputable def component86Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (3), chiLo := (3/8), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
theorem component86_sound : Sound component86Box :=
  sound_of_literal_split component86Box component86Node30Box component86Node61Box
    .k (23/8) (by rfl) (by rfl)
    component86Node30_sound component86Node61_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
