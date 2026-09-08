import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch8
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

private noncomputable def leaf4236Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (7/16), chiHi := (57/128) }

private noncomputable def leaf4236Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435747/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357140992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (591344095/536870912) }, upper := { exponent := 1, mantissa := (9169/8192) } }, logOuter := sk107LogOuterCertificate, logK := sk107LogKCertificate, logChi := chi267LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715863551/68714281984) } }, logDArg := sk107LogDArgCertificate }

private noncomputable def leaf4236InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf4236LocalValidity :
    LeafFacts leaf4236Box leaf4236Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4236Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357140992) }) = true
      norm_num [leaf4236Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4236CertificateValid :
    WideCertificateValid leaf4236Box leaf4236Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk107ValidityFacts chi267ValidityFacts
    leaf4236LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4236CoverageChecked :
    coverageCheck (innerAD leaf4236Box) leaf4236InnerLog = true := by
  rfl'

private theorem leaf4236InnerLogValid :
    leaf4236InnerLog.Valid 8 (innerAD leaf4236Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf4236CoverageChecked

private noncomputable def leaf4236InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629467/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4236InputLogOnePlusV_eq :
    leaf4236InputLogOnePlusV = outerEnclosure 24
      (leaf4236Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4236RoundedFacts : LeafRoundedFacts 8
    leaf4236Certificate.logOnePlusV leaf4236InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4236InputLogOnePlusV_eq }

private noncomputable def leaf4236Inputs : Inputs :=
  inputsOfCaches globalInput sk107RoundedInputs
    chi267InputQChi innerPair256Input
    leaf4236InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4236LowerChecked :
    lowerCheck 24 leaf4236Box leaf4236Inputs = true := by
  rfl'

private theorem leaf4236CoversExact : CoversExact 8
    leaf4236Box leaf4236Certificate leaf4236InnerLog leaf4236Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk107RoundedFacts chi267RoundedFacts
    innerPair256RoundedFacts leaf4236RoundedFacts (by rfl)

private theorem leaf4236FlatSound : Sound leaf4236Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4236CertificateValid
    leaf4236InnerLogValid leaf4236CoversExact leaf4236LowerChecked

private noncomputable def leaf4237Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (7/16), chiHi := (57/128) }

private noncomputable def leaf4237Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435749/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357111808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (595013885/536870912) }, upper := { exponent := 1, mantissa := (4613/4096) } }, logOuter := sk108LogOuterCertificate, logK := sk108LogKCertificate, logChi := chi267LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715834367/68714223616) } }, logDArg := sk108LogDArgCertificate }

private noncomputable def leaf4237InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf4237LocalValidity :
    LeafFacts leaf4237Box leaf4237Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4237Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357111808) }) = true
      norm_num [leaf4237Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4237CertificateValid :
    WideCertificateValid leaf4237Box leaf4237Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk108ValidityFacts chi267ValidityFacts
    leaf4237LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4237CoverageChecked :
    coverageCheck (innerAD leaf4237Box) leaf4237InnerLog = true := by
  rfl'

private theorem leaf4237InnerLogValid :
    leaf4237InnerLog.Valid 8 (innerAD leaf4237Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf4237CoverageChecked

private noncomputable def leaf4237InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814737/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4237InputLogOnePlusV_eq :
    leaf4237InputLogOnePlusV = outerEnclosure 24
      (leaf4237Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4237RoundedFacts : LeafRoundedFacts 8
    leaf4237Certificate.logOnePlusV leaf4237InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4237InputLogOnePlusV_eq }

private noncomputable def leaf4237Inputs : Inputs :=
  inputsOfCaches globalInput sk108RoundedInputs
    chi267InputQChi innerPair257Input
    leaf4237InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4237LowerChecked :
    lowerCheck 24 leaf4237Box leaf4237Inputs = true := by
  rfl'

private theorem leaf4237CoversExact : CoversExact 8
    leaf4237Box leaf4237Certificate leaf4237InnerLog leaf4237Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk108RoundedFacts chi267RoundedFacts
    innerPair257RoundedFacts leaf4237RoundedFacts (by rfl)

private theorem leaf4237FlatSound : Sound leaf4237Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4237CertificateValid
    leaf4237InnerLogValid leaf4237CoversExact leaf4237LowerChecked

private noncomputable def leaf4238Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (57/128), chiHi := (29/64) }

private noncomputable def leaf4238Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435749/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357095424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (597110909/536870912) }, upper := { exponent := 1, mantissa := (4629/4096) } }, logOuter := sk107LogOuterCertificate, logK := sk107LogKCertificate, logChi := chi268LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715817983/68714190848) } }, logDArg := sk107LogDArgCertificate }

private noncomputable def leaf4238InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf4238LocalValidity :
    LeafFacts leaf4238Box leaf4238Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4238Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357095424) }) = true
      norm_num [leaf4238Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4238CertificateValid :
    WideCertificateValid leaf4238Box leaf4238Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk107ValidityFacts chi268ValidityFacts
    leaf4238LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4238CoverageChecked :
    coverageCheck (innerAD leaf4238Box) leaf4238InnerLog = true := by
  rfl'

private theorem leaf4238InnerLogValid :
    leaf4238InnerLog.Valid 8 (innerAD leaf4238Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf4238CoverageChecked

private noncomputable def leaf4238InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814739/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4238InputLogOnePlusV_eq :
    leaf4238InputLogOnePlusV = outerEnclosure 24
      (leaf4238Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4238RoundedFacts : LeafRoundedFacts 8
    leaf4238Certificate.logOnePlusV leaf4238InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4238InputLogOnePlusV_eq }

private noncomputable def leaf4238Inputs : Inputs :=
  inputsOfCaches globalInput sk107RoundedInputs
    chi268InputQChi innerPair257Input
    leaf4238InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4238LowerChecked :
    lowerCheck 24 leaf4238Box leaf4238Inputs = true := by
  rfl'

private theorem leaf4238CoversExact : CoversExact 8
    leaf4238Box leaf4238Certificate leaf4238InnerLog leaf4238Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk107RoundedFacts chi268RoundedFacts
    innerPair257RoundedFacts leaf4238RoundedFacts (by rfl)

private theorem leaf4238FlatSound : Sound leaf4238Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4238CertificateValid
    leaf4238InnerLogValid leaf4238CoversExact leaf4238LowerChecked

private noncomputable def leaf4239Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (57/128), chiHi := (29/64) }

private noncomputable def leaf4239Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435751/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357065728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (600846231/536870912) }, upper := { exponent := 1, mantissa := (2329/2048) } }, logOuter := sk108LogOuterCertificate, logK := sk108LogKCertificate, logChi := chi268LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715788287/68714131456) } }, logDArg := sk108LogDArgCertificate }

private noncomputable def leaf4239InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf4239LocalValidity :
    LeafFacts leaf4239Box leaf4239Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4239Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357065728) }) = true
      norm_num [leaf4239Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4239CertificateValid :
    WideCertificateValid leaf4239Box leaf4239Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk108ValidityFacts chi268ValidityFacts
    leaf4239LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4239CoverageChecked :
    coverageCheck (innerAD leaf4239Box) leaf4239InnerLog = true := by
  rfl'

private theorem leaf4239InnerLogValid :
    leaf4239InnerLog.Valid 8 (innerAD leaf4239Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf4239CoverageChecked

private noncomputable def leaf4239InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629485/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4239InputLogOnePlusV_eq :
    leaf4239InputLogOnePlusV = outerEnclosure 24
      (leaf4239Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4239RoundedFacts : LeafRoundedFacts 8
    leaf4239Certificate.logOnePlusV leaf4239InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4239InputLogOnePlusV_eq }

private noncomputable def leaf4239Inputs : Inputs :=
  inputsOfCaches globalInput sk108RoundedInputs
    chi268InputQChi innerPair257Input
    leaf4239InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4239LowerChecked :
    lowerCheck 24 leaf4239Box leaf4239Inputs = true := by
  rfl'

private theorem leaf4239CoversExact : CoversExact 8
    leaf4239Box leaf4239Certificate leaf4239InnerLog leaf4239Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk108RoundedFacts chi268RoundedFacts
    innerPair257RoundedFacts leaf4239RoundedFacts (by rfl)

private theorem leaf4239FlatSound : Sound leaf4239Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4239CertificateValid
    leaf4239InnerLogValid leaf4239CoversExact leaf4239LowerChecked

private noncomputable def leaf4240Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (29/64), chiHi := (59/128) }

private noncomputable def leaf4240Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435751/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357049856) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (602877723/536870912) }, upper := { exponent := 1, mantissa := (9347/8192) } }, logOuter := sk107LogOuterCertificate, logK := sk107LogKCertificate, logChi := chi269LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715772415/68714099712) } }, logDArg := sk107LogDArgCertificate }

private noncomputable def leaf4240InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf4240LocalValidity :
    LeafFacts leaf4240Box leaf4240Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4240Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357049856) }) = true
      norm_num [leaf4240Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4240CertificateValid :
    WideCertificateValid leaf4240Box leaf4240Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk107ValidityFacts chi269ValidityFacts
    leaf4240LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4240CoverageChecked :
    coverageCheck (innerAD leaf4240Box) leaf4240InnerLog = true := by
  rfl'

private theorem leaf4240InnerLogValid :
    leaf4240InnerLog.Valid 8 (innerAD leaf4240Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf4240CoverageChecked

private noncomputable def leaf4240InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629489/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4240InputLogOnePlusV_eq :
    leaf4240InputLogOnePlusV = outerEnclosure 24
      (leaf4240Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4240RoundedFacts : LeafRoundedFacts 8
    leaf4240Certificate.logOnePlusV leaf4240InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4240InputLogOnePlusV_eq }

private noncomputable def leaf4240Inputs : Inputs :=
  inputsOfCaches globalInput sk107RoundedInputs
    chi269InputQChi innerPair257Input
    leaf4240InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4240LowerChecked :
    lowerCheck 24 leaf4240Box leaf4240Inputs = true := by
  rfl'

private theorem leaf4240CoversExact : CoversExact 8
    leaf4240Box leaf4240Certificate leaf4240InnerLog leaf4240Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk107RoundedFacts chi269RoundedFacts
    innerPair257RoundedFacts leaf4240RoundedFacts (by rfl)

private theorem leaf4240FlatSound : Sound leaf4240Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4240CertificateValid
    leaf4240InnerLogValid leaf4240CoversExact leaf4240LowerChecked

private noncomputable def leaf4241Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (29/64), chiHi := (59/128) }

private noncomputable def leaf4241Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435753/268435456) }, vSqrt := { lower := (32765/32768), upper := (4908388937/4908145664) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (606678577/536870912) }, upper := { exponent := 1, mantissa := (4703/4096) } }, logOuter := sk108LogOuterCertificate, logK := sk108LogKCertificate, logChi := chi269LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (9816534601/9816291328) } }, logDArg := sk108LogDArgCertificate }

private noncomputable def leaf4241InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf4241LocalValidity :
    LeafFacts leaf4241Box leaf4241Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4241Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4908388937/4908145664) }) = true
      norm_num [leaf4241Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4241CertificateValid :
    WideCertificateValid leaf4241Box leaf4241Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk108ValidityFacts chi269ValidityFacts
    leaf4241LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4241CoverageChecked :
    coverageCheck (innerAD leaf4241Box) leaf4241InnerLog = true := by
  rfl'

private theorem leaf4241InnerLogValid :
    leaf4241InnerLog.Valid 8 (innerAD leaf4241Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf4241CoverageChecked

private noncomputable def leaf4241InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629497/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4241InputLogOnePlusV_eq :
    leaf4241InputLogOnePlusV = outerEnclosure 24
      (leaf4241Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4241RoundedFacts : LeafRoundedFacts 8
    leaf4241Certificate.logOnePlusV leaf4241InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4241InputLogOnePlusV_eq }

private noncomputable def leaf4241Inputs : Inputs :=
  inputsOfCaches globalInput sk108RoundedInputs
    chi269InputQChi innerPair264Input
    leaf4241InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4241LowerChecked :
    lowerCheck 24 leaf4241Box leaf4241Inputs = true := by
  rfl'

private theorem leaf4241CoversExact : CoversExact 8
    leaf4241Box leaf4241Certificate leaf4241InnerLog leaf4241Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk108RoundedFacts chi269RoundedFacts
    innerPair264RoundedFacts leaf4241RoundedFacts (by rfl)

private theorem leaf4241FlatSound : Sound leaf4241Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4241CertificateValid
    leaf4241InnerLogValid leaf4241CoversExact leaf4241LowerChecked

private noncomputable def leaf4242Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (59/128), chiHi := (15/32) }

private noncomputable def leaf4242Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435753/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357004288) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (608644537/536870912) }, upper := { exponent := 1, mantissa := (2359/2048) } }, logOuter := sk107LogOuterCertificate, logK := sk107LogKCertificate, logChi := chi270LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715726847/68714008576) } }, logDArg := sk107LogDArgCertificate }

private noncomputable def leaf4242InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf4242LocalValidity :
    LeafFacts leaf4242Box leaf4242Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4242Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357004288) }) = true
      norm_num [leaf4242Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4242CertificateValid :
    WideCertificateValid leaf4242Box leaf4242Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk107ValidityFacts chi270ValidityFacts
    leaf4242LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4242CoverageChecked :
    coverageCheck (innerAD leaf4242Box) leaf4242InnerLog = true := by
  rfl'

private theorem leaf4242InnerLogValid :
    leaf4242InnerLog.Valid 8 (innerAD leaf4242Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf4242CoverageChecked

private noncomputable def leaf4242InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907375/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4242InputLogOnePlusV_eq :
    leaf4242InputLogOnePlusV = outerEnclosure 24
      (leaf4242Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4242RoundedFacts : LeafRoundedFacts 8
    leaf4242Certificate.logOnePlusV leaf4242InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4242InputLogOnePlusV_eq }

private noncomputable def leaf4242Inputs : Inputs :=
  inputsOfCaches globalInput sk107RoundedInputs
    chi270InputQChi innerPair264Input
    leaf4242InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4242LowerChecked :
    lowerCheck 24 leaf4242Box leaf4242Inputs = true := by
  rfl'

private theorem leaf4242CoversExact : CoversExact 8
    leaf4242Box leaf4242Certificate leaf4242InnerLog leaf4242Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk107RoundedFacts chi270RoundedFacts
    innerPair264RoundedFacts leaf4242RoundedFacts (by rfl)

private theorem leaf4242FlatSound : Sound leaf4242Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4242CertificateValid
    leaf4242InnerLogValid leaf4242CoversExact leaf4242LowerChecked

private noncomputable def leaf4243Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (59/128), chiHi := (15/32) }

private noncomputable def leaf4243Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435755/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34356973568) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (612510923/536870912) }, upper := { exponent := 1, mantissa := (1187/1024) } }, logOuter := sk108LogOuterCertificate, logK := sk108LogKCertificate, logChi := chi270LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715696127/68713947136) } }, logDArg := sk108LogDArgCertificate }

private noncomputable def leaf4243InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf4243LocalValidity :
    LeafFacts leaf4243Box leaf4243Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4243Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34356973568) }) = true
      norm_num [leaf4243Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4243CertificateValid :
    WideCertificateValid leaf4243Box leaf4243Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk108ValidityFacts chi270ValidityFacts
    leaf4243LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4243CoverageChecked :
    coverageCheck (innerAD leaf4243Box) leaf4243InnerLog = true := by
  rfl'

private theorem leaf4243InnerLogValid :
    leaf4243InnerLog.Valid 8 (innerAD leaf4243Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf4243CoverageChecked

private noncomputable def leaf4243InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907377/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4243InputLogOnePlusV_eq :
    leaf4243InputLogOnePlusV = outerEnclosure 24
      (leaf4243Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4243RoundedFacts : LeafRoundedFacts 8
    leaf4243Certificate.logOnePlusV leaf4243InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4243InputLogOnePlusV_eq }

private noncomputable def leaf4243Inputs : Inputs :=
  inputsOfCaches globalInput sk108RoundedInputs
    chi270InputQChi innerPair265Input
    leaf4243InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4243LowerChecked :
    lowerCheck 24 leaf4243Box leaf4243Inputs = true := by
  rfl'

private theorem leaf4243CoversExact : CoversExact 8
    leaf4243Box leaf4243Certificate leaf4243InnerLog leaf4243Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk108RoundedFacts chi270RoundedFacts
    innerPair265RoundedFacts leaf4243RoundedFacts (by rfl)

private theorem leaf4243FlatSound : Sound leaf4243Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4243CertificateValid
    leaf4243InnerLogValid leaf4243CoversExact leaf4243LowerChecked

private noncomputable def leaf4244Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32), chiLo := (7/16), chiHi := (57/128) }

private noncomputable def leaf4244Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435751/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357082624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (598683675/536870912) }, upper := { exponent := 1, mantissa := (9283/8192) } }, logOuter := sk109LogOuterCertificate, logK := sk109LogKCertificate, logChi := chi267LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715805183/68714165248) } }, logDArg := sk109LogDArgCertificate }

private noncomputable def leaf4244InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf4244LocalValidity :
    LeafFacts leaf4244Box leaf4244Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4244Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357082624) }) = true
      norm_num [leaf4244Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4244CertificateValid :
    WideCertificateValid leaf4244Box leaf4244Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk109ValidityFacts chi267ValidityFacts
    leaf4244LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4244CoverageChecked :
    coverageCheck (innerAD leaf4244Box) leaf4244InnerLog = true := by
  rfl'

private theorem leaf4244InnerLogValid :
    leaf4244InnerLog.Valid 8 (innerAD leaf4244Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf4244CoverageChecked

private noncomputable def leaf4244InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629481/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4244InputLogOnePlusV_eq :
    leaf4244InputLogOnePlusV = outerEnclosure 24
      (leaf4244Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4244RoundedFacts : LeafRoundedFacts 8
    leaf4244Certificate.logOnePlusV leaf4244InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4244InputLogOnePlusV_eq }

private noncomputable def leaf4244Inputs : Inputs :=
  inputsOfCaches globalInput sk109RoundedInputs
    chi267InputQChi innerPair257Input
    leaf4244InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4244LowerChecked :
    lowerCheck 24 leaf4244Box leaf4244Inputs = true := by
  rfl'

private theorem leaf4244CoversExact : CoversExact 8
    leaf4244Box leaf4244Certificate leaf4244InnerLog leaf4244Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk109RoundedFacts chi267RoundedFacts
    innerPair257RoundedFacts leaf4244RoundedFacts (by rfl)

private theorem leaf4244FlatSound : Sound leaf4244Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4244CertificateValid
    leaf4244InnerLogValid leaf4244CoversExact leaf4244LowerChecked

private noncomputable def leaf4245Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8), chiLo := (7/16), chiHi := (57/128) }

private noncomputable def leaf4245Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435753/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357053440) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (602353465/536870912) }, upper := { exponent := 1, mantissa := (2335/2048) } }, logOuter := sk110LogOuterCertificate, logK := sk110LogKCertificate, logChi := chi267LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715775999/68714106880) } }, logDArg := sk110LogDArgCertificate }

private noncomputable def leaf4245InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf4245LocalValidity :
    LeafFacts leaf4245Box leaf4245Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4245Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357053440) }) = true
      norm_num [leaf4245Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4245CertificateValid :
    WideCertificateValid leaf4245Box leaf4245Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk110ValidityFacts chi267ValidityFacts
    leaf4245LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4245CoverageChecked :
    coverageCheck (innerAD leaf4245Box) leaf4245InnerLog = true := by
  rfl'

private theorem leaf4245InnerLogValid :
    leaf4245InnerLog.Valid 8 (innerAD leaf4245Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf4245CoverageChecked

private noncomputable def leaf4245InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (726843/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf4245InputLogOnePlusV_eq :
    leaf4245InputLogOnePlusV = outerEnclosure 24
      (leaf4245Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4245RoundedFacts : LeafRoundedFacts 8
    leaf4245Certificate.logOnePlusV leaf4245InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4245InputLogOnePlusV_eq }

private noncomputable def leaf4245Inputs : Inputs :=
  inputsOfCaches globalInput sk110RoundedInputs
    chi267InputQChi innerPair257Input
    leaf4245InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4245LowerChecked :
    lowerCheck 24 leaf4245Box leaf4245Inputs = true := by
  rfl'

private theorem leaf4245CoversExact : CoversExact 8
    leaf4245Box leaf4245Certificate leaf4245InnerLog leaf4245Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk110RoundedFacts chi267RoundedFacts
    innerPair257RoundedFacts leaf4245RoundedFacts (by rfl)

private theorem leaf4245FlatSound : Sound leaf4245Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4245CertificateValid
    leaf4245InnerLogValid leaf4245CoversExact leaf4245LowerChecked

private noncomputable def leaf4246Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32), chiLo := (57/128), chiHi := (29/64) }

private noncomputable def leaf4246Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435753/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357036032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (604581553/536870912) }, upper := { exponent := 1, mantissa := (4687/4096) } }, logOuter := sk109LogOuterCertificate, logK := sk109LogKCertificate, logChi := chi268LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715758591/68714072064) } }, logDArg := sk109LogDArgCertificate }

private noncomputable def leaf4246InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf4246LocalValidity :
    LeafFacts leaf4246Box leaf4246Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4246Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357036032) }) = true
      norm_num [leaf4246Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4246CertificateValid :
    WideCertificateValid leaf4246Box leaf4246Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk109ValidityFacts chi268ValidityFacts
    leaf4246LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4246CoverageChecked :
    coverageCheck (innerAD leaf4246Box) leaf4246InnerLog = true := by
  rfl'

private theorem leaf4246InnerLogValid :
    leaf4246InnerLog.Valid 8 (innerAD leaf4246Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf4246CoverageChecked

private noncomputable def leaf4246InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629493/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4246InputLogOnePlusV_eq :
    leaf4246InputLogOnePlusV = outerEnclosure 24
      (leaf4246Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4246RoundedFacts : LeafRoundedFacts 8
    leaf4246Certificate.logOnePlusV leaf4246InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4246InputLogOnePlusV_eq }

private noncomputable def leaf4246Inputs : Inputs :=
  inputsOfCaches globalInput sk109RoundedInputs
    chi268InputQChi innerPair264Input
    leaf4246InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4246LowerChecked :
    lowerCheck 24 leaf4246Box leaf4246Inputs = true := by
  rfl'

private theorem leaf4246CoversExact : CoversExact 8
    leaf4246Box leaf4246Certificate leaf4246InnerLog leaf4246Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk109RoundedFacts chi268RoundedFacts
    innerPair264RoundedFacts leaf4246RoundedFacts (by rfl)

private theorem leaf4246FlatSound : Sound leaf4246Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4246CertificateValid
    leaf4246InnerLogValid leaf4246CoversExact leaf4246LowerChecked

private noncomputable def leaf4247Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8), chiLo := (57/128), chiHi := (29/64) }

private noncomputable def leaf4247Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435755/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357006336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (608316875/536870912) }, upper := { exponent := 1, mantissa := (1179/1024) } }, logOuter := sk110LogOuterCertificate, logK := sk110LogKCertificate, logChi := chi268LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715728895/68714012672) } }, logDArg := sk110LogDArgCertificate }

private noncomputable def leaf4247InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf4247LocalValidity :
    LeafFacts leaf4247Box leaf4247Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4247Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357006336) }) = true
      norm_num [leaf4247Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4247CertificateValid :
    WideCertificateValid leaf4247Box leaf4247Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk110ValidityFacts chi268ValidityFacts
    leaf4247LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4247CoverageChecked :
    coverageCheck (innerAD leaf4247Box) leaf4247InnerLog = true := by
  rfl'

private theorem leaf4247InnerLogValid :
    leaf4247InnerLog.Valid 8 (innerAD leaf4247Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf4247CoverageChecked

private noncomputable def leaf4247InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907375/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4247InputLogOnePlusV_eq :
    leaf4247InputLogOnePlusV = outerEnclosure 24
      (leaf4247Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4247RoundedFacts : LeafRoundedFacts 8
    leaf4247Certificate.logOnePlusV leaf4247InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4247InputLogOnePlusV_eq }

private noncomputable def leaf4247Inputs : Inputs :=
  inputsOfCaches globalInput sk110RoundedInputs
    chi268InputQChi innerPair264Input
    leaf4247InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4247LowerChecked :
    lowerCheck 24 leaf4247Box leaf4247Inputs = true := by
  rfl'

private theorem leaf4247CoversExact : CoversExact 8
    leaf4247Box leaf4247Certificate leaf4247InnerLog leaf4247Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk110RoundedFacts chi268RoundedFacts
    innerPair264RoundedFacts leaf4247RoundedFacts (by rfl)

private theorem leaf4247FlatSound : Sound leaf4247Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4247CertificateValid
    leaf4247InnerLogValid leaf4247CoversExact leaf4247LowerChecked

private noncomputable def leaf4248Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32), chiLo := (29/64), chiHi := (59/128) }

private noncomputable def leaf4248Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435755/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34356989440) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (610479431/536870912) }, upper := { exponent := 1, mantissa := (9465/8192) } }, logOuter := sk109LogOuterCertificate, logK := sk109LogKCertificate, logChi := chi269LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715711999/68713978880) } }, logDArg := sk109LogDArgCertificate }

private noncomputable def leaf4248InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf4248LocalValidity :
    LeafFacts leaf4248Box leaf4248Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4248Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34356989440) }) = true
      norm_num [leaf4248Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4248CertificateValid :
    WideCertificateValid leaf4248Box leaf4248Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk109ValidityFacts chi269ValidityFacts
    leaf4248LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4248CoverageChecked :
    coverageCheck (innerAD leaf4248Box) leaf4248InnerLog = true := by
  rfl'

private theorem leaf4248InnerLogValid :
    leaf4248InnerLog.Valid 8 (innerAD leaf4248Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf4248CoverageChecked

private noncomputable def leaf4248InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (181711/262144) }

set_option maxRecDepth 1000000 in
private theorem leaf4248InputLogOnePlusV_eq :
    leaf4248InputLogOnePlusV = outerEnclosure 24
      (leaf4248Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4248RoundedFacts : LeafRoundedFacts 8
    leaf4248Certificate.logOnePlusV leaf4248InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4248InputLogOnePlusV_eq }

private noncomputable def leaf4248Inputs : Inputs :=
  inputsOfCaches globalInput sk109RoundedInputs
    chi269InputQChi innerPair264Input
    leaf4248InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4248LowerChecked :
    lowerCheck 24 leaf4248Box leaf4248Inputs = true := by
  rfl'

private theorem leaf4248CoversExact : CoversExact 8
    leaf4248Box leaf4248Certificate leaf4248InnerLog leaf4248Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk109RoundedFacts chi269RoundedFacts
    innerPair264RoundedFacts leaf4248RoundedFacts (by rfl)

private theorem leaf4248FlatSound : Sound leaf4248Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4248CertificateValid
    leaf4248InnerLogValid leaf4248CoversExact leaf4248LowerChecked

private noncomputable def leaf4249Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8), chiLo := (29/64), chiHi := (59/128) }

private noncomputable def leaf4249Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435757/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34356959232) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (614280285/536870912) }, upper := { exponent := 1, mantissa := (2381/2048) } }, logOuter := sk110LogOuterCertificate, logK := sk110LogKCertificate, logChi := chi269LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715681791/68713918464) } }, logDArg := sk110LogDArgCertificate }

private noncomputable def leaf4249InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf4249LocalValidity :
    LeafFacts leaf4249Box leaf4249Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4249Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34356959232) }) = true
      norm_num [leaf4249Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4249CertificateValid :
    WideCertificateValid leaf4249Box leaf4249Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk110ValidityFacts chi269ValidityFacts
    leaf4249LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4249CoverageChecked :
    coverageCheck (innerAD leaf4249Box) leaf4249InnerLog = true := by
  rfl'

private theorem leaf4249InnerLogValid :
    leaf4249InnerLog.Valid 8 (innerAD leaf4249Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf4249CoverageChecked

private noncomputable def leaf4249InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629511/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4249InputLogOnePlusV_eq :
    leaf4249InputLogOnePlusV = outerEnclosure 24
      (leaf4249Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4249RoundedFacts : LeafRoundedFacts 8
    leaf4249Certificate.logOnePlusV leaf4249InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4249InputLogOnePlusV_eq }

private noncomputable def leaf4249Inputs : Inputs :=
  inputsOfCaches globalInput sk110RoundedInputs
    chi269InputQChi innerPair265Input
    leaf4249InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4249LowerChecked :
    lowerCheck 24 leaf4249Box leaf4249Inputs = true := by
  rfl'

private theorem leaf4249CoversExact : CoversExact 8
    leaf4249Box leaf4249Certificate leaf4249InnerLog leaf4249Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk110RoundedFacts chi269RoundedFacts
    innerPair265RoundedFacts leaf4249RoundedFacts (by rfl)

private theorem leaf4249FlatSound : Sound leaf4249Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4249CertificateValid
    leaf4249InnerLogValid leaf4249CoversExact leaf4249LowerChecked

private noncomputable def leaf4250Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32), chiLo := (59/128), chiHi := (15/32) }

private noncomputable def leaf4250Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435757/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34356942848) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (616377309/536870912) }, upper := { exponent := 1, mantissa := (2389/2048) } }, logOuter := sk109LogOuterCertificate, logK := sk109LogKCertificate, logChi := chi270LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715665407/68713885696) } }, logDArg := sk109LogDArgCertificate }

private noncomputable def leaf4250InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf4250LocalValidity :
    LeafFacts leaf4250Box leaf4250Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4250Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34356942848) }) = true
      norm_num [leaf4250Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4250CertificateValid :
    WideCertificateValid leaf4250Box leaf4250Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk109ValidityFacts chi270ValidityFacts
    leaf4250LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4250CoverageChecked :
    coverageCheck (innerAD leaf4250Box) leaf4250InnerLog = true := by
  rfl'

private theorem leaf4250InnerLogValid :
    leaf4250InnerLog.Valid 8 (innerAD leaf4250Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf4250CoverageChecked

private noncomputable def leaf4250InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629515/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4250InputLogOnePlusV_eq :
    leaf4250InputLogOnePlusV = outerEnclosure 24
      (leaf4250Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4250RoundedFacts : LeafRoundedFacts 8
    leaf4250Certificate.logOnePlusV leaf4250InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4250InputLogOnePlusV_eq }

private noncomputable def leaf4250Inputs : Inputs :=
  inputsOfCaches globalInput sk109RoundedInputs
    chi270InputQChi innerPair265Input
    leaf4250InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4250LowerChecked :
    lowerCheck 24 leaf4250Box leaf4250Inputs = true := by
  rfl'

private theorem leaf4250CoversExact : CoversExact 8
    leaf4250Box leaf4250Certificate leaf4250InnerLog leaf4250Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk109RoundedFacts chi270RoundedFacts
    innerPair265RoundedFacts leaf4250RoundedFacts (by rfl)

private theorem leaf4250FlatSound : Sound leaf4250Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4250CertificateValid
    leaf4250InnerLogValid leaf4250CoversExact leaf4250LowerChecked

private noncomputable def leaf4251Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8), chiLo := (59/128), chiHi := (15/32) }

private noncomputable def leaf4251Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435759/268435456) }, vSqrt := { lower := (32765/32768), upper := (158335127/158326784) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (620243695/536870912) }, upper := { exponent := 1, mantissa := (601/512) } }, logOuter := sk110LogOuterCertificate, logK := sk110LogKCertificate, logChi := chi270LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (316661911/316653568) } }, logDArg := sk110LogDArgCertificate }

private noncomputable def leaf4251InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf4251LocalValidity :
    LeafFacts leaf4251Box leaf4251Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4251Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (158335127/158326784) }) = true
      norm_num [leaf4251Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4251CertificateValid :
    WideCertificateValid leaf4251Box leaf4251Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk110ValidityFacts chi270ValidityFacts
    leaf4251LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4251CoverageChecked :
    coverageCheck (innerAD leaf4251Box) leaf4251InnerLog = true := by
  rfl'

private theorem leaf4251InnerLogValid :
    leaf4251InnerLog.Valid 8 (innerAD leaf4251Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf4251CoverageChecked

private noncomputable def leaf4251InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629523/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4251InputLogOnePlusV_eq :
    leaf4251InputLogOnePlusV = outerEnclosure 24
      (leaf4251Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4251RoundedFacts : LeafRoundedFacts 8
    leaf4251Certificate.logOnePlusV leaf4251InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4251InputLogOnePlusV_eq }

private noncomputable def leaf4251Inputs : Inputs :=
  inputsOfCaches globalInput sk110RoundedInputs
    chi270InputQChi innerPair265Input
    leaf4251InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4251LowerChecked :
    lowerCheck 24 leaf4251Box leaf4251Inputs = true := by
  rfl'

private theorem leaf4251CoversExact : CoversExact 8
    leaf4251Box leaf4251Certificate leaf4251InnerLog leaf4251Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk110RoundedFacts chi270RoundedFacts
    innerPair265RoundedFacts leaf4251RoundedFacts (by rfl)

private theorem leaf4251FlatSound : Sound leaf4251Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4251CertificateValid
    leaf4251InnerLogValid leaf4251CoversExact leaf4251LowerChecked

private noncomputable def leaf4252Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (15/32), chiHi := (61/128) }

private noncomputable def leaf4252Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217939/134217728) }, vSqrt := { lower := (32765/32768), upper := (17179377663/17178463744) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (307189231/268435456) }, upper := { exponent := 1, mantissa := (4793/4096) } }, logOuter := sk95LogOuterCertificate, logK := sk95LogKCertificate, logChi := chi271LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (34357841407/34356927488) } }, logDArg := sk95LogDArgCertificate }

private noncomputable def leaf4252InnerLog : WideLogData :=
  innerPair579Data

set_option maxRecDepth 1000000 in
private theorem leaf4252LocalValidity :
    LeafFacts leaf4252Box leaf4252Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4252Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (17179377663/17178463744) }) = true
      norm_num [leaf4252Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4252CertificateValid :
    WideCertificateValid leaf4252Box leaf4252Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk95ValidityFacts chi271ValidityFacts
    leaf4252LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4252CoverageChecked :
    coverageCheck (innerAD leaf4252Box) leaf4252InnerLog = true := by
  rfl'

private theorem leaf4252InnerLogValid :
    leaf4252InnerLog.Valid 8 (innerAD leaf4252Box) :=
  wideLogDataValid_of_cachedCheck endpoint300PositiveFacts
    endpoint301PositiveFacts.valid leaf4252CoverageChecked

private noncomputable def leaf4252InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629527/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4252InputLogOnePlusV_eq :
    leaf4252InputLogOnePlusV = outerEnclosure 24
      (leaf4252Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4252RoundedFacts : LeafRoundedFacts 8
    leaf4252Certificate.logOnePlusV leaf4252InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4252InputLogOnePlusV_eq }

private noncomputable def leaf4252Inputs : Inputs :=
  inputsOfCaches globalInput sk95RoundedInputs
    chi271InputQChi innerPair579Input
    leaf4252InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4252LowerChecked :
    lowerCheck 24 leaf4252Box leaf4252Inputs = true := by
  rfl'

private theorem leaf4252CoversExact : CoversExact 8
    leaf4252Box leaf4252Certificate leaf4252InnerLog leaf4252Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk95RoundedFacts chi271RoundedFacts
    innerPair579RoundedFacts leaf4252RoundedFacts (by rfl)

private theorem leaf4252FlatSound : Sound leaf4252Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4252CertificateValid
    leaf4252InnerLogValid leaf4252CoversExact leaf4252LowerChecked

private noncomputable def leaf4253Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (61/128), chiHi := (31/64) }

private noncomputable def leaf4253Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217941/134217728) }, vSqrt := { lower := (32765/32768), upper := (17179377663/17178440704) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (310072637/268435456) }, upper := { exponent := 1, mantissa := (2419/2048) } }, logOuter := sk95LogOuterCertificate, logK := sk95LogKCertificate, logChi := chi272LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (34357818367/34356881408) } }, logDArg := sk95LogDArgCertificate }

private noncomputable def leaf4253InnerLog : WideLogData :=
  innerPair580Data

set_option maxRecDepth 1000000 in
private theorem leaf4253LocalValidity :
    LeafFacts leaf4253Box leaf4253Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4253Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (17179377663/17178440704) }) = true
      norm_num [leaf4253Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4253CertificateValid :
    WideCertificateValid leaf4253Box leaf4253Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk95ValidityFacts chi272ValidityFacts
    leaf4253LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4253CoverageChecked :
    coverageCheck (innerAD leaf4253Box) leaf4253InnerLog = true := by
  rfl'

private theorem leaf4253InnerLogValid :
    leaf4253InnerLog.Valid 8 (innerAD leaf4253Box) :=
  wideLogDataValid_of_cachedCheck endpoint302PositiveFacts
    endpoint303PositiveFacts.valid leaf4253CoverageChecked

private noncomputable def leaf4253InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814769/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4253InputLogOnePlusV_eq :
    leaf4253InputLogOnePlusV = outerEnclosure 24
      (leaf4253Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4253RoundedFacts : LeafRoundedFacts 8
    leaf4253Certificate.logOnePlusV leaf4253InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4253InputLogOnePlusV_eq }

private noncomputable def leaf4253Inputs : Inputs :=
  inputsOfCaches globalInput sk95RoundedInputs
    chi272InputQChi innerPair580Input
    leaf4253InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4253LowerChecked :
    lowerCheck 24 leaf4253Box leaf4253Inputs = true := by
  rfl'

private theorem leaf4253CoversExact : CoversExact 8
    leaf4253Box leaf4253Certificate leaf4253InnerLog leaf4253Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk95RoundedFacts chi272RoundedFacts
    innerPair580RoundedFacts leaf4253RoundedFacts (by rfl)

private theorem leaf4253FlatSound : Sound leaf4253Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4253CertificateValid
    leaf4253InnerLogValid leaf4253CoversExact leaf4253LowerChecked

private noncomputable def leaf4254Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (31/64), chiHi := (63/128) }

private noncomputable def leaf4254Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217943/134217728) }, vSqrt := { lower := (32765/32768), upper := (17179377663/17178417664) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (312956043/268435456) }, upper := { exponent := 1, mantissa := (4883/4096) } }, logOuter := sk95LogOuterCertificate, logK := sk95LogKCertificate, logChi := chi273LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (34357795327/34356835328) } }, logDArg := sk95LogDArgCertificate }

private noncomputable def leaf4254InnerLog : WideLogData :=
  innerPair567Data

set_option maxRecDepth 1000000 in
private theorem leaf4254LocalValidity :
    LeafFacts leaf4254Box leaf4254Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4254Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (17179377663/17178417664) }) = true
      norm_num [leaf4254Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4254CertificateValid :
    WideCertificateValid leaf4254Box leaf4254Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk95ValidityFacts chi273ValidityFacts
    leaf4254LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4254CoverageChecked :
    coverageCheck (innerAD leaf4254Box) leaf4254InnerLog = true := by
  rfl'

private theorem leaf4254InnerLogValid :
    leaf4254InnerLog.Valid 8 (innerAD leaf4254Box) :=
  wideLogDataValid_of_cachedCheck endpoint296PositiveFacts
    endpoint304PositiveFacts.valid leaf4254CoverageChecked

private noncomputable def leaf4254InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814775/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4254InputLogOnePlusV_eq :
    leaf4254InputLogOnePlusV = outerEnclosure 24
      (leaf4254Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4254RoundedFacts : LeafRoundedFacts 8
    leaf4254Certificate.logOnePlusV leaf4254InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4254InputLogOnePlusV_eq }

private noncomputable def leaf4254Inputs : Inputs :=
  inputsOfCaches globalInput sk95RoundedInputs
    chi273InputQChi innerPair567Input
    leaf4254InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4254LowerChecked :
    lowerCheck 24 leaf4254Box leaf4254Inputs = true := by
  rfl'

private theorem leaf4254CoversExact : CoversExact 8
    leaf4254Box leaf4254Certificate leaf4254InnerLog leaf4254Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk95RoundedFacts chi273RoundedFacts
    innerPair567RoundedFacts leaf4254RoundedFacts (by rfl)

private theorem leaf4254FlatSound : Sound leaf4254Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4254CertificateValid
    leaf4254InnerLogValid leaf4254CoversExact leaf4254LowerChecked

private noncomputable def leaf4255Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (63/128), chiHi := (1/2) }

private noncomputable def leaf4255Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217945/134217728) }, vSqrt := { lower := (32765/32768), upper := (17179377663/17178394624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (315839449/268435456) }, upper := { exponent := 1, mantissa := (77/64) } }, logOuter := sk95LogOuterCertificate, logK := sk95LogKCertificate, logChi := chi274LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (34357772287/34356789248) } }, logDArg := sk95LogDArgCertificate }

private noncomputable def leaf4255InnerLog : WideLogData :=
  innerPair570Data

set_option maxRecDepth 1000000 in
private theorem leaf4255LocalValidity :
    LeafFacts leaf4255Box leaf4255Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4255Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (17179377663/17178394624) }) = true
      norm_num [leaf4255Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4255CertificateValid :
    WideCertificateValid leaf4255Box leaf4255Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk95ValidityFacts chi274ValidityFacts
    leaf4255LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4255CoverageChecked :
    coverageCheck (innerAD leaf4255Box) leaf4255InnerLog = true := by
  rfl'

private theorem leaf4255InnerLogValid :
    leaf4255InnerLog.Valid 8 (innerAD leaf4255Box) :=
  wideLogDataValid_of_cachedCheck endpoint297PositiveFacts
    endpoint305PositiveFacts.valid leaf4255CoverageChecked

private noncomputable def leaf4255InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629561/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4255InputLogOnePlusV_eq :
    leaf4255InputLogOnePlusV = outerEnclosure 24
      (leaf4255Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4255RoundedFacts : LeafRoundedFacts 8
    leaf4255Certificate.logOnePlusV leaf4255InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4255InputLogOnePlusV_eq }

private noncomputable def leaf4255Inputs : Inputs :=
  inputsOfCaches globalInput sk95RoundedInputs
    chi274InputQChi innerPair570Input
    leaf4255InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4255LowerChecked :
    lowerCheck 24 leaf4255Box leaf4255Inputs = true := by
  rfl'

private theorem leaf4255CoversExact : CoversExact 8
    leaf4255Box leaf4255Certificate leaf4255InnerLog leaf4255Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk95RoundedFacts chi274RoundedFacts
    innerPair570RoundedFacts leaf4255RoundedFacts (by rfl)

private theorem leaf4255FlatSound : Sound leaf4255Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4255CertificateValid
    leaf4255InnerLogValid leaf4255CoversExact leaf4255LowerChecked

private noncomputable def leaf4256Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32), chiLo := (15/32), chiHi := (61/128) }

private noncomputable def leaf4256Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435759/268435456) }, vSqrt := { lower := (32765/32768), upper := (1108345889/1108286976) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (622275187/536870912) }, upper := { exponent := 1, mantissa := (9647/8192) } }, logOuter := sk109LogOuterCertificate, logK := sk109LogKCertificate, logChi := chi271LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (2216632865/2216573952) } }, logDArg := sk109LogDArgCertificate }

private noncomputable def leaf4256InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf4256LocalValidity :
    LeafFacts leaf4256Box leaf4256Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4256Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (1108345889/1108286976) }) = true
      norm_num [leaf4256Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4256CertificateValid :
    WideCertificateValid leaf4256Box leaf4256Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk109ValidityFacts chi271ValidityFacts
    leaf4256LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4256CoverageChecked :
    coverageCheck (innerAD leaf4256Box) leaf4256InnerLog = true := by
  rfl'

private theorem leaf4256InnerLogValid :
    leaf4256InnerLog.Valid 8 (innerAD leaf4256Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf4256CoverageChecked

private noncomputable def leaf4256InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629527/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4256InputLogOnePlusV_eq :
    leaf4256InputLogOnePlusV = outerEnclosure 24
      (leaf4256Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4256RoundedFacts : LeafRoundedFacts 8
    leaf4256Certificate.logOnePlusV leaf4256InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4256InputLogOnePlusV_eq }

private noncomputable def leaf4256Inputs : Inputs :=
  inputsOfCaches globalInput sk109RoundedInputs
    chi271InputQChi innerPair272Input
    leaf4256InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4256LowerChecked :
    lowerCheck 24 leaf4256Box leaf4256Inputs = true := by
  rfl'

private theorem leaf4256CoversExact : CoversExact 8
    leaf4256Box leaf4256Certificate leaf4256InnerLog leaf4256Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk109RoundedFacts chi271RoundedFacts
    innerPair272RoundedFacts leaf4256RoundedFacts (by rfl)

private theorem leaf4256FlatSound : Sound leaf4256Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4256CertificateValid
    leaf4256InnerLogValid leaf4256CoversExact leaf4256LowerChecked

private noncomputable def leaf4257Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8), chiLo := (15/32), chiHi := (61/128) }

private noncomputable def leaf4257Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435761/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34356865024) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (626207105/536870912) }, upper := { exponent := 1, mantissa := (2427/2048) } }, logOuter := sk110LogOuterCertificate, logK := sk110LogKCertificate, logChi := chi271LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715587583/68713730048) } }, logDArg := sk110LogDArgCertificate }

private noncomputable def leaf4257InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf4257LocalValidity :
    LeafFacts leaf4257Box leaf4257Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4257Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34356865024) }) = true
      norm_num [leaf4257Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4257CertificateValid :
    WideCertificateValid leaf4257Box leaf4257Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk110ValidityFacts chi271ValidityFacts
    leaf4257LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4257CoverageChecked :
    coverageCheck (innerAD leaf4257Box) leaf4257InnerLog = true := by
  rfl'

private theorem leaf4257InnerLogValid :
    leaf4257InnerLog.Valid 8 (innerAD leaf4257Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf4257CoverageChecked

private noncomputable def leaf4257InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814767/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4257InputLogOnePlusV_eq :
    leaf4257InputLogOnePlusV = outerEnclosure 24
      (leaf4257Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4257RoundedFacts : LeafRoundedFacts 8
    leaf4257Certificate.logOnePlusV leaf4257InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4257InputLogOnePlusV_eq }

private noncomputable def leaf4257Inputs : Inputs :=
  inputsOfCaches globalInput sk110RoundedInputs
    chi271InputQChi innerPair272Input
    leaf4257InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4257LowerChecked :
    lowerCheck 24 leaf4257Box leaf4257Inputs = true := by
  rfl'

private theorem leaf4257CoversExact : CoversExact 8
    leaf4257Box leaf4257Certificate leaf4257InnerLog leaf4257Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk110RoundedFacts chi271RoundedFacts
    innerPair272RoundedFacts leaf4257RoundedFacts (by rfl)

private theorem leaf4257FlatSound : Sound leaf4257Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4257CertificateValid
    leaf4257InnerLogValid leaf4257CoversExact leaf4257LowerChecked

private noncomputable def leaf4258Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (61/128), chiHi := (31/64) }

private noncomputable def leaf4258Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217943/134217728) }, vSqrt := { lower := (32765/32768), upper := (5726459221/5726136320) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (314070087/268435456) }, upper := { exponent := 1, mantissa := (1225/1024) } }, logOuter := sk96LogOuterCertificate, logK := sk96LogKCertificate, logChi := chi272LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (11452595541/11452272640) } }, logDArg := sk96LogDArgCertificate }

private noncomputable def leaf4258InnerLog : WideLogData :=
  innerPair591Data

set_option maxRecDepth 1000000 in
private theorem leaf4258LocalValidity :
    LeafFacts leaf4258Box leaf4258Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4258Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (5726459221/5726136320) }) = true
      norm_num [leaf4258Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4258CertificateValid :
    WideCertificateValid leaf4258Box leaf4258Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk96ValidityFacts chi272ValidityFacts
    leaf4258LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4258CoverageChecked :
    coverageCheck (innerAD leaf4258Box) leaf4258InnerLog = true := by
  rfl'

private theorem leaf4258InnerLogValid :
    leaf4258InnerLog.Valid 8 (innerAD leaf4258Box) :=
  wideLogDataValid_of_cachedCheck endpoint306PositiveFacts
    endpoint307PositiveFacts.valid leaf4258CoverageChecked

private noncomputable def leaf4258InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814777/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4258InputLogOnePlusV_eq :
    leaf4258InputLogOnePlusV = outerEnclosure 24
      (leaf4258Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4258RoundedFacts : LeafRoundedFacts 8
    leaf4258Certificate.logOnePlusV leaf4258InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4258InputLogOnePlusV_eq }

private noncomputable def leaf4258Inputs : Inputs :=
  inputsOfCaches globalInput sk96RoundedInputs
    chi272InputQChi innerPair591Input
    leaf4258InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4258LowerChecked :
    lowerCheck 24 leaf4258Box leaf4258Inputs = true := by
  rfl'

private theorem leaf4258CoversExact : CoversExact 8
    leaf4258Box leaf4258Certificate leaf4258InnerLog leaf4258Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk96RoundedFacts chi272RoundedFacts
    innerPair591RoundedFacts leaf4258RoundedFacts (by rfl)

private theorem leaf4258FlatSound : Sound leaf4258Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4258CertificateValid
    leaf4258InnerLogValid leaf4258CoversExact leaf4258LowerChecked

private noncomputable def leaf4259Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (31/64), chiHi := (63/128) }

private noncomputable def leaf4259Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217945/134217728) }, vSqrt := { lower := (32765/32768), upper := (17179377663/17178385408) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (317019025/268435456) }, upper := { exponent := 1, mantissa := (2473/2048) } }, logOuter := sk96LogOuterCertificate, logK := sk96LogKCertificate, logChi := chi273LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (34357763071/34356770816) } }, logDArg := sk96LogDArgCertificate }

private noncomputable def leaf4259InnerLog : WideLogData :=
  innerPair577Data

set_option maxRecDepth 1000000 in
private theorem leaf4259LocalValidity :
    LeafFacts leaf4259Box leaf4259Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4259Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (17179377663/17178385408) }) = true
      norm_num [leaf4259Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4259CertificateValid :
    WideCertificateValid leaf4259Box leaf4259Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk96ValidityFacts chi273ValidityFacts
    leaf4259LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4259CoverageChecked :
    coverageCheck (innerAD leaf4259Box) leaf4259InnerLog = true := by
  rfl'

private theorem leaf4259InnerLogValid :
    leaf4259InnerLog.Valid 8 (innerAD leaf4259Box) :=
  wideLogDataValid_of_cachedCheck endpoint299PositiveFacts
    endpoint308PositiveFacts.valid leaf4259CoverageChecked

private noncomputable def leaf4259InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629565/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4259InputLogOnePlusV_eq :
    leaf4259InputLogOnePlusV = outerEnclosure 24
      (leaf4259Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4259RoundedFacts : LeafRoundedFacts 8
    leaf4259Certificate.logOnePlusV leaf4259InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4259InputLogOnePlusV_eq }

private noncomputable def leaf4259Inputs : Inputs :=
  inputsOfCaches globalInput sk96RoundedInputs
    chi273InputQChi innerPair577Input
    leaf4259InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4259LowerChecked :
    lowerCheck 24 leaf4259Box leaf4259Inputs = true := by
  rfl'

private theorem leaf4259CoversExact : CoversExact 8
    leaf4259Box leaf4259Certificate leaf4259InnerLog leaf4259Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk96RoundedFacts chi273RoundedFacts
    innerPair577RoundedFacts leaf4259RoundedFacts (by rfl)

private theorem leaf4259FlatSound : Sound leaf4259Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4259CertificateValid
    leaf4259InnerLogValid leaf4259CoversExact leaf4259LowerChecked

private noncomputable def leaf4260Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (63/128), chiHi := (1/2) }

private noncomputable def leaf4260Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217947/134217728) }, vSqrt := { lower := (32765/32768), upper := (17179377663/17178361856) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (319967963/268435456) }, upper := { exponent := 1, mantissa := (39/32) } }, logOuter := sk96LogOuterCertificate, logK := sk96LogKCertificate, logChi := chi274LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (34357739519/34356723712) } }, logDArg := sk96LogDArgCertificate }

private noncomputable def leaf4260InnerLog : WideLogData :=
  innerPair278Data

set_option maxRecDepth 1000000 in
private theorem leaf4260LocalValidity :
    LeafFacts leaf4260Box leaf4260Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4260Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (17179377663/17178361856) }) = true
      norm_num [leaf4260Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4260CertificateValid :
    WideCertificateValid leaf4260Box leaf4260Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk96ValidityFacts chi274ValidityFacts
    leaf4260LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4260CoverageChecked :
    coverageCheck (innerAD leaf4260Box) leaf4260InnerLog = true := by
  rfl'

private theorem leaf4260InnerLogValid :
    leaf4260InnerLog.Valid 8 (innerAD leaf4260Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint78PositiveFacts.valid leaf4260CoverageChecked

private noncomputable def leaf4260InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629577/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4260InputLogOnePlusV_eq :
    leaf4260InputLogOnePlusV = outerEnclosure 24
      (leaf4260Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4260RoundedFacts : LeafRoundedFacts 8
    leaf4260Certificate.logOnePlusV leaf4260InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4260InputLogOnePlusV_eq }

private noncomputable def leaf4260Inputs : Inputs :=
  inputsOfCaches globalInput sk96RoundedInputs
    chi274InputQChi innerPair278Input
    leaf4260InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4260LowerChecked :
    lowerCheck 24 leaf4260Box leaf4260Inputs = true := by
  rfl'

private theorem leaf4260CoversExact : CoversExact 8
    leaf4260Box leaf4260Certificate leaf4260InnerLog leaf4260Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk96RoundedFacts chi274RoundedFacts
    innerPair278RoundedFacts leaf4260RoundedFacts (by rfl)

private theorem leaf4260FlatSound : Sound leaf4260Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4260CertificateValid
    leaf4260InnerLogValid leaf4260CoversExact leaf4260LowerChecked

private noncomputable def leaf4261Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32), chiLo := (7/16), chiHi := (57/128) }

private noncomputable def leaf4261Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435755/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357024256) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (606023255/536870912) }, upper := { exponent := 1, mantissa := (9397/8192) } }, logOuter := sk111LogOuterCertificate, logK := sk111LogKCertificate, logChi := chi267LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715746815/68714048512) } }, logDArg := sk111LogDArgCertificate }

private noncomputable def leaf4261InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf4261LocalValidity :
    LeafFacts leaf4261Box leaf4261Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4261Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357024256) }) = true
      norm_num [leaf4261Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4261CertificateValid :
    WideCertificateValid leaf4261Box leaf4261Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk111ValidityFacts chi267ValidityFacts
    leaf4261LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4261CoverageChecked :
    coverageCheck (innerAD leaf4261Box) leaf4261InnerLog = true := by
  rfl'

private theorem leaf4261InnerLogValid :
    leaf4261InnerLog.Valid 8 (innerAD leaf4261Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf4261CoverageChecked

private noncomputable def leaf4261InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629495/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4261InputLogOnePlusV_eq :
    leaf4261InputLogOnePlusV = outerEnclosure 24
      (leaf4261Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4261RoundedFacts : LeafRoundedFacts 8
    leaf4261Certificate.logOnePlusV leaf4261InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4261InputLogOnePlusV_eq }

private noncomputable def leaf4261Inputs : Inputs :=
  inputsOfCaches globalInput sk111RoundedInputs
    chi267InputQChi innerPair264Input
    leaf4261InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4261LowerChecked :
    lowerCheck 24 leaf4261Box leaf4261Inputs = true := by
  rfl'

private theorem leaf4261CoversExact : CoversExact 8
    leaf4261Box leaf4261Certificate leaf4261InnerLog leaf4261Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk111RoundedFacts chi267RoundedFacts
    innerPair264RoundedFacts leaf4261RoundedFacts (by rfl)

private theorem leaf4261FlatSound : Sound leaf4261Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4261CertificateValid
    leaf4261InnerLogValid leaf4261CoversExact leaf4261LowerChecked

private noncomputable def leaf4262Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16), chiLo := (7/16), chiHi := (57/128) }

private noncomputable def leaf4262Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435757/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34356995072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (609693045/536870912) }, upper := { exponent := 1, mantissa := (4727/4096) } }, logOuter := sk112LogOuterCertificate, logK := sk112LogKCertificate, logChi := chi267LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715717631/68713990144) } }, logDArg := sk112LogDArgCertificate }

private noncomputable def leaf4262InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf4262LocalValidity :
    LeafFacts leaf4262Box leaf4262Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4262Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34356995072) }) = true
      norm_num [leaf4262Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4262CertificateValid :
    WideCertificateValid leaf4262Box leaf4262Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk112ValidityFacts chi267ValidityFacts
    leaf4262LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4262CoverageChecked :
    coverageCheck (innerAD leaf4262Box) leaf4262InnerLog = true := by
  rfl'

private theorem leaf4262InnerLogValid :
    leaf4262InnerLog.Valid 8 (innerAD leaf4262Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf4262CoverageChecked

private noncomputable def leaf4262InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629503/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4262InputLogOnePlusV_eq :
    leaf4262InputLogOnePlusV = outerEnclosure 24
      (leaf4262Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4262RoundedFacts : LeafRoundedFacts 8
    leaf4262Certificate.logOnePlusV leaf4262InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4262InputLogOnePlusV_eq }

private noncomputable def leaf4262Inputs : Inputs :=
  inputsOfCaches globalInput sk112RoundedInputs
    chi267InputQChi innerPair264Input
    leaf4262InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4262LowerChecked :
    lowerCheck 24 leaf4262Box leaf4262Inputs = true := by
  rfl'

private theorem leaf4262CoversExact : CoversExact 8
    leaf4262Box leaf4262Certificate leaf4262InnerLog leaf4262Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk112RoundedFacts chi267RoundedFacts
    innerPair264RoundedFacts leaf4262RoundedFacts (by rfl)

private theorem leaf4262FlatSound : Sound leaf4262Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4262CertificateValid
    leaf4262InnerLogValid leaf4262CoversExact leaf4262LowerChecked

private noncomputable def leaf4263Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32), chiLo := (57/128), chiHi := (29/64) }

private noncomputable def leaf4263Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435757/268435456) }, vSqrt := { lower := (32765/32768), upper := (4908388937/4908139520) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (612052197/536870912) }, upper := { exponent := 1, mantissa := (4745/4096) } }, logOuter := sk111LogOuterCertificate, logK := sk111LogKCertificate, logChi := chi268LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (9816528457/9816279040) } }, logDArg := sk111LogDArgCertificate }

private noncomputable def leaf4263InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf4263LocalValidity :
    LeafFacts leaf4263Box leaf4263Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4263Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4908388937/4908139520) }) = true
      norm_num [leaf4263Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4263CertificateValid :
    WideCertificateValid leaf4263Box leaf4263Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk111ValidityFacts chi268ValidityFacts
    leaf4263LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4263CoverageChecked :
    coverageCheck (innerAD leaf4263Box) leaf4263InnerLog = true := by
  rfl'

private theorem leaf4263InnerLogValid :
    leaf4263InnerLog.Valid 8 (innerAD leaf4263Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf4263CoverageChecked

private noncomputable def leaf4263InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629507/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4263InputLogOnePlusV_eq :
    leaf4263InputLogOnePlusV = outerEnclosure 24
      (leaf4263Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4263RoundedFacts : LeafRoundedFacts 8
    leaf4263Certificate.logOnePlusV leaf4263InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4263InputLogOnePlusV_eq }

private noncomputable def leaf4263Inputs : Inputs :=
  inputsOfCaches globalInput sk111RoundedInputs
    chi268InputQChi innerPair265Input
    leaf4263InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4263LowerChecked :
    lowerCheck 24 leaf4263Box leaf4263Inputs = true := by
  rfl'

private theorem leaf4263CoversExact : CoversExact 8
    leaf4263Box leaf4263Certificate leaf4263InnerLog leaf4263Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk111RoundedFacts chi268RoundedFacts
    innerPair265RoundedFacts leaf4263RoundedFacts (by rfl)

private theorem leaf4263FlatSound : Sound leaf4263Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4263CertificateValid
    leaf4263InnerLogValid leaf4263CoversExact leaf4263LowerChecked

private noncomputable def leaf4264Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16), chiLo := (57/128), chiHi := (29/64) }

private noncomputable def leaf4264Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435759/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34356946944) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (615787519/536870912) }, upper := { exponent := 1, mantissa := (2387/2048) } }, logOuter := sk112LogOuterCertificate, logK := sk112LogKCertificate, logChi := chi268LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715669503/68713893888) } }, logDArg := sk112LogDArgCertificate }

private noncomputable def leaf4264InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf4264LocalValidity :
    LeafFacts leaf4264Box leaf4264Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4264Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34356946944) }) = true
      norm_num [leaf4264Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4264CertificateValid :
    WideCertificateValid leaf4264Box leaf4264Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk112ValidityFacts chi268ValidityFacts
    leaf4264LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4264CoverageChecked :
    coverageCheck (innerAD leaf4264Box) leaf4264InnerLog = true := by
  rfl'

private theorem leaf4264InnerLogValid :
    leaf4264InnerLog.Valid 8 (innerAD leaf4264Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf4264CoverageChecked

private noncomputable def leaf4264InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814757/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4264InputLogOnePlusV_eq :
    leaf4264InputLogOnePlusV = outerEnclosure 24
      (leaf4264Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4264RoundedFacts : LeafRoundedFacts 8
    leaf4264Certificate.logOnePlusV leaf4264InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4264InputLogOnePlusV_eq }

private noncomputable def leaf4264Inputs : Inputs :=
  inputsOfCaches globalInput sk112RoundedInputs
    chi268InputQChi innerPair265Input
    leaf4264InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4264LowerChecked :
    lowerCheck 24 leaf4264Box leaf4264Inputs = true := by
  rfl'

private theorem leaf4264CoversExact : CoversExact 8
    leaf4264Box leaf4264Certificate leaf4264InnerLog leaf4264Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk112RoundedFacts chi268RoundedFacts
    innerPair265RoundedFacts leaf4264RoundedFacts (by rfl)

private theorem leaf4264FlatSound : Sound leaf4264Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4264CertificateValid
    leaf4264InnerLogValid leaf4264CoversExact leaf4264LowerChecked

private noncomputable def leaf4265Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32), chiLo := (29/64), chiHi := (59/128) }

private noncomputable def leaf4265Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435759/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34356929024) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (618081139/536870912) }, upper := { exponent := 1, mantissa := (9583/8192) } }, logOuter := sk111LogOuterCertificate, logK := sk111LogKCertificate, logChi := chi269LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715651583/68713858048) } }, logDArg := sk111LogDArgCertificate }

private noncomputable def leaf4265InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf4265LocalValidity :
    LeafFacts leaf4265Box leaf4265Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4265Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34356929024) }) = true
      norm_num [leaf4265Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4265CertificateValid :
    WideCertificateValid leaf4265Box leaf4265Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk111ValidityFacts chi269ValidityFacts
    leaf4265LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4265CoverageChecked :
    coverageCheck (innerAD leaf4265Box) leaf4265InnerLog = true := by
  rfl'

private theorem leaf4265InnerLogValid :
    leaf4265InnerLog.Valid 8 (innerAD leaf4265Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf4265CoverageChecked

private noncomputable def leaf4265InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629519/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4265InputLogOnePlusV_eq :
    leaf4265InputLogOnePlusV = outerEnclosure 24
      (leaf4265Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4265RoundedFacts : LeafRoundedFacts 8
    leaf4265Certificate.logOnePlusV leaf4265InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4265InputLogOnePlusV_eq }

private noncomputable def leaf4265Inputs : Inputs :=
  inputsOfCaches globalInput sk111RoundedInputs
    chi269InputQChi innerPair265Input
    leaf4265InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4265LowerChecked :
    lowerCheck 24 leaf4265Box leaf4265Inputs = true := by
  rfl'

private theorem leaf4265CoversExact : CoversExact 8
    leaf4265Box leaf4265Certificate leaf4265InnerLog leaf4265Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk111RoundedFacts chi269RoundedFacts
    innerPair265RoundedFacts leaf4265RoundedFacts (by rfl)

private theorem leaf4265FlatSound : Sound leaf4265Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4265CertificateValid
    leaf4265InnerLogValid leaf4265CoversExact leaf4265LowerChecked

private noncomputable def leaf4266Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16), chiLo := (29/64), chiHi := (59/128) }

private noncomputable def leaf4266Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435761/268435456) }, vSqrt := { lower := (32765/32768), upper := (2021101327/2020994048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (621881993/536870912) }, upper := { exponent := 1, mantissa := (4821/4096) } }, logOuter := sk112LogOuterCertificate, logK := sk112LogKCertificate, logChi := chi269LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (4042095375/4041988096) } }, logDArg := sk112LogDArgCertificate }

private noncomputable def leaf4266InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf4266LocalValidity :
    LeafFacts leaf4266Box leaf4266Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4266Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (2021101327/2020994048) }) = true
      norm_num [leaf4266Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4266CertificateValid :
    WideCertificateValid leaf4266Box leaf4266Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk112ValidityFacts chi269ValidityFacts
    leaf4266LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4266CoverageChecked :
    coverageCheck (innerAD leaf4266Box) leaf4266InnerLog = true := by
  rfl'

private theorem leaf4266InnerLogValid :
    leaf4266InnerLog.Valid 8 (innerAD leaf4266Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf4266CoverageChecked

private noncomputable def leaf4266InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814763/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4266InputLogOnePlusV_eq :
    leaf4266InputLogOnePlusV = outerEnclosure 24
      (leaf4266Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4266RoundedFacts : LeafRoundedFacts 8
    leaf4266Certificate.logOnePlusV leaf4266InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4266InputLogOnePlusV_eq }

private noncomputable def leaf4266Inputs : Inputs :=
  inputsOfCaches globalInput sk112RoundedInputs
    chi269InputQChi innerPair272Input
    leaf4266InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4266LowerChecked :
    lowerCheck 24 leaf4266Box leaf4266Inputs = true := by
  rfl'

private theorem leaf4266CoversExact : CoversExact 8
    leaf4266Box leaf4266Certificate leaf4266InnerLog leaf4266Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk112RoundedFacts chi269RoundedFacts
    innerPair272RoundedFacts leaf4266RoundedFacts (by rfl)

private theorem leaf4266FlatSound : Sound leaf4266Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4266CertificateValid
    leaf4266InnerLogValid leaf4266CoversExact leaf4266LowerChecked

private noncomputable def leaf4267Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32), chiLo := (59/128), chiHi := (15/32) }

private noncomputable def leaf4267Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435761/268435456) }, vSqrt := { lower := (32765/32768), upper := (2021101327/2020993024) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (624110081/536870912) }, upper := { exponent := 1, mantissa := (2419/2048) } }, logOuter := sk111LogOuterCertificate, logK := sk111LogKCertificate, logChi := chi270LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (4042094351/4041986048) } }, logDArg := sk111LogDArgCertificate }

private noncomputable def leaf4267InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf4267LocalValidity :
    LeafFacts leaf4267Box leaf4267Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4267Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (2021101327/2020993024) }) = true
      norm_num [leaf4267Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4267CertificateValid :
    WideCertificateValid leaf4267Box leaf4267Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk111ValidityFacts chi270ValidityFacts
    leaf4267LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4267CoverageChecked :
    coverageCheck (innerAD leaf4267Box) leaf4267InnerLog = true := by
  rfl'

private theorem leaf4267InnerLogValid :
    leaf4267InnerLog.Valid 8 (innerAD leaf4267Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf4267CoverageChecked

private noncomputable def leaf4267InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814765/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4267InputLogOnePlusV_eq :
    leaf4267InputLogOnePlusV = outerEnclosure 24
      (leaf4267Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4267RoundedFacts : LeafRoundedFacts 8
    leaf4267Certificate.logOnePlusV leaf4267InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4267InputLogOnePlusV_eq }

private noncomputable def leaf4267Inputs : Inputs :=
  inputsOfCaches globalInput sk111RoundedInputs
    chi270InputQChi innerPair272Input
    leaf4267InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4267LowerChecked :
    lowerCheck 24 leaf4267Box leaf4267Inputs = true := by
  rfl'

private theorem leaf4267CoversExact : CoversExact 8
    leaf4267Box leaf4267Certificate leaf4267InnerLog leaf4267Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk111RoundedFacts chi270RoundedFacts
    innerPair272RoundedFacts leaf4267RoundedFacts (by rfl)

private theorem leaf4267FlatSound : Sound leaf4267Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4267CertificateValid
    leaf4267InnerLogValid leaf4267CoversExact leaf4267LowerChecked

private noncomputable def leaf4268Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16), chiLo := (59/128), chiHi := (15/32) }

private noncomputable def leaf4268Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435763/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34356850688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (627976467/536870912) }, upper := { exponent := 1, mantissa := (1217/1024) } }, logOuter := sk112LogOuterCertificate, logK := sk112LogKCertificate, logChi := chi270LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715573247/68713701376) } }, logDArg := sk112LogDArgCertificate }

private noncomputable def leaf4268InnerLog : WideLogData :=
  innerPair273Data

set_option maxRecDepth 1000000 in
private theorem leaf4268LocalValidity :
    LeafFacts leaf4268Box leaf4268Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4268Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34356850688) }) = true
      norm_num [leaf4268Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4268CertificateValid :
    WideCertificateValid leaf4268Box leaf4268Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk112ValidityFacts chi270ValidityFacts
    leaf4268LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4268CoverageChecked :
    coverageCheck (innerAD leaf4268Box) leaf4268InnerLog = true := by
  rfl'

private theorem leaf4268InnerLogValid :
    leaf4268InnerLog.Valid 8 (innerAD leaf4268Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint78PositiveFacts.valid leaf4268CoverageChecked

private noncomputable def leaf4268InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814769/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4268InputLogOnePlusV_eq :
    leaf4268InputLogOnePlusV = outerEnclosure 24
      (leaf4268Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4268RoundedFacts : LeafRoundedFacts 8
    leaf4268Certificate.logOnePlusV leaf4268InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4268InputLogOnePlusV_eq }

private noncomputable def leaf4268Inputs : Inputs :=
  inputsOfCaches globalInput sk112RoundedInputs
    chi270InputQChi innerPair273Input
    leaf4268InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4268LowerChecked :
    lowerCheck 24 leaf4268Box leaf4268Inputs = true := by
  rfl'

private theorem leaf4268CoversExact : CoversExact 8
    leaf4268Box leaf4268Certificate leaf4268InnerLog leaf4268Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk112RoundedFacts chi270RoundedFacts
    innerPair273RoundedFacts leaf4268RoundedFacts (by rfl)

private theorem leaf4268FlatSound : Sound leaf4268Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4268CertificateValid
    leaf4268InnerLogValid leaf4268CoversExact leaf4268LowerChecked

private noncomputable def leaf4269Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (95/32), chiLo := (7/16), chiHi := (57/128) }

private noncomputable def leaf4269Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435759/268435456) }, vSqrt := { lower := (32765/32768), upper := (4908388937/4908137984) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (613362835/536870912) }, upper := { exponent := 1, mantissa := (9511/8192) } }, logOuter := sk113LogOuterCertificate, logK := sk113LogKCertificate, logChi := chi267LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (9816526921/9816275968) } }, logDArg := sk113LogDArgCertificate }

private noncomputable def leaf4269InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf4269LocalValidity :
    LeafFacts leaf4269Box leaf4269Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4269Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4908388937/4908137984) }) = true
      norm_num [leaf4269Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4269CertificateValid :
    WideCertificateValid leaf4269Box leaf4269Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk113ValidityFacts chi267ValidityFacts
    leaf4269LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4269CoverageChecked :
    coverageCheck (innerAD leaf4269Box) leaf4269InnerLog = true := by
  rfl'

private theorem leaf4269InnerLogValid :
    leaf4269InnerLog.Valid 8 (innerAD leaf4269Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf4269CoverageChecked

private noncomputable def leaf4269InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814755/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4269InputLogOnePlusV_eq :
    leaf4269InputLogOnePlusV = outerEnclosure 24
      (leaf4269Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4269RoundedFacts : LeafRoundedFacts 8
    leaf4269Certificate.logOnePlusV leaf4269InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4269InputLogOnePlusV_eq }

private noncomputable def leaf4269Inputs : Inputs :=
  inputsOfCaches globalInput sk113RoundedInputs
    chi267InputQChi innerPair265Input
    leaf4269InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4269LowerChecked :
    lowerCheck 24 leaf4269Box leaf4269Inputs = true := by
  rfl'

private theorem leaf4269CoversExact : CoversExact 8
    leaf4269Box leaf4269Certificate leaf4269InnerLog leaf4269Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk113RoundedFacts chi267RoundedFacts
    innerPair265RoundedFacts leaf4269RoundedFacts (by rfl)

private theorem leaf4269FlatSound : Sound leaf4269Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4269CertificateValid
    leaf4269InnerLogValid leaf4269CoversExact leaf4269LowerChecked

private noncomputable def leaf4270Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (7/16), chiHi := (57/128) }

private noncomputable def leaf4270Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435761/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356936704) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (617032625/536870912) }, upper := { exponent := 1, mantissa := (299/256) } }, logOuter := sk114LogOuterCertificate, logK := sk114LogKCertificate, logChi := chi267LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715659263/68713873408) } }, logDArg := sk114LogDArgCertificate }

private noncomputable def leaf4270InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf4270LocalValidity :
    LeafFacts leaf4270Box leaf4270Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4270Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356936704) }) = true
      norm_num [leaf4270Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4270CertificateValid :
    WideCertificateValid leaf4270Box leaf4270Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk114ValidityFacts chi267ValidityFacts
    leaf4270LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4270CoverageChecked :
    coverageCheck (innerAD leaf4270Box) leaf4270InnerLog = true := by
  rfl'

private theorem leaf4270InnerLogValid :
    leaf4270InnerLog.Valid 8 (innerAD leaf4270Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf4270CoverageChecked

private noncomputable def leaf4270InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629517/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4270InputLogOnePlusV_eq :
    leaf4270InputLogOnePlusV = outerEnclosure 24
      (leaf4270Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4270RoundedFacts : LeafRoundedFacts 8
    leaf4270Certificate.logOnePlusV leaf4270InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4270InputLogOnePlusV_eq }

private noncomputable def leaf4270Inputs : Inputs :=
  inputsOfCaches globalInput sk114RoundedInputs
    chi267InputQChi innerPair265Input
    leaf4270InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4270LowerChecked :
    lowerCheck 24 leaf4270Box leaf4270Inputs = true := by
  rfl'

private theorem leaf4270CoversExact : CoversExact 8
    leaf4270Box leaf4270Certificate leaf4270InnerLog leaf4270Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk114RoundedFacts chi267RoundedFacts
    innerPair265RoundedFacts leaf4270RoundedFacts (by rfl)

private theorem leaf4270FlatSound : Sound leaf4270Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4270CertificateValid
    leaf4270InnerLogValid leaf4270CoversExact leaf4270LowerChecked

private noncomputable def leaf4271Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (95/32), chiLo := (57/128), chiHi := (29/64) }

private noncomputable def leaf4271Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435761/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34356917248) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (619522841/536870912) }, upper := { exponent := 1, mantissa := (4803/4096) } }, logOuter := sk113LogOuterCertificate, logK := sk113LogKCertificate, logChi := chi268LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715639807/68713834496) } }, logDArg := sk113LogDArgCertificate }

private noncomputable def leaf4271InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf4271LocalValidity :
    LeafFacts leaf4271Box leaf4271Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4271Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34356917248) }) = true
      norm_num [leaf4271Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4271CertificateValid :
    WideCertificateValid leaf4271Box leaf4271Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk113ValidityFacts chi268ValidityFacts
    leaf4271LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4271CoverageChecked :
    coverageCheck (innerAD leaf4271Box) leaf4271InnerLog = true := by
  rfl'

private theorem leaf4271InnerLogValid :
    leaf4271InnerLog.Valid 8 (innerAD leaf4271Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf4271CoverageChecked

private noncomputable def leaf4271InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814761/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4271InputLogOnePlusV_eq :
    leaf4271InputLogOnePlusV = outerEnclosure 24
      (leaf4271Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4271RoundedFacts : LeafRoundedFacts 8
    leaf4271Certificate.logOnePlusV leaf4271InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4271InputLogOnePlusV_eq }

private noncomputable def leaf4271Inputs : Inputs :=
  inputsOfCaches globalInput sk113RoundedInputs
    chi268InputQChi innerPair265Input
    leaf4271InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4271LowerChecked :
    lowerCheck 24 leaf4271Box leaf4271Inputs = true := by
  rfl'

private theorem leaf4271CoversExact : CoversExact 8
    leaf4271Box leaf4271Certificate leaf4271InnerLog leaf4271Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk113RoundedFacts chi268RoundedFacts
    innerPair265RoundedFacts leaf4271RoundedFacts (by rfl)

private theorem leaf4271FlatSound : Sound leaf4271Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4271CertificateValid
    leaf4271InnerLogValid leaf4271CoversExact leaf4271LowerChecked

private noncomputable def leaf4272Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (57/128), chiHi := (29/64) }

private noncomputable def leaf4272Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435763/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356887552) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (623258163/536870912) }, upper := { exponent := 1, mantissa := (151/128) } }, logOuter := sk114LogOuterCertificate, logK := sk114LogKCertificate, logChi := chi268LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715610111/68713775104) } }, logDArg := sk114LogDArgCertificate }

private noncomputable def leaf4272InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf4272LocalValidity :
    LeafFacts leaf4272Box leaf4272Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4272Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356887552) }) = true
      norm_num [leaf4272Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4272CertificateValid :
    WideCertificateValid leaf4272Box leaf4272Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk114ValidityFacts chi268ValidityFacts
    leaf4272LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4272CoverageChecked :
    coverageCheck (innerAD leaf4272Box) leaf4272InnerLog = true := by
  rfl'

private theorem leaf4272InnerLogValid :
    leaf4272InnerLog.Valid 8 (innerAD leaf4272Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf4272CoverageChecked

private noncomputable def leaf4272InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629529/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4272InputLogOnePlusV_eq :
    leaf4272InputLogOnePlusV = outerEnclosure 24
      (leaf4272Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4272RoundedFacts : LeafRoundedFacts 8
    leaf4272Certificate.logOnePlusV leaf4272InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4272InputLogOnePlusV_eq }

private noncomputable def leaf4272Inputs : Inputs :=
  inputsOfCaches globalInput sk114RoundedInputs
    chi268InputQChi innerPair272Input
    leaf4272InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4272LowerChecked :
    lowerCheck 24 leaf4272Box leaf4272Inputs = true := by
  rfl'

private theorem leaf4272CoversExact : CoversExact 8
    leaf4272Box leaf4272Certificate leaf4272InnerLog leaf4272Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk114RoundedFacts chi268RoundedFacts
    innerPair272RoundedFacts leaf4272RoundedFacts (by rfl)

private theorem leaf4272FlatSound : Sound leaf4272Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4272CertificateValid
    leaf4272InnerLogValid leaf4272CoversExact leaf4272LowerChecked

private noncomputable def leaf4273Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (95/32), chiLo := (29/64), chiHi := (59/128) }

private noncomputable def leaf4273Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435763/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34356868608) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (625682847/536870912) }, upper := { exponent := 1, mantissa := (9701/8192) } }, logOuter := sk113LogOuterCertificate, logK := sk113LogKCertificate, logChi := chi269LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715591167/68713737216) } }, logDArg := sk113LogDArgCertificate }

private noncomputable def leaf4273InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf4273LocalValidity :
    LeafFacts leaf4273Box leaf4273Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4273Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34356868608) }) = true
      norm_num [leaf4273Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4273CertificateValid :
    WideCertificateValid leaf4273Box leaf4273Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk113ValidityFacts chi269ValidityFacts
    leaf4273LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4273CoverageChecked :
    coverageCheck (innerAD leaf4273Box) leaf4273InnerLog = true := by
  rfl'

private theorem leaf4273InnerLogValid :
    leaf4273InnerLog.Valid 8 (innerAD leaf4273Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf4273CoverageChecked

private noncomputable def leaf4273InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629533/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4273InputLogOnePlusV_eq :
    leaf4273InputLogOnePlusV = outerEnclosure 24
      (leaf4273Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4273RoundedFacts : LeafRoundedFacts 8
    leaf4273Certificate.logOnePlusV leaf4273InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4273InputLogOnePlusV_eq }

private noncomputable def leaf4273Inputs : Inputs :=
  inputsOfCaches globalInput sk113RoundedInputs
    chi269InputQChi innerPair272Input
    leaf4273InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4273LowerChecked :
    lowerCheck 24 leaf4273Box leaf4273Inputs = true := by
  rfl'

private theorem leaf4273CoversExact : CoversExact 8
    leaf4273Box leaf4273Certificate leaf4273InnerLog leaf4273Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk113RoundedFacts chi269RoundedFacts
    innerPair272RoundedFacts leaf4273RoundedFacts (by rfl)

private theorem leaf4273FlatSound : Sound leaf4273Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4273CertificateValid
    leaf4273InnerLogValid leaf4273CoversExact leaf4273LowerChecked

private noncomputable def leaf4274Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (29/64), chiHi := (59/128) }

private noncomputable def leaf4274Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435765/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356838400) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (629483701/536870912) }, upper := { exponent := 1, mantissa := (305/256) } }, logOuter := sk114LogOuterCertificate, logK := sk114LogKCertificate, logChi := chi269LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715560959/68713676800) } }, logDArg := sk114LogDArgCertificate }

private noncomputable def leaf4274InnerLog : WideLogData :=
  innerPair273Data

set_option maxRecDepth 1000000 in
private theorem leaf4274LocalValidity :
    LeafFacts leaf4274Box leaf4274Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4274Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356838400) }) = true
      norm_num [leaf4274Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4274CertificateValid :
    WideCertificateValid leaf4274Box leaf4274Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk114ValidityFacts chi269ValidityFacts
    leaf4274LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4274CoverageChecked :
    coverageCheck (innerAD leaf4274Box) leaf4274InnerLog = true := by
  rfl'

private theorem leaf4274InnerLogValid :
    leaf4274InnerLog.Valid 8 (innerAD leaf4274Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint78PositiveFacts.valid leaf4274CoverageChecked

private noncomputable def leaf4274InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629541/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4274InputLogOnePlusV_eq :
    leaf4274InputLogOnePlusV = outerEnclosure 24
      (leaf4274Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4274RoundedFacts : LeafRoundedFacts 8
    leaf4274Certificate.logOnePlusV leaf4274InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4274InputLogOnePlusV_eq }

private noncomputable def leaf4274Inputs : Inputs :=
  inputsOfCaches globalInput sk114RoundedInputs
    chi269InputQChi innerPair273Input
    leaf4274InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4274LowerChecked :
    lowerCheck 24 leaf4274Box leaf4274Inputs = true := by
  rfl'

private theorem leaf4274CoversExact : CoversExact 8
    leaf4274Box leaf4274Certificate leaf4274InnerLog leaf4274Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk114RoundedFacts chi269RoundedFacts
    innerPair273RoundedFacts leaf4274RoundedFacts (by rfl)

private theorem leaf4274FlatSound : Sound leaf4274Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4274CertificateValid
    leaf4274InnerLogValid leaf4274CoversExact leaf4274LowerChecked

private noncomputable def leaf4275Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (95/32), chiLo := (59/128), chiHi := (15/32) }

private noncomputable def leaf4275Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435765/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34356819968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (631842853/536870912) }, upper := { exponent := 1, mantissa := (2449/2048) } }, logOuter := sk113LogOuterCertificate, logK := sk113LogKCertificate, logChi := chi270LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715542527/68713639936) } }, logDArg := sk113LogDArgCertificate }

private noncomputable def leaf4275InnerLog : WideLogData :=
  innerPair273Data

set_option maxRecDepth 1000000 in
private theorem leaf4275LocalValidity :
    LeafFacts leaf4275Box leaf4275Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4275Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34356819968) }) = true
      norm_num [leaf4275Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4275CertificateValid :
    WideCertificateValid leaf4275Box leaf4275Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk113ValidityFacts chi270ValidityFacts
    leaf4275LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4275CoverageChecked :
    coverageCheck (innerAD leaf4275Box) leaf4275InnerLog = true := by
  rfl'

private theorem leaf4275InnerLogValid :
    leaf4275InnerLog.Valid 8 (innerAD leaf4275Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint78PositiveFacts.valid leaf4275CoverageChecked

private noncomputable def leaf4275InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629545/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4275InputLogOnePlusV_eq :
    leaf4275InputLogOnePlusV = outerEnclosure 24
      (leaf4275Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4275RoundedFacts : LeafRoundedFacts 8
    leaf4275Certificate.logOnePlusV leaf4275InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4275InputLogOnePlusV_eq }

private noncomputable def leaf4275Inputs : Inputs :=
  inputsOfCaches globalInput sk113RoundedInputs
    chi270InputQChi innerPair273Input
    leaf4275InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4275LowerChecked :
    lowerCheck 24 leaf4275Box leaf4275Inputs = true := by
  rfl'

private theorem leaf4275CoversExact : CoversExact 8
    leaf4275Box leaf4275Certificate leaf4275InnerLog leaf4275Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk113RoundedFacts chi270RoundedFacts
    innerPair273RoundedFacts leaf4275RoundedFacts (by rfl)

private theorem leaf4275FlatSound : Sound leaf4275Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4275CertificateValid
    leaf4275InnerLogValid leaf4275CoversExact leaf4275LowerChecked

private noncomputable def leaf4276Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (59/128), chiHi := (15/32) }

private noncomputable def leaf4276Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435767/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356789248) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (635709239/536870912) }, upper := { exponent := 1, mantissa := (77/64) } }, logOuter := sk114LogOuterCertificate, logK := sk114LogKCertificate, logChi := chi270LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715511807/68713578496) } }, logDArg := sk114LogDArgCertificate }

private noncomputable def leaf4276InnerLog : WideLogData :=
  innerPair273Data

set_option maxRecDepth 1000000 in
private theorem leaf4276LocalValidity :
    LeafFacts leaf4276Box leaf4276Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4276Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356789248) }) = true
      norm_num [leaf4276Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4276CertificateValid :
    WideCertificateValid leaf4276Box leaf4276Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk114ValidityFacts chi270ValidityFacts
    leaf4276LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4276CoverageChecked :
    coverageCheck (innerAD leaf4276Box) leaf4276InnerLog = true := by
  rfl'

private theorem leaf4276InnerLogValid :
    leaf4276InnerLog.Valid 8 (innerAD leaf4276Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint78PositiveFacts.valid leaf4276CoverageChecked

private noncomputable def leaf4276InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629553/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4276InputLogOnePlusV_eq :
    leaf4276InputLogOnePlusV = outerEnclosure 24
      (leaf4276Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4276RoundedFacts : LeafRoundedFacts 8
    leaf4276Certificate.logOnePlusV leaf4276InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4276InputLogOnePlusV_eq }

private noncomputable def leaf4276Inputs : Inputs :=
  inputsOfCaches globalInput sk114RoundedInputs
    chi270InputQChi innerPair273Input
    leaf4276InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4276LowerChecked :
    lowerCheck 24 leaf4276Box leaf4276Inputs = true := by
  rfl'

private theorem leaf4276CoversExact : CoversExact 8
    leaf4276Box leaf4276Certificate leaf4276InnerLog leaf4276Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk114RoundedFacts chi270RoundedFacts
    innerPair273RoundedFacts leaf4276RoundedFacts (by rfl)

private theorem leaf4276FlatSound : Sound leaf4276Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4276CertificateValid
    leaf4276InnerLogValid leaf4276CoversExact leaf4276LowerChecked

private noncomputable def leaf4277Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32), chiLo := (15/32), chiHi := (61/128) }

private noncomputable def leaf4277Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435763/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34356833792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (630139023/536870912) }, upper := { exponent := 1, mantissa := (9769/8192) } }, logOuter := sk111LogOuterCertificate, logK := sk111LogKCertificate, logChi := chi271LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715556351/68713667584) } }, logDArg := sk111LogDArgCertificate }

private noncomputable def leaf4277InnerLog : WideLogData :=
  innerPair273Data

set_option maxRecDepth 1000000 in
private theorem leaf4277LocalValidity :
    LeafFacts leaf4277Box leaf4277Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4277Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34356833792) }) = true
      norm_num [leaf4277Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4277CertificateValid :
    WideCertificateValid leaf4277Box leaf4277Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk111ValidityFacts chi271ValidityFacts
    leaf4277LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4277CoverageChecked :
    coverageCheck (innerAD leaf4277Box) leaf4277InnerLog = true := by
  rfl'

private theorem leaf4277InnerLogValid :
    leaf4277InnerLog.Valid 8 (innerAD leaf4277Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint78PositiveFacts.valid leaf4277CoverageChecked

private noncomputable def leaf4277InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814771/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4277InputLogOnePlusV_eq :
    leaf4277InputLogOnePlusV = outerEnclosure 24
      (leaf4277Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4277RoundedFacts : LeafRoundedFacts 8
    leaf4277Certificate.logOnePlusV leaf4277InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4277InputLogOnePlusV_eq }

private noncomputable def leaf4277Inputs : Inputs :=
  inputsOfCaches globalInput sk111RoundedInputs
    chi271InputQChi innerPair273Input
    leaf4277InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4277LowerChecked :
    lowerCheck 24 leaf4277Box leaf4277Inputs = true := by
  rfl'

private theorem leaf4277CoversExact : CoversExact 8
    leaf4277Box leaf4277Certificate leaf4277InnerLog leaf4277Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk111RoundedFacts chi271RoundedFacts
    innerPair273RoundedFacts leaf4277RoundedFacts (by rfl)

private theorem leaf4277FlatSound : Sound leaf4277Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4277CertificateValid
    leaf4277InnerLogValid leaf4277CoversExact leaf4277LowerChecked

private noncomputable def leaf4278Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16), chiLo := (15/32), chiHi := (61/128) }

private noncomputable def leaf4278Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435765/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34356802560) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (634070941/536870912) }, upper := { exponent := 1, mantissa := (4915/4096) } }, logOuter := sk112LogOuterCertificate, logK := sk112LogKCertificate, logChi := chi271LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715525119/68713605120) } }, logDArg := sk112LogDArgCertificate }

private noncomputable def leaf4278InnerLog : WideLogData :=
  innerPair273Data

set_option maxRecDepth 1000000 in
private theorem leaf4278LocalValidity :
    LeafFacts leaf4278Box leaf4278Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4278Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34356802560) }) = true
      norm_num [leaf4278Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4278CertificateValid :
    WideCertificateValid leaf4278Box leaf4278Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk112ValidityFacts chi271ValidityFacts
    leaf4278LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4278CoverageChecked :
    coverageCheck (innerAD leaf4278Box) leaf4278InnerLog = true := by
  rfl'

private theorem leaf4278InnerLogValid :
    leaf4278InnerLog.Valid 8 (innerAD leaf4278Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint78PositiveFacts.valid leaf4278CoverageChecked

private noncomputable def leaf4278InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814775/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4278InputLogOnePlusV_eq :
    leaf4278InputLogOnePlusV = outerEnclosure 24
      (leaf4278Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4278RoundedFacts : LeafRoundedFacts 8
    leaf4278Certificate.logOnePlusV leaf4278InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4278InputLogOnePlusV_eq }

private noncomputable def leaf4278Inputs : Inputs :=
  inputsOfCaches globalInput sk112RoundedInputs
    chi271InputQChi innerPair273Input
    leaf4278InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4278LowerChecked :
    lowerCheck 24 leaf4278Box leaf4278Inputs = true := by
  rfl'

private theorem leaf4278CoversExact : CoversExact 8
    leaf4278Box leaf4278Certificate leaf4278InnerLog leaf4278Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk112RoundedFacts chi271RoundedFacts
    innerPair273RoundedFacts leaf4278RoundedFacts (by rfl)

private theorem leaf4278FlatSound : Sound leaf4278Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4278CertificateValid
    leaf4278InnerLogValid leaf4278CoversExact leaf4278LowerChecked

private noncomputable def leaf4279Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32), chiLo := (61/128), chiHi := (31/64) }

private noncomputable def leaf4279Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435765/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34356786176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (636167965/536870912) }, upper := { exponent := 1, mantissa := (4931/4096) } }, logOuter := sk111LogOuterCertificate, logK := sk111LogKCertificate, logChi := chi272LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715508735/68713572352) } }, logDArg := sk111LogDArgCertificate }

private noncomputable def leaf4279InnerLog : WideLogData :=
  innerPair273Data

set_option maxRecDepth 1000000 in
private theorem leaf4279LocalValidity :
    LeafFacts leaf4279Box leaf4279Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4279Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34356786176) }) = true
      norm_num [leaf4279Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4279CertificateValid :
    WideCertificateValid leaf4279Box leaf4279Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk111ValidityFacts chi272ValidityFacts
    leaf4279LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4279CoverageChecked :
    coverageCheck (innerAD leaf4279Box) leaf4279InnerLog = true := by
  rfl'

private theorem leaf4279InnerLogValid :
    leaf4279InnerLog.Valid 8 (innerAD leaf4279Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint78PositiveFacts.valid leaf4279CoverageChecked

private noncomputable def leaf4279InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814777/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4279InputLogOnePlusV_eq :
    leaf4279InputLogOnePlusV = outerEnclosure 24
      (leaf4279Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4279RoundedFacts : LeafRoundedFacts 8
    leaf4279Certificate.logOnePlusV leaf4279InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4279InputLogOnePlusV_eq }

private noncomputable def leaf4279Inputs : Inputs :=
  inputsOfCaches globalInput sk111RoundedInputs
    chi272InputQChi innerPair273Input
    leaf4279InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4279LowerChecked :
    lowerCheck 24 leaf4279Box leaf4279Inputs = true := by
  rfl'

private theorem leaf4279CoversExact : CoversExact 8
    leaf4279Box leaf4279Certificate leaf4279InnerLog leaf4279Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk111RoundedFacts chi272RoundedFacts
    innerPair273RoundedFacts leaf4279RoundedFacts (by rfl)

private theorem leaf4279FlatSound : Sound leaf4279Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4279CertificateValid
    leaf4279InnerLogValid leaf4279CoversExact leaf4279LowerChecked

private noncomputable def leaf4280Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16), chiLo := (61/128), chiHi := (31/64) }

private noncomputable def leaf4280Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435767/268435456) }, vSqrt := { lower := (32765/32768), upper := (4908388937/4908107776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (640165415/536870912) }, upper := { exponent := 1, mantissa := (2481/2048) } }, logOuter := sk112LogOuterCertificate, logK := sk112LogKCertificate, logChi := chi272LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (9816496713/9816215552) } }, logDArg := sk112LogDArgCertificate }

private noncomputable def leaf4280InnerLog : WideLogData :=
  innerPair278Data

set_option maxRecDepth 1000000 in
private theorem leaf4280LocalValidity :
    LeafFacts leaf4280Box leaf4280Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4280Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4908388937/4908107776) }) = true
      norm_num [leaf4280Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4280CertificateValid :
    WideCertificateValid leaf4280Box leaf4280Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk112ValidityFacts chi272ValidityFacts
    leaf4280LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4280CoverageChecked :
    coverageCheck (innerAD leaf4280Box) leaf4280InnerLog = true := by
  rfl'

private theorem leaf4280InnerLogValid :
    leaf4280InnerLog.Valid 8 (innerAD leaf4280Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint78PositiveFacts.valid leaf4280CoverageChecked

private noncomputable def leaf4280InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629561/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4280InputLogOnePlusV_eq :
    leaf4280InputLogOnePlusV = outerEnclosure 24
      (leaf4280Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4280RoundedFacts : LeafRoundedFacts 8
    leaf4280Certificate.logOnePlusV leaf4280InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4280InputLogOnePlusV_eq }

private noncomputable def leaf4280Inputs : Inputs :=
  inputsOfCaches globalInput sk112RoundedInputs
    chi272InputQChi innerPair278Input
    leaf4280InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4280LowerChecked :
    lowerCheck 24 leaf4280Box leaf4280Inputs = true := by
  rfl'

private theorem leaf4280CoversExact : CoversExact 8
    leaf4280Box leaf4280Certificate leaf4280InnerLog leaf4280Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk112RoundedFacts chi272RoundedFacts
    innerPair278RoundedFacts leaf4280RoundedFacts (by rfl)

private theorem leaf4280FlatSound : Sound leaf4280Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4280CertificateValid
    leaf4280InnerLogValid leaf4280CoversExact leaf4280LowerChecked

private noncomputable def leaf4281Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (31/64), chiHi := (63/128) }

private noncomputable def leaf4281Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217947/134217728) }, vSqrt := { lower := (32765/32768), upper := (17179377663/17178353152) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (321082007/268435456) }, upper := { exponent := 1, mantissa := (5009/4096) } }, logOuter := sk97LogOuterCertificate, logK := sk97LogKCertificate, logChi := chi273LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (34357730815/34356706304) } }, logDArg := sk97LogDArgCertificate }

private noncomputable def leaf4281InnerLog : WideLogData :=
  innerPair595Data

set_option maxRecDepth 1000000 in
private theorem leaf4281LocalValidity :
    LeafFacts leaf4281Box leaf4281Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4281Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (17179377663/17178353152) }) = true
      norm_num [leaf4281Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4281CertificateValid :
    WideCertificateValid leaf4281Box leaf4281Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk97ValidityFacts chi273ValidityFacts
    leaf4281LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4281CoverageChecked :
    coverageCheck (innerAD leaf4281Box) leaf4281InnerLog = true := by
  rfl'

private theorem leaf4281InnerLogValid :
    leaf4281InnerLog.Valid 8 (innerAD leaf4281Box) :=
  wideLogDataValid_of_cachedCheck endpoint309PositiveFacts
    endpoint310PositiveFacts.valid leaf4281CoverageChecked

private noncomputable def leaf4281InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629581/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4281InputLogOnePlusV_eq :
    leaf4281InputLogOnePlusV = outerEnclosure 24
      (leaf4281Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4281RoundedFacts : LeafRoundedFacts 8
    leaf4281Certificate.logOnePlusV leaf4281InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4281InputLogOnePlusV_eq }

private noncomputable def leaf4281Inputs : Inputs :=
  inputsOfCaches globalInput sk97RoundedInputs
    chi273InputQChi innerPair595Input
    leaf4281InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4281LowerChecked :
    lowerCheck 24 leaf4281Box leaf4281Inputs = true := by
  rfl'

private theorem leaf4281CoversExact : CoversExact 8
    leaf4281Box leaf4281Certificate leaf4281InnerLog leaf4281Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk97RoundedFacts chi273RoundedFacts
    innerPair595RoundedFacts leaf4281RoundedFacts (by rfl)

private theorem leaf4281FlatSound : Sound leaf4281Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4281CertificateValid
    leaf4281InnerLogValid leaf4281CoversExact leaf4281LowerChecked

private noncomputable def leaf4282Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (63/128), chiHi := (1/2) }

private noncomputable def leaf4282Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217949/134217728) }, vSqrt := { lower := (32765/32768), upper := (11452743679/11452219392) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (324096477/268435456) }, upper := { exponent := 1, mantissa := (79/64) } }, logOuter := sk97LogOuterCertificate, logK := sk97LogKCertificate, logChi := chi274LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (22904963071/22904438784) } }, logDArg := sk97LogDArgCertificate }

private noncomputable def leaf4282InnerLog : WideLogData :=
  innerPair589Data

set_option maxRecDepth 1000000 in
private theorem leaf4282LocalValidity :
    LeafFacts leaf4282Box leaf4282Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4282Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (11452743679/11452219392) }) = true
      norm_num [leaf4282Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4282CertificateValid :
    WideCertificateValid leaf4282Box leaf4282Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk97ValidityFacts chi274ValidityFacts
    leaf4282LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4282CoverageChecked :
    coverageCheck (innerAD leaf4282Box) leaf4282InnerLog = true := by
  rfl'

private theorem leaf4282InnerLogValid :
    leaf4282InnerLog.Valid 8 (innerAD leaf4282Box) :=
  wideLogDataValid_of_cachedCheck endpoint305PositiveFacts
    endpoint94PositiveFacts.valid leaf4282CoverageChecked

private noncomputable def leaf4282InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629465/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4282InputLogOnePlusV_eq :
    leaf4282InputLogOnePlusV = outerEnclosure 24
      (leaf4282Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4282RoundedFacts : LeafRoundedFacts 8
    leaf4282Certificate.logOnePlusV leaf4282InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4282InputLogOnePlusV_eq }

private noncomputable def leaf4282Inputs : Inputs :=
  inputsOfCaches globalInput sk97RoundedInputs
    chi274InputQChi innerPair589Input
    leaf4282InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4282LowerChecked :
    lowerCheck 24 leaf4282Box leaf4282Inputs = true := by
  rfl'

private theorem leaf4282CoversExact : CoversExact 8
    leaf4282Box leaf4282Certificate leaf4282InnerLog leaf4282Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk97RoundedFacts chi274RoundedFacts
    innerPair589RoundedFacts leaf4282RoundedFacts (by rfl)

private theorem leaf4282FlatSound : Sound leaf4282Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4282CertificateValid
    leaf4282InnerLogValid leaf4282CoversExact leaf4282LowerChecked

private noncomputable def leaf4283Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (95/32), chiLo := (15/32), chiHi := (61/128) }

private noncomputable def leaf4283Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435767/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34356771328) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (638002859/536870912) }, upper := { exponent := 1, mantissa := (9891/8192) } }, logOuter := sk113LogOuterCertificate, logK := sk113LogKCertificate, logChi := chi271LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715493887/68713542656) } }, logDArg := sk113LogDArgCertificate }

private noncomputable def leaf4283InnerLog : WideLogData :=
  innerPair278Data

set_option maxRecDepth 1000000 in
private theorem leaf4283LocalValidity :
    LeafFacts leaf4283Box leaf4283Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4283Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34356771328) }) = true
      norm_num [leaf4283Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4283CertificateValid :
    WideCertificateValid leaf4283Box leaf4283Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk113ValidityFacts chi271ValidityFacts
    leaf4283LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4283CoverageChecked :
    coverageCheck (innerAD leaf4283Box) leaf4283InnerLog = true := by
  rfl'

private theorem leaf4283InnerLogValid :
    leaf4283InnerLog.Valid 8 (innerAD leaf4283Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint78PositiveFacts.valid leaf4283CoverageChecked

private noncomputable def leaf4283InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629557/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4283InputLogOnePlusV_eq :
    leaf4283InputLogOnePlusV = outerEnclosure 24
      (leaf4283Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4283RoundedFacts : LeafRoundedFacts 8
    leaf4283Certificate.logOnePlusV leaf4283InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4283InputLogOnePlusV_eq }

private noncomputable def leaf4283Inputs : Inputs :=
  inputsOfCaches globalInput sk113RoundedInputs
    chi271InputQChi innerPair278Input
    leaf4283InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4283LowerChecked :
    lowerCheck 24 leaf4283Box leaf4283Inputs = true := by
  rfl'

private theorem leaf4283CoversExact : CoversExact 8
    leaf4283Box leaf4283Certificate leaf4283InnerLog leaf4283Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk113RoundedFacts chi271RoundedFacts
    innerPair278RoundedFacts leaf4283RoundedFacts (by rfl)

private theorem leaf4283FlatSound : Sound leaf4283Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4283CertificateValid
    leaf4283InnerLogValid leaf4283CoversExact leaf4283LowerChecked

private noncomputable def leaf4284Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (15/32), chiHi := (61/128) }

private noncomputable def leaf4284Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435769/268435456) }, vSqrt := { lower := (65529/65536), upper := (4908388937/4908105728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (641934777/536870912) }, upper := { exponent := 1, mantissa := (311/256) } }, logOuter := sk114LogOuterCertificate, logK := sk114LogKCertificate, logChi := chi271LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9816494665/9816211456) } }, logDArg := sk114LogDArgCertificate }

private noncomputable def leaf4284InnerLog : WideLogData :=
  innerPair278Data

set_option maxRecDepth 1000000 in
private theorem leaf4284LocalValidity :
    LeafFacts leaf4284Box leaf4284Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4284Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4908388937/4908105728) }) = true
      norm_num [leaf4284Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4284CertificateValid :
    WideCertificateValid leaf4284Box leaf4284Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk114ValidityFacts chi271ValidityFacts
    leaf4284LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4284CoverageChecked :
    coverageCheck (innerAD leaf4284Box) leaf4284InnerLog = true := by
  rfl'

private theorem leaf4284InnerLogValid :
    leaf4284InnerLog.Valid 8 (innerAD leaf4284Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint78PositiveFacts.valid leaf4284CoverageChecked

private noncomputable def leaf4284InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629565/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4284InputLogOnePlusV_eq :
    leaf4284InputLogOnePlusV = outerEnclosure 24
      (leaf4284Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4284RoundedFacts : LeafRoundedFacts 8
    leaf4284Certificate.logOnePlusV leaf4284InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4284InputLogOnePlusV_eq }

private noncomputable def leaf4284Inputs : Inputs :=
  inputsOfCaches globalInput sk114RoundedInputs
    chi271InputQChi innerPair278Input
    leaf4284InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4284LowerChecked :
    lowerCheck 24 leaf4284Box leaf4284Inputs = true := by
  rfl'

private theorem leaf4284CoversExact : CoversExact 8
    leaf4284Box leaf4284Certificate leaf4284InnerLog leaf4284Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk114RoundedFacts chi271RoundedFacts
    innerPair278RoundedFacts leaf4284RoundedFacts (by rfl)

private theorem leaf4284FlatSound : Sound leaf4284Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4284CertificateValid
    leaf4284InnerLogValid leaf4284CoversExact leaf4284LowerChecked

private noncomputable def leaf4285Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (95/32), chiLo := (61/128), chiHi := (31/64) }

private noncomputable def leaf4285Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435769/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34356722688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (644162865/536870912) }, upper := { exponent := 1, mantissa := (4993/4096) } }, logOuter := sk113LogOuterCertificate, logK := sk113LogKCertificate, logChi := chi272LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715445247/68713445376) } }, logDArg := sk113LogDArgCertificate }

private noncomputable def leaf4285InnerLog : WideLogData :=
  innerPair279Data

set_option maxRecDepth 1000000 in
private theorem leaf4285LocalValidity :
    LeafFacts leaf4285Box leaf4285Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4285Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34356722688) }) = true
      norm_num [leaf4285Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4285CertificateValid :
    WideCertificateValid leaf4285Box leaf4285Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk113ValidityFacts chi272ValidityFacts
    leaf4285LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4285CoverageChecked :
    coverageCheck (innerAD leaf4285Box) leaf4285InnerLog = true := by
  rfl'

private theorem leaf4285InnerLogValid :
    leaf4285InnerLog.Valid 8 (innerAD leaf4285Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint79PositiveFacts.valid leaf4285CoverageChecked

private noncomputable def leaf4285InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629569/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4285InputLogOnePlusV_eq :
    leaf4285InputLogOnePlusV = outerEnclosure 24
      (leaf4285Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4285RoundedFacts : LeafRoundedFacts 8
    leaf4285Certificate.logOnePlusV leaf4285InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4285InputLogOnePlusV_eq }

private noncomputable def leaf4285Inputs : Inputs :=
  inputsOfCaches globalInput sk113RoundedInputs
    chi272InputQChi innerPair279Input
    leaf4285InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4285LowerChecked :
    lowerCheck 24 leaf4285Box leaf4285Inputs = true := by
  rfl'

private theorem leaf4285CoversExact : CoversExact 8
    leaf4285Box leaf4285Certificate leaf4285InnerLog leaf4285Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk113RoundedFacts chi272RoundedFacts
    innerPair279RoundedFacts leaf4285RoundedFacts (by rfl)

private theorem leaf4285FlatSound : Sound leaf4285Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4285CertificateValid
    leaf4285InnerLogValid leaf4285CoversExact leaf4285LowerChecked

private noncomputable def leaf4286Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (61/128), chiHi := (31/64) }

private noncomputable def leaf4286Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435771/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356690944) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (648160315/536870912) }, upper := { exponent := 1, mantissa := (157/128) } }, logOuter := sk114LogOuterCertificate, logK := sk114LogKCertificate, logChi := chi272LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715413503/68713381888) } }, logDArg := sk114LogDArgCertificate }

private noncomputable def leaf4286InnerLog : WideLogData :=
  innerPair279Data

set_option maxRecDepth 1000000 in
private theorem leaf4286LocalValidity :
    LeafFacts leaf4286Box leaf4286Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4286Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356690944) }) = true
      norm_num [leaf4286Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4286CertificateValid :
    WideCertificateValid leaf4286Box leaf4286Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk114ValidityFacts chi272ValidityFacts
    leaf4286LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4286CoverageChecked :
    coverageCheck (innerAD leaf4286Box) leaf4286InnerLog = true := by
  rfl'

private theorem leaf4286InnerLogValid :
    leaf4286InnerLog.Valid 8 (innerAD leaf4286Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint79PositiveFacts.valid leaf4286CoverageChecked

private noncomputable def leaf4286InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629577/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4286InputLogOnePlusV_eq :
    leaf4286InputLogOnePlusV = outerEnclosure 24
      (leaf4286Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4286RoundedFacts : LeafRoundedFacts 8
    leaf4286Certificate.logOnePlusV leaf4286InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4286InputLogOnePlusV_eq }

private noncomputable def leaf4286Inputs : Inputs :=
  inputsOfCaches globalInput sk114RoundedInputs
    chi272InputQChi innerPair279Input
    leaf4286InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4286LowerChecked :
    lowerCheck 24 leaf4286Box leaf4286Inputs = true := by
  rfl'

private theorem leaf4286CoversExact : CoversExact 8
    leaf4286Box leaf4286Certificate leaf4286InnerLog leaf4286Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk114RoundedFacts chi272RoundedFacts
    innerPair279RoundedFacts leaf4286RoundedFacts (by rfl)

private theorem leaf4286FlatSound : Sound leaf4286Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4286CertificateValid
    leaf4286InnerLogValid leaf4286CoversExact leaf4286LowerChecked

private noncomputable def leaf4287Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (95/32), chiLo := (31/64), chiHi := (63/128) }

private noncomputable def leaf4287Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435771/268435456) }, vSqrt := { lower := (32765/32768), upper := (1108345889/1108279808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (650322871/536870912) }, upper := { exponent := 1, mantissa := (10081/8192) } }, logOuter := sk113LogOuterCertificate, logK := sk113LogKCertificate, logChi := chi273LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (2216625697/2216559616) } }, logDArg := sk113LogDArgCertificate }

private noncomputable def leaf4287InnerLog : WideLogData :=
  innerPair279Data

set_option maxRecDepth 1000000 in
private theorem leaf4287LocalValidity :
    LeafFacts leaf4287Box leaf4287Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4287Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (1108345889/1108279808) }) = true
      norm_num [leaf4287Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4287CertificateValid :
    WideCertificateValid leaf4287Box leaf4287Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk113ValidityFacts chi273ValidityFacts
    leaf4287LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4287CoverageChecked :
    coverageCheck (innerAD leaf4287Box) leaf4287InnerLog = true := by
  rfl'

private theorem leaf4287InnerLogValid :
    leaf4287InnerLog.Valid 8 (innerAD leaf4287Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint79PositiveFacts.valid leaf4287CoverageChecked

private noncomputable def leaf4287InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629581/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4287InputLogOnePlusV_eq :
    leaf4287InputLogOnePlusV = outerEnclosure 24
      (leaf4287Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4287RoundedFacts : LeafRoundedFacts 8
    leaf4287Certificate.logOnePlusV leaf4287InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4287InputLogOnePlusV_eq }

private noncomputable def leaf4287Inputs : Inputs :=
  inputsOfCaches globalInput sk113RoundedInputs
    chi273InputQChi innerPair279Input
    leaf4287InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4287LowerChecked :
    lowerCheck 24 leaf4287Box leaf4287Inputs = true := by
  rfl'

private theorem leaf4287CoversExact : CoversExact 8
    leaf4287Box leaf4287Certificate leaf4287InnerLog leaf4287Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk113RoundedFacts chi273RoundedFacts
    innerPair279RoundedFacts leaf4287RoundedFacts (by rfl)

private theorem leaf4287FlatSound : Sound leaf4287Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4287CertificateValid
    leaf4287InnerLogValid leaf4287CoversExact leaf4287LowerChecked

private noncomputable def leaf4288Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (31/64), chiHi := (63/128) }

private noncomputable def leaf4288Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435773/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34356641792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (654385853/536870912) }, upper := { exponent := 1, mantissa := (317/256) } }, logOuter := sk114LogOuterCertificate, logK := sk114LogKCertificate, logChi := chi273LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715364351/68713283584) } }, logDArg := sk114LogDArgCertificate }

private noncomputable def leaf4288InnerLog : WideLogData :=
  innerPair285Data

set_option maxRecDepth 1000000 in
private theorem leaf4288LocalValidity :
    LeafFacts leaf4288Box leaf4288Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4288Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34356641792) }) = true
      norm_num [leaf4288Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4288CertificateValid :
    WideCertificateValid leaf4288Box leaf4288Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk114ValidityFacts chi273ValidityFacts
    leaf4288LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4288CoverageChecked :
    coverageCheck (innerAD leaf4288Box) leaf4288InnerLog = true := by
  rfl'

private theorem leaf4288InnerLogValid :
    leaf4288InnerLog.Valid 8 (innerAD leaf4288Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint79PositiveFacts.valid leaf4288CoverageChecked

private noncomputable def leaf4288InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629589/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4288InputLogOnePlusV_eq :
    leaf4288InputLogOnePlusV = outerEnclosure 24
      (leaf4288Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4288RoundedFacts : LeafRoundedFacts 8
    leaf4288Certificate.logOnePlusV leaf4288InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4288InputLogOnePlusV_eq }

private noncomputable def leaf4288Inputs : Inputs :=
  inputsOfCaches globalInput sk114RoundedInputs
    chi273InputQChi innerPair285Input
    leaf4288InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4288LowerChecked :
    lowerCheck 24 leaf4288Box leaf4288Inputs = true := by
  rfl'

private theorem leaf4288CoversExact : CoversExact 8
    leaf4288Box leaf4288Certificate leaf4288InnerLog leaf4288Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk114RoundedFacts chi273RoundedFacts
    innerPair285RoundedFacts leaf4288RoundedFacts (by rfl)

private theorem leaf4288FlatSound : Sound leaf4288Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4288CertificateValid
    leaf4288InnerLogValid leaf4288CoversExact leaf4288LowerChecked

private noncomputable def leaf4289Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (63/128), chiHi := (1/2) }

private noncomputable def leaf4289Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217951/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34356592640) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (328224991/268435456) }, upper := { exponent := 1, mantissa := (5/4) } }, logOuter := sk98LogOuterCertificate, logK := sk98LogKCertificate, logChi := chi274LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68714823677/68713185280) } }, logDArg := sk98LogDArgCertificate }

private noncomputable def leaf4289InnerLog : WideLogData :=
  innerPair285Data

set_option maxRecDepth 1000000 in
private theorem leaf4289LocalValidity :
    LeafFacts leaf4289Box leaf4289Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4289Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34356592640) }) = true
      norm_num [leaf4289Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4289CertificateValid :
    WideCertificateValid leaf4289Box leaf4289Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk98ValidityFacts chi274ValidityFacts
    leaf4289LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4289CoverageChecked :
    coverageCheck (innerAD leaf4289Box) leaf4289InnerLog = true := by
  rfl'

private theorem leaf4289InnerLogValid :
    leaf4289InnerLog.Valid 8 (innerAD leaf4289Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint79PositiveFacts.valid leaf4289CoverageChecked

private noncomputable def leaf4289InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629481/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4289InputLogOnePlusV_eq :
    leaf4289InputLogOnePlusV = outerEnclosure 24
      (leaf4289Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4289RoundedFacts : LeafRoundedFacts 8
    leaf4289Certificate.logOnePlusV leaf4289InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4289InputLogOnePlusV_eq }

private noncomputable def leaf4289Inputs : Inputs :=
  inputsOfCaches globalInput sk98RoundedInputs
    chi274InputQChi innerPair285Input
    leaf4289InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4289LowerChecked :
    lowerCheck 24 leaf4289Box leaf4289Inputs = true := by
  rfl'

private theorem leaf4289CoversExact : CoversExact 8
    leaf4289Box leaf4289Certificate leaf4289InnerLog leaf4289Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk98RoundedFacts chi274RoundedFacts
    innerPair285RoundedFacts leaf4289RoundedFacts (by rfl)

private theorem leaf4289FlatSound : Sound leaf4289Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4289CertificateValid
    leaf4289InnerLogValid leaf4289CoversExact leaf4289LowerChecked

private noncomputable def component87Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (7/16), chiHi := (57/128) }

set_option maxRecDepth 1000000 in
private theorem component87Node0_sound : Sound component87Node0Box :=
  sound_of_literal_split component87Node0Box leaf4236Box leaf4237Box
    .k (89/32) (by rfl) (by rfl)
    leaf4236FlatSound leaf4237FlatSound

private noncomputable def component87Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (57/128), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component87Node1_sound : Sound component87Node1Box :=
  sound_of_literal_split component87Node1Box leaf4238Box leaf4239Box
    .k (89/32) (by rfl) (by rfl)
    leaf4238FlatSound leaf4239FlatSound

private noncomputable def component87Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (7/16), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component87Node2_sound : Sound component87Node2Box :=
  sound_of_literal_split component87Node2Box component87Node0Box component87Node1Box
    .chi (57/128) (by rfl) (by rfl)
    component87Node0_sound component87Node1_sound

private noncomputable def component87Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (29/64), chiHi := (59/128) }

set_option maxRecDepth 1000000 in
private theorem component87Node3_sound : Sound component87Node3Box :=
  sound_of_literal_split component87Node3Box leaf4240Box leaf4241Box
    .k (89/32) (by rfl) (by rfl)
    leaf4240FlatSound leaf4241FlatSound

private noncomputable def component87Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (59/128), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component87Node4_sound : Sound component87Node4Box :=
  sound_of_literal_split component87Node4Box leaf4242Box leaf4243Box
    .k (89/32) (by rfl) (by rfl)
    leaf4242FlatSound leaf4243FlatSound

private noncomputable def component87Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (29/64), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component87Node5_sound : Sound component87Node5Box :=
  sound_of_literal_split component87Node5Box component87Node3Box component87Node4Box
    .chi (59/128) (by rfl) (by rfl)
    component87Node3_sound component87Node4_sound

private noncomputable def component87Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (7/16), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component87Node6_sound : Sound component87Node6Box :=
  sound_of_literal_split component87Node6Box component87Node2Box component87Node5Box
    .chi (29/64) (by rfl) (by rfl)
    component87Node2_sound component87Node5_sound

private noncomputable def component87Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (7/16), chiHi := (57/128) }

set_option maxRecDepth 1000000 in
private theorem component87Node7_sound : Sound component87Node7Box :=
  sound_of_literal_split component87Node7Box leaf4244Box leaf4245Box
    .k (91/32) (by rfl) (by rfl)
    leaf4244FlatSound leaf4245FlatSound

private noncomputable def component87Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (57/128), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component87Node8_sound : Sound component87Node8Box :=
  sound_of_literal_split component87Node8Box leaf4246Box leaf4247Box
    .k (91/32) (by rfl) (by rfl)
    leaf4246FlatSound leaf4247FlatSound

private noncomputable def component87Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (7/16), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component87Node9_sound : Sound component87Node9Box :=
  sound_of_literal_split component87Node9Box component87Node7Box component87Node8Box
    .chi (57/128) (by rfl) (by rfl)
    component87Node7_sound component87Node8_sound

private noncomputable def component87Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (29/64), chiHi := (59/128) }

set_option maxRecDepth 1000000 in
private theorem component87Node10_sound : Sound component87Node10Box :=
  sound_of_literal_split component87Node10Box leaf4248Box leaf4249Box
    .k (91/32) (by rfl) (by rfl)
    leaf4248FlatSound leaf4249FlatSound

private noncomputable def component87Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (59/128), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component87Node11_sound : Sound component87Node11Box :=
  sound_of_literal_split component87Node11Box leaf4250Box leaf4251Box
    .k (91/32) (by rfl) (by rfl)
    leaf4250FlatSound leaf4251FlatSound

private noncomputable def component87Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (29/64), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component87Node12_sound : Sound component87Node12Box :=
  sound_of_literal_split component87Node12Box component87Node10Box component87Node11Box
    .chi (59/128) (by rfl) (by rfl)
    component87Node10_sound component87Node11_sound

private noncomputable def component87Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (7/16), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component87Node13_sound : Sound component87Node13Box :=
  sound_of_literal_split component87Node13Box component87Node9Box component87Node12Box
    .chi (29/64) (by rfl) (by rfl)
    component87Node9_sound component87Node12_sound

private noncomputable def component87Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (7/16), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component87Node14_sound : Sound component87Node14Box :=
  sound_of_literal_split component87Node14Box component87Node6Box component87Node13Box
    .k (45/16) (by rfl) (by rfl)
    component87Node6_sound component87Node13_sound

private noncomputable def component87Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (15/32), chiHi := (31/64) }

set_option maxRecDepth 1000000 in
private theorem component87Node15_sound : Sound component87Node15Box :=
  sound_of_literal_split component87Node15Box leaf4252Box leaf4253Box
    .chi (61/128) (by rfl) (by rfl)
    leaf4252FlatSound leaf4253FlatSound

private noncomputable def component87Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (31/64), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component87Node16_sound : Sound component87Node16Box :=
  sound_of_literal_split component87Node16Box leaf4254Box leaf4255Box
    .chi (63/128) (by rfl) (by rfl)
    leaf4254FlatSound leaf4255FlatSound

private noncomputable def component87Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (15/32), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component87Node17_sound : Sound component87Node17Box :=
  sound_of_literal_split component87Node17Box component87Node15Box component87Node16Box
    .chi (31/64) (by rfl) (by rfl)
    component87Node15_sound component87Node16_sound

private noncomputable def component87Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (15/32), chiHi := (61/128) }

set_option maxRecDepth 1000000 in
private theorem component87Node18_sound : Sound component87Node18Box :=
  sound_of_literal_split component87Node18Box leaf4256Box leaf4257Box
    .k (91/32) (by rfl) (by rfl)
    leaf4256FlatSound leaf4257FlatSound

private noncomputable def component87Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (15/32), chiHi := (31/64) }

set_option maxRecDepth 1000000 in
private theorem component87Node19_sound : Sound component87Node19Box :=
  sound_of_literal_split component87Node19Box component87Node18Box leaf4258Box
    .chi (61/128) (by rfl) (by rfl)
    component87Node18_sound leaf4258FlatSound

private noncomputable def component87Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (31/64), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component87Node20_sound : Sound component87Node20Box :=
  sound_of_literal_split component87Node20Box leaf4259Box leaf4260Box
    .chi (63/128) (by rfl) (by rfl)
    leaf4259FlatSound leaf4260FlatSound

private noncomputable def component87Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (15/32), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component87Node21_sound : Sound component87Node21Box :=
  sound_of_literal_split component87Node21Box component87Node19Box component87Node20Box
    .chi (31/64) (by rfl) (by rfl)
    component87Node19_sound component87Node20_sound

private noncomputable def component87Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (15/32), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component87Node22_sound : Sound component87Node22Box :=
  sound_of_literal_split component87Node22Box component87Node17Box component87Node21Box
    .k (45/16) (by rfl) (by rfl)
    component87Node17_sound component87Node21_sound

private noncomputable def component87Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (7/16), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component87Node23_sound : Sound component87Node23Box :=
  sound_of_literal_split component87Node23Box component87Node14Box component87Node22Box
    .chi (15/32) (by rfl) (by rfl)
    component87Node14_sound component87Node22_sound

private noncomputable def component87Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (7/16), chiHi := (57/128) }

set_option maxRecDepth 1000000 in
private theorem component87Node24_sound : Sound component87Node24Box :=
  sound_of_literal_split component87Node24Box leaf4261Box leaf4262Box
    .k (93/32) (by rfl) (by rfl)
    leaf4261FlatSound leaf4262FlatSound

private noncomputable def component87Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (57/128), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component87Node25_sound : Sound component87Node25Box :=
  sound_of_literal_split component87Node25Box leaf4263Box leaf4264Box
    .k (93/32) (by rfl) (by rfl)
    leaf4263FlatSound leaf4264FlatSound

private noncomputable def component87Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (7/16), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component87Node26_sound : Sound component87Node26Box :=
  sound_of_literal_split component87Node26Box component87Node24Box component87Node25Box
    .chi (57/128) (by rfl) (by rfl)
    component87Node24_sound component87Node25_sound

private noncomputable def component87Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (29/64), chiHi := (59/128) }

set_option maxRecDepth 1000000 in
private theorem component87Node27_sound : Sound component87Node27Box :=
  sound_of_literal_split component87Node27Box leaf4265Box leaf4266Box
    .k (93/32) (by rfl) (by rfl)
    leaf4265FlatSound leaf4266FlatSound

private noncomputable def component87Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (59/128), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component87Node28_sound : Sound component87Node28Box :=
  sound_of_literal_split component87Node28Box leaf4267Box leaf4268Box
    .k (93/32) (by rfl) (by rfl)
    leaf4267FlatSound leaf4268FlatSound

private noncomputable def component87Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (29/64), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component87Node29_sound : Sound component87Node29Box :=
  sound_of_literal_split component87Node29Box component87Node27Box component87Node28Box
    .chi (59/128) (by rfl) (by rfl)
    component87Node27_sound component87Node28_sound

private noncomputable def component87Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (7/16), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component87Node30_sound : Sound component87Node30Box :=
  sound_of_literal_split component87Node30Box component87Node26Box component87Node29Box
    .chi (29/64) (by rfl) (by rfl)
    component87Node26_sound component87Node29_sound

private noncomputable def component87Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (7/16), chiHi := (57/128) }

set_option maxRecDepth 1000000 in
private theorem component87Node31_sound : Sound component87Node31Box :=
  sound_of_literal_split component87Node31Box leaf4269Box leaf4270Box
    .k (95/32) (by rfl) (by rfl)
    leaf4269FlatSound leaf4270FlatSound

private noncomputable def component87Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (57/128), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component87Node32_sound : Sound component87Node32Box :=
  sound_of_literal_split component87Node32Box leaf4271Box leaf4272Box
    .k (95/32) (by rfl) (by rfl)
    leaf4271FlatSound leaf4272FlatSound

private noncomputable def component87Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (7/16), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component87Node33_sound : Sound component87Node33Box :=
  sound_of_literal_split component87Node33Box component87Node31Box component87Node32Box
    .chi (57/128) (by rfl) (by rfl)
    component87Node31_sound component87Node32_sound

private noncomputable def component87Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (29/64), chiHi := (59/128) }

set_option maxRecDepth 1000000 in
private theorem component87Node34_sound : Sound component87Node34Box :=
  sound_of_literal_split component87Node34Box leaf4273Box leaf4274Box
    .k (95/32) (by rfl) (by rfl)
    leaf4273FlatSound leaf4274FlatSound

private noncomputable def component87Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (59/128), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component87Node35_sound : Sound component87Node35Box :=
  sound_of_literal_split component87Node35Box leaf4275Box leaf4276Box
    .k (95/32) (by rfl) (by rfl)
    leaf4275FlatSound leaf4276FlatSound

private noncomputable def component87Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (29/64), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component87Node36_sound : Sound component87Node36Box :=
  sound_of_literal_split component87Node36Box component87Node34Box component87Node35Box
    .chi (59/128) (by rfl) (by rfl)
    component87Node34_sound component87Node35_sound

private noncomputable def component87Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (7/16), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component87Node37_sound : Sound component87Node37Box :=
  sound_of_literal_split component87Node37Box component87Node33Box component87Node36Box
    .chi (29/64) (by rfl) (by rfl)
    component87Node33_sound component87Node36_sound

private noncomputable def component87Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (7/16), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component87Node38_sound : Sound component87Node38Box :=
  sound_of_literal_split component87Node38Box component87Node30Box component87Node37Box
    .k (47/16) (by rfl) (by rfl)
    component87Node30_sound component87Node37_sound

private noncomputable def component87Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (15/32), chiHi := (61/128) }

set_option maxRecDepth 1000000 in
private theorem component87Node39_sound : Sound component87Node39Box :=
  sound_of_literal_split component87Node39Box leaf4277Box leaf4278Box
    .k (93/32) (by rfl) (by rfl)
    leaf4277FlatSound leaf4278FlatSound

private noncomputable def component87Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (61/128), chiHi := (31/64) }

set_option maxRecDepth 1000000 in
private theorem component87Node40_sound : Sound component87Node40Box :=
  sound_of_literal_split component87Node40Box leaf4279Box leaf4280Box
    .k (93/32) (by rfl) (by rfl)
    leaf4279FlatSound leaf4280FlatSound

private noncomputable def component87Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (15/32), chiHi := (31/64) }

set_option maxRecDepth 1000000 in
private theorem component87Node41_sound : Sound component87Node41Box :=
  sound_of_literal_split component87Node41Box component87Node39Box component87Node40Box
    .chi (61/128) (by rfl) (by rfl)
    component87Node39_sound component87Node40_sound

private noncomputable def component87Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (31/64), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component87Node42_sound : Sound component87Node42Box :=
  sound_of_literal_split component87Node42Box leaf4281Box leaf4282Box
    .chi (63/128) (by rfl) (by rfl)
    leaf4281FlatSound leaf4282FlatSound

private noncomputable def component87Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (15/32), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component87Node43_sound : Sound component87Node43Box :=
  sound_of_literal_split component87Node43Box component87Node41Box component87Node42Box
    .chi (31/64) (by rfl) (by rfl)
    component87Node41_sound component87Node42_sound

private noncomputable def component87Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (15/32), chiHi := (61/128) }

set_option maxRecDepth 1000000 in
private theorem component87Node44_sound : Sound component87Node44Box :=
  sound_of_literal_split component87Node44Box leaf4283Box leaf4284Box
    .k (95/32) (by rfl) (by rfl)
    leaf4283FlatSound leaf4284FlatSound

private noncomputable def component87Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (61/128), chiHi := (31/64) }

set_option maxRecDepth 1000000 in
private theorem component87Node45_sound : Sound component87Node45Box :=
  sound_of_literal_split component87Node45Box leaf4285Box leaf4286Box
    .k (95/32) (by rfl) (by rfl)
    leaf4285FlatSound leaf4286FlatSound

private noncomputable def component87Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (15/32), chiHi := (31/64) }

set_option maxRecDepth 1000000 in
private theorem component87Node46_sound : Sound component87Node46Box :=
  sound_of_literal_split component87Node46Box component87Node44Box component87Node45Box
    .chi (61/128) (by rfl) (by rfl)
    component87Node44_sound component87Node45_sound

private noncomputable def component87Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (31/64), chiHi := (63/128) }

set_option maxRecDepth 1000000 in
private theorem component87Node47_sound : Sound component87Node47Box :=
  sound_of_literal_split component87Node47Box leaf4287Box leaf4288Box
    .k (95/32) (by rfl) (by rfl)
    leaf4287FlatSound leaf4288FlatSound

private noncomputable def component87Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (31/64), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component87Node48_sound : Sound component87Node48Box :=
  sound_of_literal_split component87Node48Box component87Node47Box leaf4289Box
    .chi (63/128) (by rfl) (by rfl)
    component87Node47_sound leaf4289FlatSound

private noncomputable def component87Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (15/32), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component87Node49_sound : Sound component87Node49Box :=
  sound_of_literal_split component87Node49Box component87Node46Box component87Node48Box
    .chi (31/64) (by rfl) (by rfl)
    component87Node46_sound component87Node48_sound

private noncomputable def component87Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (15/32), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component87Node50_sound : Sound component87Node50Box :=
  sound_of_literal_split component87Node50Box component87Node43Box component87Node49Box
    .k (47/16) (by rfl) (by rfl)
    component87Node43_sound component87Node49_sound

private noncomputable def component87Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (7/16), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component87Node51_sound : Sound component87Node51Box :=
  sound_of_literal_split component87Node51Box component87Node38Box component87Node50Box
    .chi (15/32) (by rfl) (by rfl)
    component87Node38_sound component87Node50_sound

noncomputable def component87Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (3), chiLo := (7/16), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
theorem component87_sound : Sound component87Box :=
  sound_of_literal_split component87Box component87Node23Box component87Node51Box
    .k (23/8) (by rfl) (by rfl)
    component87Node23_sound component87Node51_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
