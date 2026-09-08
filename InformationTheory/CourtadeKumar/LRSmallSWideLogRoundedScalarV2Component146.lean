import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch7
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch9
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
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

private noncomputable def leaf7164Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (3/4), chiHi := (49/64) }

private noncomputable def leaf7164Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109075/67108864) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34354018304) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (243225903/134217728) }, upper := { exponent := 1, mantissa := (3817/2048) } }, logOuter := sk151LogOuterCertificate, logK := sk151LogKCertificate, logChi := chi345LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68711200763/68708036608) } }, logDArg := sk151LogDArgCertificate }

private noncomputable def leaf7164InnerLog : WideLogData :=
  innerPair795Data

set_option maxRecDepth 1000000 in
private theorem leaf7164LocalValidity :
    LeafFacts leaf7164Box leaf7164Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7164Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34354018304) }) = true
      norm_num [leaf7164Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7164CertificateValid :
    WideCertificateValid leaf7164Box leaf7164Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk151ValidityFacts chi345ValidityFacts
    leaf7164LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7164CoverageChecked :
    coverageCheck (innerAD leaf7164Box) leaf7164InnerLog = true := by
  rfl'

private theorem leaf7164InnerLogValid :
    leaf7164InnerLog.Valid 8 (innerAD leaf7164Box) :=
  wideLogDataValid_of_cachedCheck endpoint498PositiveFacts
    endpoint502PositiveFacts.valid leaf7164CoverageChecked

private noncomputable def leaf7164InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629853/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7164InputLogOnePlusV_eq :
    leaf7164InputLogOnePlusV = outerEnclosure 24
      (leaf7164Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7164RoundedFacts : LeafRoundedFacts 8
    leaf7164Certificate.logOnePlusV leaf7164InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7164InputLogOnePlusV_eq }

private noncomputable def leaf7164Inputs : Inputs :=
  inputsOfCaches globalInput sk151RoundedInputs
    chi345InputQChi innerPair795Input
    leaf7164InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7164LowerChecked :
    lowerCheck 24 leaf7164Box leaf7164Inputs = true := by
  rfl'

private theorem leaf7164CoversExact : CoversExact 8
    leaf7164Box leaf7164Certificate leaf7164InnerLog leaf7164Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk151RoundedFacts chi345RoundedFacts
    innerPair795RoundedFacts leaf7164RoundedFacts (by rfl)

private theorem leaf7164FlatSound : Sound leaf7164Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7164CertificateValid
    leaf7164InnerLogValid leaf7164CoversExact leaf7164LowerChecked

private noncomputable def leaf7165Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (3/4), chiHi := (49/64) }

private noncomputable def leaf7165Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109077/67108864) }, vSqrt := { lower := (8191/8192), upper := (11452394153/11451305984) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (246371437/134217728) }, upper := { exponent := 1, mantissa := (1933/1024) } }, logOuter := sk152LogOuterCertificate, logK := sk152LogKCertificate, logChi := chi345LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (22903700137/22902611968) } }, logDArg := sk152LogDArgCertificate }

private noncomputable def leaf7165InnerLog : WideLogData :=
  innerPair799Data

set_option maxRecDepth 1000000 in
private theorem leaf7165LocalValidity :
    LeafFacts leaf7165Box leaf7165Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7165Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (11452394153/11451305984) }) = true
      norm_num [leaf7165Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7165CertificateValid :
    WideCertificateValid leaf7165Box leaf7165Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk152ValidityFacts chi345ValidityFacts
    leaf7165LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7165CoverageChecked :
    coverageCheck (innerAD leaf7165Box) leaf7165InnerLog = true := by
  rfl'

private theorem leaf7165InnerLogValid :
    leaf7165InnerLog.Valid 8 (innerAD leaf7165Box) :=
  wideLogDataValid_of_cachedCheck endpoint500PositiveFacts
    endpoint503PositiveFacts.valid leaf7165CoverageChecked

private noncomputable def leaf7165InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814939/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf7165InputLogOnePlusV_eq :
    leaf7165InputLogOnePlusV = outerEnclosure 24
      (leaf7165Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7165RoundedFacts : LeafRoundedFacts 8
    leaf7165Certificate.logOnePlusV leaf7165InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7165InputLogOnePlusV_eq }

private noncomputable def leaf7165Inputs : Inputs :=
  inputsOfCaches globalInput sk152RoundedInputs
    chi345InputQChi innerPair799Input
    leaf7165InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7165LowerChecked :
    lowerCheck 24 leaf7165Box leaf7165Inputs = true := by
  rfl'

private theorem leaf7165CoversExact : CoversExact 8
    leaf7165Box leaf7165Certificate leaf7165InnerLog leaf7165Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk152RoundedFacts chi345RoundedFacts
    innerPair799RoundedFacts leaf7165RoundedFacts (by rfl)

private theorem leaf7165FlatSound : Sound leaf7165Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7165CertificateValid
    leaf7165InnerLogValid leaf7165CoversExact leaf7165LowerChecked

private noncomputable def leaf7166Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (49/64), chiHi := (25/32) }

private noncomputable def leaf7166Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109077/67108864) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34353901568) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (246895693/134217728) }, upper := { exponent := 1, mantissa := (1937/1024) } }, logOuter := sk151LogOuterCertificate, logK := sk151LogKCertificate, logChi := chi346LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68711084027/68707803136) } }, logDArg := sk151LogDArgCertificate }

private noncomputable def leaf7166InnerLog : WideLogData :=
  innerPair799Data

set_option maxRecDepth 1000000 in
private theorem leaf7166LocalValidity :
    LeafFacts leaf7166Box leaf7166Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7166Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34353901568) }) = true
      norm_num [leaf7166Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7166CertificateValid :
    WideCertificateValid leaf7166Box leaf7166Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk151ValidityFacts chi346ValidityFacts
    leaf7166LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7166CoverageChecked :
    coverageCheck (innerAD leaf7166Box) leaf7166InnerLog = true := by
  rfl'

private theorem leaf7166InnerLogValid :
    leaf7166InnerLog.Valid 8 (innerAD leaf7166Box) :=
  wideLogDataValid_of_cachedCheck endpoint500PositiveFacts
    endpoint503PositiveFacts.valid leaf7166CoverageChecked

private noncomputable def leaf7166InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814941/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf7166InputLogOnePlusV_eq :
    leaf7166InputLogOnePlusV = outerEnclosure 24
      (leaf7166Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7166RoundedFacts : LeafRoundedFacts 8
    leaf7166Certificate.logOnePlusV leaf7166InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7166InputLogOnePlusV_eq }

private noncomputable def leaf7166Inputs : Inputs :=
  inputsOfCaches globalInput sk151RoundedInputs
    chi346InputQChi innerPair799Input
    leaf7166InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7166LowerChecked :
    lowerCheck 24 leaf7166Box leaf7166Inputs = true := by
  rfl'

private theorem leaf7166CoversExact : CoversExact 8
    leaf7166Box leaf7166Certificate leaf7166InnerLog leaf7166Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk151RoundedFacts chi346RoundedFacts
    innerPair799RoundedFacts leaf7166RoundedFacts (by rfl)

private theorem leaf7166FlatSound : Sound leaf7166Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7166CertificateValid
    leaf7166InnerLogValid leaf7166CoversExact leaf7166LowerChecked

private noncomputable def leaf7167Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (49/64), chiHi := (25/32) }

private noncomputable def leaf7167Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109079/67108864) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34353799168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (250106759/134217728) }, upper := { exponent := 1, mantissa := (981/512) } }, logOuter := sk152LogOuterCertificate, logK := sk152LogKCertificate, logChi := chi346LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68710981627/68707598336) } }, logDArg := sk152LogDArgCertificate }

private noncomputable def leaf7167InnerLog : WideLogData :=
  innerPair802Data

set_option maxRecDepth 1000000 in
private theorem leaf7167LocalValidity :
    LeafFacts leaf7167Box leaf7167Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7167Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34353799168) }) = true
      norm_num [leaf7167Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7167CertificateValid :
    WideCertificateValid leaf7167Box leaf7167Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk152ValidityFacts chi346ValidityFacts
    leaf7167LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7167CoverageChecked :
    coverageCheck (innerAD leaf7167Box) leaf7167InnerLog = true := by
  rfl'

private theorem leaf7167InnerLogValid :
    leaf7167InnerLog.Valid 8 (innerAD leaf7167Box) :=
  wideLogDataValid_of_cachedCheck endpoint501PositiveFacts
    endpoint504PositiveFacts.valid leaf7167CoverageChecked

private noncomputable def leaf7167InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629907/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7167InputLogOnePlusV_eq :
    leaf7167InputLogOnePlusV = outerEnclosure 24
      (leaf7167Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7167RoundedFacts : LeafRoundedFacts 8
    leaf7167Certificate.logOnePlusV leaf7167InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7167InputLogOnePlusV_eq }

private noncomputable def leaf7167Inputs : Inputs :=
  inputsOfCaches globalInput sk152RoundedInputs
    chi346InputQChi innerPair802Input
    leaf7167InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7167LowerChecked :
    lowerCheck 24 leaf7167Box leaf7167Inputs = true := by
  rfl'

private theorem leaf7167CoversExact : CoversExact 8
    leaf7167Box leaf7167Certificate leaf7167InnerLog leaf7167Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk152RoundedFacts chi346RoundedFacts
    innerPair802RoundedFacts leaf7167RoundedFacts (by rfl)

private theorem leaf7167FlatSound : Sound leaf7167Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7167CertificateValid
    leaf7167InnerLogValid leaf7167CoversExact leaf7167LowerChecked

private noncomputable def leaf7168Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (25/32), chiHi := (51/64) }

private noncomputable def leaf7168Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109079/67108864) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34353784832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (250565483/134217728) }, upper := { exponent := 1, mantissa := (3931/2048) } }, logOuter := sk151LogOuterCertificate, logK := sk151LogKCertificate, logChi := chi361LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68710967291/68707569664) } }, logDArg := sk151LogDArgCertificate }

private noncomputable def leaf7168InnerLog : WideLogData :=
  innerPair802Data

set_option maxRecDepth 1000000 in
private theorem leaf7168LocalValidity :
    LeafFacts leaf7168Box leaf7168Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7168Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34353784832) }) = true
      norm_num [leaf7168Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7168CertificateValid :
    WideCertificateValid leaf7168Box leaf7168Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk151ValidityFacts chi361ValidityFacts
    leaf7168LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7168CoverageChecked :
    coverageCheck (innerAD leaf7168Box) leaf7168InnerLog = true := by
  rfl'

private theorem leaf7168InnerLogValid :
    leaf7168InnerLog.Valid 8 (innerAD leaf7168Box) :=
  wideLogDataValid_of_cachedCheck endpoint501PositiveFacts
    endpoint504PositiveFacts.valid leaf7168CoverageChecked

private noncomputable def leaf7168InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814955/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf7168InputLogOnePlusV_eq :
    leaf7168InputLogOnePlusV = outerEnclosure 24
      (leaf7168Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7168RoundedFacts : LeafRoundedFacts 8
    leaf7168Certificate.logOnePlusV leaf7168InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7168InputLogOnePlusV_eq }

private noncomputable def leaf7168Inputs : Inputs :=
  inputsOfCaches globalInput sk151RoundedInputs
    chi361InputQChi innerPair802Input
    leaf7168InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7168LowerChecked :
    lowerCheck 24 leaf7168Box leaf7168Inputs = true := by
  rfl'

private theorem leaf7168CoversExact : CoversExact 8
    leaf7168Box leaf7168Certificate leaf7168InnerLog leaf7168Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk151RoundedFacts chi361RoundedFacts
    innerPair802RoundedFacts leaf7168RoundedFacts (by rfl)

private theorem leaf7168FlatSound : Sound leaf7168Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7168CertificateValid
    leaf7168InnerLogValid leaf7168CoversExact leaf7168LowerChecked

private noncomputable def leaf7169Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (25/32), chiHi := (51/64) }

private noncomputable def leaf7169Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109081/67108864) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34353680384) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (253842081/134217728) }, upper := { exponent := 1, mantissa := (1991/1024) } }, logOuter := sk152LogOuterCertificate, logK := sk152LogKCertificate, logChi := chi361LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68710862843/68707360768) } }, logDArg := sk152LogDArgCertificate }

private noncomputable def leaf7169InnerLog : WideLogData :=
  innerPair806Data

set_option maxRecDepth 1000000 in
private theorem leaf7169LocalValidity :
    LeafFacts leaf7169Box leaf7169Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7169Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34353680384) }) = true
      norm_num [leaf7169Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7169CertificateValid :
    WideCertificateValid leaf7169Box leaf7169Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk152ValidityFacts chi361ValidityFacts
    leaf7169LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7169CoverageChecked :
    coverageCheck (innerAD leaf7169Box) leaf7169InnerLog = true := by
  rfl'

private theorem leaf7169InnerLogValid :
    leaf7169InnerLog.Valid 8 (innerAD leaf7169Box) :=
  wideLogDataValid_of_cachedCheck endpoint502PositiveFacts
    endpoint505PositiveFacts.valid leaf7169CoverageChecked

private noncomputable def leaf7169InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726871/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf7169InputLogOnePlusV_eq :
    leaf7169InputLogOnePlusV = outerEnclosure 24
      (leaf7169Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7169RoundedFacts : LeafRoundedFacts 8
    leaf7169Certificate.logOnePlusV leaf7169InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7169InputLogOnePlusV_eq }

private noncomputable def leaf7169Inputs : Inputs :=
  inputsOfCaches globalInput sk152RoundedInputs
    chi361InputQChi innerPair806Input
    leaf7169InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7169LowerChecked :
    lowerCheck 24 leaf7169Box leaf7169Inputs = true := by
  rfl'

private theorem leaf7169CoversExact : CoversExact 8
    leaf7169Box leaf7169Certificate leaf7169InnerLog leaf7169Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk152RoundedFacts chi361RoundedFacts
    innerPair806RoundedFacts leaf7169RoundedFacts (by rfl)

private theorem leaf7169FlatSound : Sound leaf7169Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7169CertificateValid
    leaf7169InnerLogValid leaf7169CoversExact leaf7169LowerChecked

private noncomputable def leaf7170Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (51/64), chiHi := (13/16) }

private noncomputable def leaf7170Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109081/67108864) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34353668096) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (254235273/134217728) }, upper := { exponent := 1, mantissa := (997/512) } }, logOuter := sk151LogOuterCertificate, logK := sk151LogKCertificate, logChi := chi362LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68710850555/68707336192) } }, logDArg := sk151LogDArgCertificate }

private noncomputable def leaf7170InnerLog : WideLogData :=
  innerPair806Data

set_option maxRecDepth 1000000 in
private theorem leaf7170LocalValidity :
    LeafFacts leaf7170Box leaf7170Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7170Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34353668096) }) = true
      norm_num [leaf7170Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7170CertificateValid :
    WideCertificateValid leaf7170Box leaf7170Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk151ValidityFacts chi362ValidityFacts
    leaf7170LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7170CoverageChecked :
    coverageCheck (innerAD leaf7170Box) leaf7170InnerLog = true := by
  rfl'

private theorem leaf7170InnerLogValid :
    leaf7170InnerLog.Valid 8 (innerAD leaf7170Box) :=
  wideLogDataValid_of_cachedCheck endpoint502PositiveFacts
    endpoint505PositiveFacts.valid leaf7170CoverageChecked

private noncomputable def leaf7170InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629939/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7170InputLogOnePlusV_eq :
    leaf7170InputLogOnePlusV = outerEnclosure 24
      (leaf7170Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7170RoundedFacts : LeafRoundedFacts 8
    leaf7170Certificate.logOnePlusV leaf7170InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7170InputLogOnePlusV_eq }

private noncomputable def leaf7170Inputs : Inputs :=
  inputsOfCaches globalInput sk151RoundedInputs
    chi362InputQChi innerPair806Input
    leaf7170InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7170LowerChecked :
    lowerCheck 24 leaf7170Box leaf7170Inputs = true := by
  rfl'

private theorem leaf7170CoversExact : CoversExact 8
    leaf7170Box leaf7170Certificate leaf7170InnerLog leaf7170Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk151RoundedFacts chi362RoundedFacts
    innerPair806RoundedFacts leaf7170RoundedFacts (by rfl)

private theorem leaf7170FlatSound : Sound leaf7170Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7170CertificateValid
    leaf7170InnerLogValid leaf7170CoversExact leaf7170LowerChecked

private noncomputable def leaf7171Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (51/64), chiHi := (13/16) }

private noncomputable def leaf7171Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109083/67108864) }, vSqrt := { lower := (8191/8192), upper := (11452394153/11451187200) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (257577403/134217728) }, upper := { exponent := 1, mantissa := (505/256) } }, logOuter := sk152LogOuterCertificate, logK := sk152LogKCertificate, logChi := chi362LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (22903581353/22902374400) } }, logDArg := sk152LogDArgCertificate }

private noncomputable def leaf7171InnerLog : WideLogData :=
  innerPair809Data

set_option maxRecDepth 1000000 in
private theorem leaf7171LocalValidity :
    LeafFacts leaf7171Box leaf7171Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7171Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (11452394153/11451187200) }) = true
      norm_num [leaf7171Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7171CertificateValid :
    WideCertificateValid leaf7171Box leaf7171Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk152ValidityFacts chi362ValidityFacts
    leaf7171LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7171CoverageChecked :
    coverageCheck (innerAD leaf7171Box) leaf7171InnerLog = true := by
  rfl'

private theorem leaf7171InnerLogValid :
    leaf7171InnerLog.Valid 8 (innerAD leaf7171Box) :=
  wideLogDataValid_of_cachedCheck endpoint503PositiveFacts
    endpoint506PositiveFacts.valid leaf7171CoverageChecked

private noncomputable def leaf7171InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629965/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7171InputLogOnePlusV_eq :
    leaf7171InputLogOnePlusV = outerEnclosure 24
      (leaf7171Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7171RoundedFacts : LeafRoundedFacts 8
    leaf7171Certificate.logOnePlusV leaf7171InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7171InputLogOnePlusV_eq }

private noncomputable def leaf7171Inputs : Inputs :=
  inputsOfCaches globalInput sk152RoundedInputs
    chi362InputQChi innerPair809Input
    leaf7171InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7171LowerChecked :
    lowerCheck 24 leaf7171Box leaf7171Inputs = true := by
  rfl'

private theorem leaf7171CoversExact : CoversExact 8
    leaf7171Box leaf7171Certificate leaf7171InnerLog leaf7171Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk152RoundedFacts chi362RoundedFacts
    innerPair809RoundedFacts leaf7171RoundedFacts (by rfl)

private theorem leaf7171FlatSound : Sound leaf7171Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7171CertificateValid
    leaf7171InnerLogValid leaf7171CoversExact leaf7171LowerChecked

private noncomputable def leaf7172Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (3/4), chiHi := (49/64) }

private noncomputable def leaf7172Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109079/67108864) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34353817600) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (249516971/134217728) }, upper := { exponent := 1, mantissa := (3915/2048) } }, logOuter := sk153LogOuterCertificate, logK := sk153LogKCertificate, logChi := chi345LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68711000059/68707635200) } }, logDArg := sk153LogDArgCertificate }

private noncomputable def leaf7172InnerLog : WideLogData :=
  innerPair802Data

set_option maxRecDepth 1000000 in
private theorem leaf7172LocalValidity :
    LeafFacts leaf7172Box leaf7172Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7172Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34353817600) }) = true
      norm_num [leaf7172Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7172CertificateValid :
    WideCertificateValid leaf7172Box leaf7172Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk153ValidityFacts chi345ValidityFacts
    leaf7172LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7172CoverageChecked :
    coverageCheck (innerAD leaf7172Box) leaf7172InnerLog = true := by
  rfl'

private theorem leaf7172InnerLogValid :
    leaf7172InnerLog.Valid 8 (innerAD leaf7172Box) :=
  wideLogDataValid_of_cachedCheck endpoint501PositiveFacts
    endpoint504PositiveFacts.valid leaf7172CoverageChecked

private noncomputable def leaf7172InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814951/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf7172InputLogOnePlusV_eq :
    leaf7172InputLogOnePlusV = outerEnclosure 24
      (leaf7172Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7172RoundedFacts : LeafRoundedFacts 8
    leaf7172Certificate.logOnePlusV leaf7172InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7172InputLogOnePlusV_eq }

private noncomputable def leaf7172Inputs : Inputs :=
  inputsOfCaches globalInput sk153RoundedInputs
    chi345InputQChi innerPair802Input
    leaf7172InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7172LowerChecked :
    lowerCheck 24 leaf7172Box leaf7172Inputs = true := by
  rfl'

private theorem leaf7172CoversExact : CoversExact 8
    leaf7172Box leaf7172Certificate leaf7172InnerLog leaf7172Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk153RoundedFacts chi345RoundedFacts
    innerPair802RoundedFacts leaf7172RoundedFacts (by rfl)

private theorem leaf7172FlatSound : Sound leaf7172Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7172CertificateValid
    leaf7172InnerLogValid leaf7172CoversExact leaf7172LowerChecked

private noncomputable def leaf7173Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (3/4), chiHi := (49/64) }

private noncomputable def leaf7173Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109081/67108864) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34353717248) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (252662505/134217728) }, upper := { exponent := 1, mantissa := (991/512) } }, logOuter := sk154LogOuterCertificate, logK := sk154LogKCertificate, logChi := chi345LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68710899707/68707434496) } }, logDArg := sk154LogDArgCertificate }

private noncomputable def leaf7173InnerLog : WideLogData :=
  innerPair805Data

set_option maxRecDepth 1000000 in
private theorem leaf7173LocalValidity :
    LeafFacts leaf7173Box leaf7173Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7173Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34353717248) }) = true
      norm_num [leaf7173Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7173CertificateValid :
    WideCertificateValid leaf7173Box leaf7173Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk154ValidityFacts chi345ValidityFacts
    leaf7173LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7173CoverageChecked :
    coverageCheck (innerAD leaf7173Box) leaf7173InnerLog = true := by
  rfl'

private theorem leaf7173InnerLogValid :
    leaf7173InnerLog.Valid 8 (innerAD leaf7173Box) :=
  wideLogDataValid_of_cachedCheck endpoint502PositiveFacts
    endpoint504PositiveFacts.valid leaf7173CoverageChecked

private noncomputable def leaf7173InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629927/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7173InputLogOnePlusV_eq :
    leaf7173InputLogOnePlusV = outerEnclosure 24
      (leaf7173Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7173RoundedFacts : LeafRoundedFacts 8
    leaf7173Certificate.logOnePlusV leaf7173InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7173InputLogOnePlusV_eq }

private noncomputable def leaf7173Inputs : Inputs :=
  inputsOfCaches globalInput sk154RoundedInputs
    chi345InputQChi innerPair805Input
    leaf7173InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7173LowerChecked :
    lowerCheck 24 leaf7173Box leaf7173Inputs = true := by
  rfl'

private theorem leaf7173CoversExact : CoversExact 8
    leaf7173Box leaf7173Certificate leaf7173InnerLog leaf7173Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk154RoundedFacts chi345RoundedFacts
    innerPair805RoundedFacts leaf7173RoundedFacts (by rfl)

private theorem leaf7173FlatSound : Sound leaf7173Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7173CertificateValid
    leaf7173InnerLogValid leaf7173CoversExact leaf7173LowerChecked

private noncomputable def leaf7174Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (49/64), chiHi := (25/32) }

private noncomputable def leaf7174Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109081/67108864) }, vSqrt := { lower := (8191/8192), upper := (11452394153/11451232256) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (253317825/134217728) }, upper := { exponent := 1, mantissa := (1987/1024) } }, logOuter := sk153LogOuterCertificate, logK := sk153LogKCertificate, logChi := chi346LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (22903626409/22902464512) } }, logDArg := sk153LogDArgCertificate }

private noncomputable def leaf7174InnerLog : WideLogData :=
  innerPair806Data

set_option maxRecDepth 1000000 in
private theorem leaf7174LocalValidity :
    LeafFacts leaf7174Box leaf7174Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7174Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (11452394153/11451232256) }) = true
      norm_num [leaf7174Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7174CertificateValid :
    WideCertificateValid leaf7174Box leaf7174Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk153ValidityFacts chi346ValidityFacts
    leaf7174LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7174CoverageChecked :
    coverageCheck (innerAD leaf7174Box) leaf7174InnerLog = true := by
  rfl'

private theorem leaf7174InnerLogValid :
    leaf7174InnerLog.Valid 8 (innerAD leaf7174Box) :=
  wideLogDataValid_of_cachedCheck endpoint502PositiveFacts
    endpoint505PositiveFacts.valid leaf7174CoverageChecked

private noncomputable def leaf7174InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907483/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf7174InputLogOnePlusV_eq :
    leaf7174InputLogOnePlusV = outerEnclosure 24
      (leaf7174Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7174RoundedFacts : LeafRoundedFacts 8
    leaf7174Certificate.logOnePlusV leaf7174InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7174InputLogOnePlusV_eq }

private noncomputable def leaf7174Inputs : Inputs :=
  inputsOfCaches globalInput sk153RoundedInputs
    chi346InputQChi innerPair806Input
    leaf7174InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7174LowerChecked :
    lowerCheck 24 leaf7174Box leaf7174Inputs = true := by
  rfl'

private theorem leaf7174CoversExact : CoversExact 8
    leaf7174Box leaf7174Certificate leaf7174InnerLog leaf7174Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk153RoundedFacts chi346RoundedFacts
    innerPair806RoundedFacts leaf7174RoundedFacts (by rfl)

private theorem leaf7174FlatSound : Sound leaf7174Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7174CertificateValid
    leaf7174InnerLogValid leaf7174CoversExact leaf7174LowerChecked

private noncomputable def leaf7175Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (49/64), chiHi := (25/32) }

private noncomputable def leaf7175Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109083/67108864) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34353594368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (256528891/134217728) }, upper := { exponent := 1, mantissa := (503/256) } }, logOuter := sk154LogOuterCertificate, logK := sk154LogKCertificate, logChi := chi346LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68710776827/68707188736) } }, logDArg := sk154LogDArgCertificate }

private noncomputable def leaf7175InnerLog : WideLogData :=
  innerPair808Data

set_option maxRecDepth 1000000 in
private theorem leaf7175LocalValidity :
    LeafFacts leaf7175Box leaf7175Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7175Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34353594368) }) = true
      norm_num [leaf7175Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7175CertificateValid :
    WideCertificateValid leaf7175Box leaf7175Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk154ValidityFacts chi346ValidityFacts
    leaf7175LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7175CoverageChecked :
    coverageCheck (innerAD leaf7175Box) leaf7175InnerLog = true := by
  rfl'

private theorem leaf7175InnerLogValid :
    leaf7175InnerLog.Valid 8 (innerAD leaf7175Box) :=
  wideLogDataValid_of_cachedCheck endpoint503PositiveFacts
    endpoint505PositiveFacts.valid leaf7175CoverageChecked

private noncomputable def leaf7175InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629957/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7175InputLogOnePlusV_eq :
    leaf7175InputLogOnePlusV = outerEnclosure 24
      (leaf7175Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7175RoundedFacts : LeafRoundedFacts 8
    leaf7175Certificate.logOnePlusV leaf7175InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7175InputLogOnePlusV_eq }

private noncomputable def leaf7175Inputs : Inputs :=
  inputsOfCaches globalInput sk154RoundedInputs
    chi346InputQChi innerPair808Input
    leaf7175InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7175LowerChecked :
    lowerCheck 24 leaf7175Box leaf7175Inputs = true := by
  rfl'

private theorem leaf7175CoversExact : CoversExact 8
    leaf7175Box leaf7175Certificate leaf7175InnerLog leaf7175Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk154RoundedFacts chi346RoundedFacts
    innerPair808RoundedFacts leaf7175RoundedFacts (by rfl)

private theorem leaf7175FlatSound : Sound leaf7175Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7175CertificateValid
    leaf7175InnerLogValid leaf7175CoversExact leaf7175LowerChecked

private noncomputable def leaf7176Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (25/32), chiHi := (51/64) }

private noncomputable def leaf7176Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109083/67108864) }, vSqrt := { lower := (8191/8192), upper := (1808272761/1808082944) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (257118679/134217728) }, upper := { exponent := 1, mantissa := (4033/2048) } }, logOuter := sk153LogOuterCertificate, logK := sk153LogKCertificate, logChi := chi361LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (3616355705/3616165888) } }, logDArg := sk153LogDArgCertificate }

private noncomputable def leaf7176InnerLog : WideLogData :=
  innerPair809Data

set_option maxRecDepth 1000000 in
private theorem leaf7176LocalValidity :
    LeafFacts leaf7176Box leaf7176Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7176Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (1808272761/1808082944) }) = true
      norm_num [leaf7176Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7176CertificateValid :
    WideCertificateValid leaf7176Box leaf7176Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk153ValidityFacts chi361ValidityFacts
    leaf7176LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7176CoverageChecked :
    coverageCheck (innerAD leaf7176Box) leaf7176InnerLog = true := by
  rfl'

private theorem leaf7176InnerLogValid :
    leaf7176InnerLog.Valid 8 (innerAD leaf7176Box) :=
  wideLogDataValid_of_cachedCheck endpoint503PositiveFacts
    endpoint506PositiveFacts.valid leaf7176CoverageChecked

private noncomputable def leaf7176InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629961/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7176InputLogOnePlusV_eq :
    leaf7176InputLogOnePlusV = outerEnclosure 24
      (leaf7176Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7176RoundedFacts : LeafRoundedFacts 8
    leaf7176Certificate.logOnePlusV leaf7176InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7176InputLogOnePlusV_eq }

private noncomputable def leaf7176Inputs : Inputs :=
  inputsOfCaches globalInput sk153RoundedInputs
    chi361InputQChi innerPair809Input
    leaf7176InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7176LowerChecked :
    lowerCheck 24 leaf7176Box leaf7176Inputs = true := by
  rfl'

private theorem leaf7176CoversExact : CoversExact 8
    leaf7176Box leaf7176Certificate leaf7176InnerLog leaf7176Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk153RoundedFacts chi361RoundedFacts
    innerPair809RoundedFacts leaf7176RoundedFacts (by rfl)

private theorem leaf7176FlatSound : Sound leaf7176Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7176CertificateValid
    leaf7176InnerLogValid leaf7176CoversExact leaf7176LowerChecked

private noncomputable def leaf7177Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (25/32), chiHi := (51/64) }

private noncomputable def leaf7177Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109085/67108864) }, vSqrt := { lower := (8191/8192), upper := (17178329085/17176735744) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (260395277/134217728) }, upper := { exponent := 1, mantissa := (1021/512) } }, logOuter := sk154LogOuterCertificate, logK := sk154LogKCertificate, logChi := chi361LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34355064829/34353471488) } }, logDArg := sk154LogDArgCertificate }

private noncomputable def leaf7177InnerLog : WideLogData :=
  innerPair811Data

set_option maxRecDepth 1000000 in
private theorem leaf7177LocalValidity :
    LeafFacts leaf7177Box leaf7177Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7177Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178329085/17176735744) }) = true
      norm_num [leaf7177Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7177CertificateValid :
    WideCertificateValid leaf7177Box leaf7177Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk154ValidityFacts chi361ValidityFacts
    leaf7177LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7177CoverageChecked :
    coverageCheck (innerAD leaf7177Box) leaf7177InnerLog = true := by
  rfl'

private theorem leaf7177InnerLogValid :
    leaf7177InnerLog.Valid 8 (innerAD leaf7177Box) :=
  wideLogDataValid_of_cachedCheck endpoint504PositiveFacts
    endpoint506PositiveFacts.valid leaf7177CoverageChecked

private noncomputable def leaf7177InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629859/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7177InputLogOnePlusV_eq :
    leaf7177InputLogOnePlusV = outerEnclosure 24
      (leaf7177Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7177RoundedFacts : LeafRoundedFacts 8
    leaf7177Certificate.logOnePlusV leaf7177InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7177InputLogOnePlusV_eq }

private noncomputable def leaf7177Inputs : Inputs :=
  inputsOfCaches globalInput sk154RoundedInputs
    chi361InputQChi innerPair811Input
    leaf7177InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7177LowerChecked :
    lowerCheck 24 leaf7177Box leaf7177Inputs = true := by
  rfl'

private theorem leaf7177CoversExact : CoversExact 8
    leaf7177Box leaf7177Certificate leaf7177InnerLog leaf7177Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk154RoundedFacts chi361RoundedFacts
    innerPair811RoundedFacts leaf7177RoundedFacts (by rfl)

private theorem leaf7177FlatSound : Sound leaf7177Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7177CertificateValid
    leaf7177InnerLogValid leaf7177CoversExact leaf7177LowerChecked

private noncomputable def leaf7178Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (51/64), chiHi := (13/16) }

private noncomputable def leaf7178Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109085/67108864) }, vSqrt := { lower := (8191/8192), upper := (17178329085/17176727552) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (260919533/134217728) }, upper := { exponent := 1, mantissa := (1023/512) } }, logOuter := sk153LogOuterCertificate, logK := sk153LogKCertificate, logChi := chi362LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34355056637/34353455104) } }, logDArg := sk153LogDArgCertificate }

private noncomputable def leaf7178InnerLog : WideLogData :=
  innerPair811Data

set_option maxRecDepth 1000000 in
private theorem leaf7178LocalValidity :
    LeafFacts leaf7178Box leaf7178Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7178Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178329085/17176727552) }) = true
      norm_num [leaf7178Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7178CertificateValid :
    WideCertificateValid leaf7178Box leaf7178Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk153ValidityFacts chi362ValidityFacts
    leaf7178LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7178CoverageChecked :
    coverageCheck (innerAD leaf7178Box) leaf7178InnerLog = true := by
  rfl'

private theorem leaf7178InnerLogValid :
    leaf7178InnerLog.Valid 8 (innerAD leaf7178Box) :=
  wideLogDataValid_of_cachedCheck endpoint504PositiveFacts
    endpoint506PositiveFacts.valid leaf7178CoverageChecked

private noncomputable def leaf7178InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629863/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7178InputLogOnePlusV_eq :
    leaf7178InputLogOnePlusV = outerEnclosure 24
      (leaf7178Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7178RoundedFacts : LeafRoundedFacts 8
    leaf7178Certificate.logOnePlusV leaf7178InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7178InputLogOnePlusV_eq }

private noncomputable def leaf7178Inputs : Inputs :=
  inputsOfCaches globalInput sk153RoundedInputs
    chi362InputQChi innerPair811Input
    leaf7178InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7178LowerChecked :
    lowerCheck 24 leaf7178Box leaf7178Inputs = true := by
  rfl'

private theorem leaf7178CoversExact : CoversExact 8
    leaf7178Box leaf7178Certificate leaf7178InnerLog leaf7178Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk153RoundedFacts chi362RoundedFacts
    innerPair811RoundedFacts leaf7178RoundedFacts (by rfl)

private theorem leaf7178FlatSound : Sound leaf7178Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7178CertificateValid
    leaf7178InnerLogValid leaf7178CoversExact leaf7178LowerChecked

private noncomputable def leaf7179Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (51/64), chiHi := (13/16) }

private noncomputable def leaf7179Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109087/67108864) }, vSqrt := { lower := (8191/8192), upper := (17178329085/17176674304) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (264261663/134217728) }, upper := { exponent := 2, mantissa := (259/256) } }, logOuter := sk154LogOuterCertificate, logK := sk154LogKCertificate, logChi := chi362LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34355003389/34353348608) } }, logDArg := sk154LogDArgCertificate }

private noncomputable def leaf7179InnerLog : WideLogData :=
  innerPair814Data

set_option maxRecDepth 1000000 in
private theorem leaf7179LocalValidity :
    LeafFacts leaf7179Box leaf7179Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7179Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178329085/17176674304) }) = true
      norm_num [leaf7179Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7179CertificateValid :
    WideCertificateValid leaf7179Box leaf7179Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk154ValidityFacts chi362ValidityFacts
    leaf7179LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7179CoverageChecked :
    coverageCheck (innerAD leaf7179Box) leaf7179InnerLog = true := by
  rfl'

private theorem leaf7179InnerLogValid :
    leaf7179InnerLog.Valid 8 (innerAD leaf7179Box) :=
  wideLogDataValid_of_cachedCheck endpoint505PositiveFacts
    endpoint582PositiveFacts.valid leaf7179CoverageChecked

private noncomputable def leaf7179InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629889/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7179InputLogOnePlusV_eq :
    leaf7179InputLogOnePlusV = outerEnclosure 24
      (leaf7179Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7179RoundedFacts : LeafRoundedFacts 8
    leaf7179Certificate.logOnePlusV leaf7179InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7179InputLogOnePlusV_eq }

private noncomputable def leaf7179Inputs : Inputs :=
  inputsOfCaches globalInput sk154RoundedInputs
    chi362InputQChi innerPair814Input
    leaf7179InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7179LowerChecked :
    lowerCheck 24 leaf7179Box leaf7179Inputs = true := by
  rfl'

private theorem leaf7179CoversExact : CoversExact 8
    leaf7179Box leaf7179Certificate leaf7179InnerLog leaf7179Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk154RoundedFacts chi362RoundedFacts
    innerPair814RoundedFacts leaf7179RoundedFacts (by rfl)

private theorem leaf7179FlatSound : Sound leaf7179Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7179CertificateValid
    leaf7179InnerLogValid leaf7179CoversExact leaf7179LowerChecked

private noncomputable def leaf7180Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (13/16), chiHi := (53/64) }

private noncomputable def leaf7180Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109083/67108864) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34353551360) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (257905063/134217728) }, upper := { exponent := 1, mantissa := (4045/2048) } }, logOuter := sk151LogOuterCertificate, logK := sk151LogKCertificate, logChi := chi363LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68710733819/68707102720) } }, logDArg := sk151LogDArgCertificate }

private noncomputable def leaf7180InnerLog : WideLogData :=
  innerPair809Data

set_option maxRecDepth 1000000 in
private theorem leaf7180LocalValidity :
    LeafFacts leaf7180Box leaf7180Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7180Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34353551360) }) = true
      norm_num [leaf7180Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7180CertificateValid :
    WideCertificateValid leaf7180Box leaf7180Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk151ValidityFacts chi363ValidityFacts
    leaf7180LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7180CoverageChecked :
    coverageCheck (innerAD leaf7180Box) leaf7180InnerLog = true := by
  rfl'

private theorem leaf7180InnerLogValid :
    leaf7180InnerLog.Valid 8 (innerAD leaf7180Box) :=
  wideLogDataValid_of_cachedCheck endpoint503PositiveFacts
    endpoint506PositiveFacts.valid leaf7180CoverageChecked

private noncomputable def leaf7180InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629967/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7180InputLogOnePlusV_eq :
    leaf7180InputLogOnePlusV = outerEnclosure 24
      (leaf7180Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7180RoundedFacts : LeafRoundedFacts 8
    leaf7180Certificate.logOnePlusV leaf7180InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7180InputLogOnePlusV_eq }

private noncomputable def leaf7180Inputs : Inputs :=
  inputsOfCaches globalInput sk151RoundedInputs
    chi363InputQChi innerPair809Input
    leaf7180InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7180LowerChecked :
    lowerCheck 24 leaf7180Box leaf7180Inputs = true := by
  rfl'

private theorem leaf7180CoversExact : CoversExact 8
    leaf7180Box leaf7180Certificate leaf7180InnerLog leaf7180Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk151RoundedFacts chi363RoundedFacts
    innerPair809RoundedFacts leaf7180RoundedFacts (by rfl)

private theorem leaf7180FlatSound : Sound leaf7180Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7180CertificateValid
    leaf7180InnerLogValid leaf7180CoversExact leaf7180LowerChecked

private noncomputable def leaf7181Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (13/16), chiHi := (53/64) }

private noncomputable def leaf7181Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109085/67108864) }, vSqrt := { lower := (8191/8192), upper := (17178329085/17176721408) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (261312725/134217728) }, upper := { exponent := 2, mantissa := (2049/2048) } }, logOuter := sk152LogOuterCertificate, logK := sk152LogKCertificate, logChi := chi363LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34355050493/34353442816) } }, logDArg := sk152LogDArgCertificate }

private noncomputable def leaf7181InnerLog : WideLogData :=
  innerPair812Data

set_option maxRecDepth 1000000 in
private theorem leaf7181LocalValidity :
    LeafFacts leaf7181Box leaf7181Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7181Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178329085/17176721408) }) = true
      norm_num [leaf7181Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7181CertificateValid :
    WideCertificateValid leaf7181Box leaf7181Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk152ValidityFacts chi363ValidityFacts
    leaf7181LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7181CoverageChecked :
    coverageCheck (innerAD leaf7181Box) leaf7181InnerLog = true := by
  rfl'

private theorem leaf7181InnerLogValid :
    leaf7181InnerLog.Valid 8 (innerAD leaf7181Box) :=
  wideLogDataValid_of_cachedCheck endpoint504PositiveFacts
    endpoint582PositiveFacts.valid leaf7181CoverageChecked

private noncomputable def leaf7181InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814933/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf7181InputLogOnePlusV_eq :
    leaf7181InputLogOnePlusV = outerEnclosure 24
      (leaf7181Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7181RoundedFacts : LeafRoundedFacts 8
    leaf7181Certificate.logOnePlusV leaf7181InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7181InputLogOnePlusV_eq }

private noncomputable def leaf7181Inputs : Inputs :=
  inputsOfCaches globalInput sk152RoundedInputs
    chi363InputQChi innerPair812Input
    leaf7181InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7181LowerChecked :
    lowerCheck 24 leaf7181Box leaf7181Inputs = true := by
  rfl'

private theorem leaf7181CoversExact : CoversExact 8
    leaf7181Box leaf7181Certificate leaf7181InnerLog leaf7181Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk152RoundedFacts chi363RoundedFacts
    innerPair812RoundedFacts leaf7181RoundedFacts (by rfl)

private theorem leaf7181FlatSound : Sound leaf7181Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7181CertificateValid
    leaf7181InnerLogValid leaf7181CoversExact leaf7181LowerChecked

private noncomputable def leaf7182Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (53/64), chiHi := (27/32) }

private noncomputable def leaf7182Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109085/67108864) }, vSqrt := { lower := (8191/8192), upper := (17178329085/17176717312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (261574853/134217728) }, upper := { exponent := 2, mantissa := (2051/2048) } }, logOuter := sk151LogOuterCertificate, logK := sk151LogKCertificate, logChi := chi364LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34355046397/34353434624) } }, logDArg := sk151LogDArgCertificate }

private noncomputable def leaf7182InnerLog : WideLogData :=
  innerPair812Data

set_option maxRecDepth 1000000 in
private theorem leaf7182LocalValidity :
    LeafFacts leaf7182Box leaf7182Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7182Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178329085/17176717312) }) = true
      norm_num [leaf7182Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7182CertificateValid :
    WideCertificateValid leaf7182Box leaf7182Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk151ValidityFacts chi364ValidityFacts
    leaf7182LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7182CoverageChecked :
    coverageCheck (innerAD leaf7182Box) leaf7182InnerLog = true := by
  rfl'

private theorem leaf7182InnerLogValid :
    leaf7182InnerLog.Valid 8 (innerAD leaf7182Box) :=
  wideLogDataValid_of_cachedCheck endpoint504PositiveFacts
    endpoint582PositiveFacts.valid leaf7182CoverageChecked

private noncomputable def leaf7182InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907467/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf7182InputLogOnePlusV_eq :
    leaf7182InputLogOnePlusV = outerEnclosure 24
      (leaf7182Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7182RoundedFacts : LeafRoundedFacts 8
    leaf7182Certificate.logOnePlusV leaf7182InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7182InputLogOnePlusV_eq }

private noncomputable def leaf7182Inputs : Inputs :=
  inputsOfCaches globalInput sk151RoundedInputs
    chi364InputQChi innerPair812Input
    leaf7182InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7182LowerChecked :
    lowerCheck 24 leaf7182Box leaf7182Inputs = true := by
  rfl'

private theorem leaf7182CoversExact : CoversExact 8
    leaf7182Box leaf7182Certificate leaf7182InnerLog leaf7182Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk151RoundedFacts chi364RoundedFacts
    innerPair812RoundedFacts leaf7182RoundedFacts (by rfl)

private theorem leaf7182FlatSound : Sound leaf7182Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7182CertificateValid
    leaf7182InnerLogValid leaf7182CoversExact leaf7182LowerChecked

private noncomputable def leaf7183Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (53/64), chiHi := (27/32) }

private noncomputable def leaf7183Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109087/67108864) }, vSqrt := { lower := (8191/8192), upper := (17178329085/17176662016) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (265048047/134217728) }, upper := { exponent := 2, mantissa := (1039/1024) } }, logOuter := sk152LogOuterCertificate, logK := sk152LogKCertificate, logChi := chi364LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34354991101/34353324032) } }, logDArg := sk152LogDArgCertificate }

private noncomputable def leaf7183InnerLog : WideLogData :=
  innerPair814Data

set_option maxRecDepth 1000000 in
private theorem leaf7183LocalValidity :
    LeafFacts leaf7183Box leaf7183Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7183Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178329085/17176662016) }) = true
      norm_num [leaf7183Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7183CertificateValid :
    WideCertificateValid leaf7183Box leaf7183Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk152ValidityFacts chi364ValidityFacts
    leaf7183LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7183CoverageChecked :
    coverageCheck (innerAD leaf7183Box) leaf7183InnerLog = true := by
  rfl'

private theorem leaf7183InnerLogValid :
    leaf7183InnerLog.Valid 8 (innerAD leaf7183Box) :=
  wideLogDataValid_of_cachedCheck endpoint505PositiveFacts
    endpoint582PositiveFacts.valid leaf7183CoverageChecked

private noncomputable def leaf7183InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629895/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7183InputLogOnePlusV_eq :
    leaf7183InputLogOnePlusV = outerEnclosure 24
      (leaf7183Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7183RoundedFacts : LeafRoundedFacts 8
    leaf7183Certificate.logOnePlusV leaf7183InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7183InputLogOnePlusV_eq }

private noncomputable def leaf7183Inputs : Inputs :=
  inputsOfCaches globalInput sk152RoundedInputs
    chi364InputQChi innerPair814Input
    leaf7183InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7183LowerChecked :
    lowerCheck 24 leaf7183Box leaf7183Inputs = true := by
  rfl'

private theorem leaf7183CoversExact : CoversExact 8
    leaf7183Box leaf7183Certificate leaf7183InnerLog leaf7183Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk152RoundedFacts chi364RoundedFacts
    innerPair814RoundedFacts leaf7183RoundedFacts (by rfl)

private theorem leaf7183FlatSound : Sound leaf7183Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7183CertificateValid
    leaf7183InnerLogValid leaf7183CoversExact leaf7183LowerChecked

private noncomputable def leaf7184Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (27/32), chiHi := (55/64) }

private noncomputable def leaf7184Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109087/67108864) }, vSqrt := { lower := (8191/8192), upper := (17178329085/17176658944) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (265244643/134217728) }, upper := { exponent := 2, mantissa := (4159/4096) } }, logOuter := sk151LogOuterCertificate, logK := sk151LogKCertificate, logChi := chi365LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34354988029/34353317888) } }, logDArg := sk151LogDArgCertificate }

private noncomputable def leaf7184InnerLog : WideLogData :=
  innerPair814Data

set_option maxRecDepth 1000000 in
private theorem leaf7184LocalValidity :
    LeafFacts leaf7184Box leaf7184Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7184Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178329085/17176658944) }) = true
      norm_num [leaf7184Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7184CertificateValid :
    WideCertificateValid leaf7184Box leaf7184Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk151ValidityFacts chi365ValidityFacts
    leaf7184LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7184CoverageChecked :
    coverageCheck (innerAD leaf7184Box) leaf7184InnerLog = true := by
  rfl'

private theorem leaf7184InnerLogValid :
    leaf7184InnerLog.Valid 8 (innerAD leaf7184Box) :=
  wideLogDataValid_of_cachedCheck endpoint505PositiveFacts
    endpoint582PositiveFacts.valid leaf7184CoverageChecked

private noncomputable def leaf7184InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453737/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf7184InputLogOnePlusV_eq :
    leaf7184InputLogOnePlusV = outerEnclosure 24
      (leaf7184Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7184RoundedFacts : LeafRoundedFacts 8
    leaf7184Certificate.logOnePlusV leaf7184InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7184InputLogOnePlusV_eq }

private noncomputable def leaf7184Inputs : Inputs :=
  inputsOfCaches globalInput sk151RoundedInputs
    chi365InputQChi innerPair814Input
    leaf7184InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7184LowerChecked :
    lowerCheck 24 leaf7184Box leaf7184Inputs = true := by
  rfl'

private theorem leaf7184CoversExact : CoversExact 8
    leaf7184Box leaf7184Certificate leaf7184InnerLog leaf7184Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk151RoundedFacts chi365RoundedFacts
    innerPair814RoundedFacts leaf7184RoundedFacts (by rfl)

private theorem leaf7184FlatSound : Sound leaf7184Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7184CertificateValid
    leaf7184InnerLogValid leaf7184CoversExact leaf7184LowerChecked

private noncomputable def leaf7185Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (27/32), chiHi := (55/64) }

private noncomputable def leaf7185Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109089/67108864) }, vSqrt := { lower := (8191/8192), upper := (5726109695/5725534208) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (268783369/268435456) }, upper := { exponent := 2, mantissa := (2107/2048) } }, logOuter := sk152LogOuterCertificate, logK := sk152LogKCertificate, logChi := chi365LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (11451643903/11451068416) } }, logDArg := sk152LogDArgCertificate }

private noncomputable def leaf7185InnerLog : WideLogData :=
  innerPair817Data

set_option maxRecDepth 1000000 in
private theorem leaf7185LocalValidity :
    LeafFacts leaf7185Box leaf7185Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7185Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5726109695/5725534208) }) = true
      norm_num [leaf7185Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7185CertificateValid :
    WideCertificateValid leaf7185Box leaf7185Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk152ValidityFacts chi365ValidityFacts
    leaf7185LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7185CoverageChecked :
    coverageCheck (innerAD leaf7185Box) leaf7185InnerLog = true := by
  rfl'

private theorem leaf7185InnerLogValid :
    leaf7185InnerLog.Valid 8 (innerAD leaf7185Box) :=
  wideLogDataValid_of_cachedCheck endpoint506PositiveFacts
    endpoint583PositiveFacts.valid leaf7185CoverageChecked

private noncomputable def leaf7185InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907481/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf7185InputLogOnePlusV_eq :
    leaf7185InputLogOnePlusV = outerEnclosure 24
      (leaf7185Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7185RoundedFacts : LeafRoundedFacts 8
    leaf7185Certificate.logOnePlusV leaf7185InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7185InputLogOnePlusV_eq }

private noncomputable def leaf7185Inputs : Inputs :=
  inputsOfCaches globalInput sk152RoundedInputs
    chi365InputQChi innerPair817Input
    leaf7185InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7185LowerChecked :
    lowerCheck 24 leaf7185Box leaf7185Inputs = true := by
  rfl'

private theorem leaf7185CoversExact : CoversExact 8
    leaf7185Box leaf7185Certificate leaf7185InnerLog leaf7185Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk152RoundedFacts chi365RoundedFacts
    innerPair817RoundedFacts leaf7185RoundedFacts (by rfl)

private theorem leaf7185FlatSound : Sound leaf7185Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7185CertificateValid
    leaf7185InnerLogValid leaf7185CoversExact leaf7185LowerChecked

private noncomputable def leaf7186Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (55/64), chiHi := (7/8) }

private noncomputable def leaf7186Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109089/67108864) }, vSqrt := { lower := (8191/8192), upper := (17178329085/17176600576) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (268914433/268435456) }, upper := { exponent := 2, mantissa := (527/512) } }, logOuter := sk151LogOuterCertificate, logK := sk151LogKCertificate, logChi := chi366LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34354929661/34353201152) } }, logDArg := sk151LogDArgCertificate }

private noncomputable def leaf7186InnerLog : WideLogData :=
  innerPair817Data

set_option maxRecDepth 1000000 in
private theorem leaf7186LocalValidity :
    LeafFacts leaf7186Box leaf7186Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7186Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178329085/17176600576) }) = true
      norm_num [leaf7186Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7186CertificateValid :
    WideCertificateValid leaf7186Box leaf7186Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk151ValidityFacts chi366ValidityFacts
    leaf7186LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7186CoverageChecked :
    coverageCheck (innerAD leaf7186Box) leaf7186InnerLog = true := by
  rfl'

private theorem leaf7186InnerLogValid :
    leaf7186InnerLog.Valid 8 (innerAD leaf7186Box) :=
  wideLogDataValid_of_cachedCheck endpoint506PositiveFacts
    endpoint583PositiveFacts.valid leaf7186CoverageChecked

private noncomputable def leaf7186InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629925/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7186InputLogOnePlusV_eq :
    leaf7186InputLogOnePlusV = outerEnclosure 24
      (leaf7186Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7186RoundedFacts : LeafRoundedFacts 8
    leaf7186Certificate.logOnePlusV leaf7186InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7186InputLogOnePlusV_eq }

private noncomputable def leaf7186Inputs : Inputs :=
  inputsOfCaches globalInput sk151RoundedInputs
    chi366InputQChi innerPair817Input
    leaf7186InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7186LowerChecked :
    lowerCheck 24 leaf7186Box leaf7186Inputs = true := by
  rfl'

private theorem leaf7186CoversExact : CoversExact 8
    leaf7186Box leaf7186Certificate leaf7186InnerLog leaf7186Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk151RoundedFacts chi366RoundedFacts
    innerPair817RoundedFacts leaf7186RoundedFacts (by rfl)

private theorem leaf7186FlatSound : Sound leaf7186Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7186CertificateValid
    leaf7186InnerLogValid leaf7186CoversExact leaf7186LowerChecked

private noncomputable def leaf7187Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (55/64), chiHi := (7/8) }

private noncomputable def leaf7187Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109091/67108864) }, vSqrt := { lower := (8191/8192), upper := (17178329085/17176543232) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (272518691/268435456) }, upper := { exponent := 2, mantissa := (267/256) } }, logOuter := sk152LogOuterCertificate, logK := sk152LogKCertificate, logChi := chi366LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34354872317/34353086464) } }, logDArg := sk152LogDArgCertificate }

private noncomputable def leaf7187InnerLog : WideLogData :=
  innerPair818Data

set_option maxRecDepth 1000000 in
private theorem leaf7187LocalValidity :
    LeafFacts leaf7187Box leaf7187Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7187Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178329085/17176543232) }) = true
      norm_num [leaf7187Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7187CertificateValid :
    WideCertificateValid leaf7187Box leaf7187Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk152ValidityFacts chi366ValidityFacts
    leaf7187LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7187CoverageChecked :
    coverageCheck (innerAD leaf7187Box) leaf7187InnerLog = true := by
  rfl'

private theorem leaf7187InnerLogValid :
    leaf7187InnerLog.Valid 8 (innerAD leaf7187Box) :=
  wideLogDataValid_of_cachedCheck endpoint506PositiveFacts
    endpoint584PositiveFacts.valid leaf7187CoverageChecked

private noncomputable def leaf7187InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629953/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7187InputLogOnePlusV_eq :
    leaf7187InputLogOnePlusV = outerEnclosure 24
      (leaf7187Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7187RoundedFacts : LeafRoundedFacts 8
    leaf7187Certificate.logOnePlusV leaf7187InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7187InputLogOnePlusV_eq }

private noncomputable def leaf7187Inputs : Inputs :=
  inputsOfCaches globalInput sk152RoundedInputs
    chi366InputQChi innerPair818Input
    leaf7187InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7187LowerChecked :
    lowerCheck 24 leaf7187Box leaf7187Inputs = true := by
  rfl'

private theorem leaf7187CoversExact : CoversExact 8
    leaf7187Box leaf7187Certificate leaf7187InnerLog leaf7187Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk152RoundedFacts chi366RoundedFacts
    innerPair818RoundedFacts leaf7187RoundedFacts (by rfl)

private theorem leaf7187FlatSound : Sound leaf7187Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7187CertificateValid
    leaf7187InnerLogValid leaf7187CoversExact leaf7187LowerChecked

private noncomputable def leaf7188Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (13/16), chiHi := (53/64) }

private noncomputable def leaf7188Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109087/67108864) }, vSqrt := { lower := (8191/8192), upper := (5726109695/5725555712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (264720387/134217728) }, upper := { exponent := 2, mantissa := (4151/4096) } }, logOuter := sk153LogOuterCertificate, logK := sk153LogKCertificate, logChi := chi363LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (11451665407/11451111424) } }, logDArg := sk153LogDArgCertificate }

private noncomputable def leaf7188InnerLog : WideLogData :=
  innerPair814Data

set_option maxRecDepth 1000000 in
private theorem leaf7188LocalValidity :
    LeafFacts leaf7188Box leaf7188Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7188Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5726109695/5725555712) }) = true
      norm_num [leaf7188Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7188CertificateValid :
    WideCertificateValid leaf7188Box leaf7188Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk153ValidityFacts chi363ValidityFacts
    leaf7188LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7188CoverageChecked :
    coverageCheck (innerAD leaf7188Box) leaf7188InnerLog = true := by
  rfl'

private theorem leaf7188InnerLogValid :
    leaf7188InnerLog.Valid 8 (innerAD leaf7188Box) :=
  wideLogDataValid_of_cachedCheck endpoint505PositiveFacts
    endpoint582PositiveFacts.valid leaf7188CoverageChecked

private noncomputable def leaf7188InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907473/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf7188InputLogOnePlusV_eq :
    leaf7188InputLogOnePlusV = outerEnclosure 24
      (leaf7188Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7188RoundedFacts : LeafRoundedFacts 8
    leaf7188Certificate.logOnePlusV leaf7188InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7188InputLogOnePlusV_eq }

private noncomputable def leaf7188Inputs : Inputs :=
  inputsOfCaches globalInput sk153RoundedInputs
    chi363InputQChi innerPair814Input
    leaf7188InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7188LowerChecked :
    lowerCheck 24 leaf7188Box leaf7188Inputs = true := by
  rfl'

private theorem leaf7188CoversExact : CoversExact 8
    leaf7188Box leaf7188Certificate leaf7188InnerLog leaf7188Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk153RoundedFacts chi363RoundedFacts
    innerPair814RoundedFacts leaf7188RoundedFacts (by rfl)

private theorem leaf7188FlatSound : Sound leaf7188Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7188CertificateValid
    leaf7188InnerLogValid leaf7188CoversExact leaf7188LowerChecked

private noncomputable def leaf7189Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (13/16), chiHi := (53/64) }

private noncomputable def leaf7189Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109089/67108864) }, vSqrt := { lower := (8191/8192), upper := (17178329085/17176612864) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (268128049/134217728) }, upper := { exponent := 2, mantissa := (1051/1024) } }, logOuter := sk154LogOuterCertificate, logK := sk154LogKCertificate, logChi := chi363LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34354941949/34353225728) } }, logDArg := sk154LogDArgCertificate }

private noncomputable def leaf7189InnerLog : WideLogData :=
  innerPair815Data

set_option maxRecDepth 1000000 in
private theorem leaf7189LocalValidity :
    LeafFacts leaf7189Box leaf7189Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7189Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178329085/17176612864) }) = true
      norm_num [leaf7189Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7189CertificateValid :
    WideCertificateValid leaf7189Box leaf7189Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk154ValidityFacts chi363ValidityFacts
    leaf7189LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7189CoverageChecked :
    coverageCheck (innerAD leaf7189Box) leaf7189InnerLog = true := by
  rfl'

private theorem leaf7189InnerLogValid :
    leaf7189InnerLog.Valid 8 (innerAD leaf7189Box) :=
  wideLogDataValid_of_cachedCheck endpoint505PositiveFacts
    endpoint583PositiveFacts.valid leaf7189CoverageChecked

private noncomputable def leaf7189InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629919/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7189InputLogOnePlusV_eq :
    leaf7189InputLogOnePlusV = outerEnclosure 24
      (leaf7189Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7189RoundedFacts : LeafRoundedFacts 8
    leaf7189Certificate.logOnePlusV leaf7189InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7189InputLogOnePlusV_eq }

private noncomputable def leaf7189Inputs : Inputs :=
  inputsOfCaches globalInput sk154RoundedInputs
    chi363InputQChi innerPair815Input
    leaf7189InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7189LowerChecked :
    lowerCheck 24 leaf7189Box leaf7189Inputs = true := by
  rfl'

private theorem leaf7189CoversExact : CoversExact 8
    leaf7189Box leaf7189Certificate leaf7189InnerLog leaf7189Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk154RoundedFacts chi363RoundedFacts
    innerPair815RoundedFacts leaf7189RoundedFacts (by rfl)

private theorem leaf7189FlatSound : Sound leaf7189Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7189CertificateValid
    leaf7189InnerLogValid leaf7189CoversExact leaf7189LowerChecked

private noncomputable def leaf7190Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (53/64), chiHi := (27/32) }

private noncomputable def leaf7190Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109089/67108864) }, vSqrt := { lower := (8191/8192), upper := (3435665817/3435321344) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (268521241/268435456) }, upper := { exponent := 2, mantissa := (2105/2048) } }, logOuter := sk153LogOuterCertificate, logK := sk153LogKCertificate, logChi := chi364LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (6870987161/6870642688) } }, logDArg := sk153LogDArgCertificate }

private noncomputable def leaf7190InnerLog : WideLogData :=
  innerPair817Data

set_option maxRecDepth 1000000 in
private theorem leaf7190LocalValidity :
    LeafFacts leaf7190Box leaf7190Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7190Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (3435665817/3435321344) }) = true
      norm_num [leaf7190Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7190CertificateValid :
    WideCertificateValid leaf7190Box leaf7190Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk153ValidityFacts chi364ValidityFacts
    leaf7190LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7190CoverageChecked :
    coverageCheck (innerAD leaf7190Box) leaf7190InnerLog = true := by
  rfl'

private theorem leaf7190InnerLogValid :
    leaf7190InnerLog.Valid 8 (innerAD leaf7190Box) :=
  wideLogDataValid_of_cachedCheck endpoint506PositiveFacts
    endpoint583PositiveFacts.valid leaf7190CoverageChecked

private noncomputable def leaf7190InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814961/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf7190InputLogOnePlusV_eq :
    leaf7190InputLogOnePlusV = outerEnclosure 24
      (leaf7190Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7190RoundedFacts : LeafRoundedFacts 8
    leaf7190Certificate.logOnePlusV leaf7190InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7190InputLogOnePlusV_eq }

private noncomputable def leaf7190Inputs : Inputs :=
  inputsOfCaches globalInput sk153RoundedInputs
    chi364InputQChi innerPair817Input
    leaf7190InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7190LowerChecked :
    lowerCheck 24 leaf7190Box leaf7190Inputs = true := by
  rfl'

private theorem leaf7190CoversExact : CoversExact 8
    leaf7190Box leaf7190Certificate leaf7190InnerLog leaf7190Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk153RoundedFacts chi364RoundedFacts
    innerPair817RoundedFacts leaf7190RoundedFacts (by rfl)

private theorem leaf7190FlatSound : Sound leaf7190Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7190CertificateValid
    leaf7190InnerLogValid leaf7190CoversExact leaf7190LowerChecked

private noncomputable def leaf7191Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (53/64), chiHi := (27/32) }

private noncomputable def leaf7191Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109091/67108864) }, vSqrt := { lower := (8191/8192), upper := (17178329085/17176551424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (271994435/268435456) }, upper := { exponent := 2, mantissa := (533/512) } }, logOuter := sk154LogOuterCertificate, logK := sk154LogKCertificate, logChi := chi364LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34354880509/34353102848) } }, logDArg := sk154LogDArgCertificate }

private noncomputable def leaf7191InnerLog : WideLogData :=
  innerPair818Data

set_option maxRecDepth 1000000 in
private theorem leaf7191LocalValidity :
    LeafFacts leaf7191Box leaf7191Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7191Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178329085/17176551424) }) = true
      norm_num [leaf7191Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7191CertificateValid :
    WideCertificateValid leaf7191Box leaf7191Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk154ValidityFacts chi364ValidityFacts
    leaf7191LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7191CoverageChecked :
    coverageCheck (innerAD leaf7191Box) leaf7191InnerLog = true := by
  rfl'

private theorem leaf7191InnerLogValid :
    leaf7191InnerLog.Valid 8 (innerAD leaf7191Box) :=
  wideLogDataValid_of_cachedCheck endpoint506PositiveFacts
    endpoint584PositiveFacts.valid leaf7191CoverageChecked

private noncomputable def leaf7191InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629949/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7191InputLogOnePlusV_eq :
    leaf7191InputLogOnePlusV = outerEnclosure 24
      (leaf7191Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7191RoundedFacts : LeafRoundedFacts 8
    leaf7191Certificate.logOnePlusV leaf7191InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7191InputLogOnePlusV_eq }

private noncomputable def leaf7191Inputs : Inputs :=
  inputsOfCaches globalInput sk154RoundedInputs
    chi364InputQChi innerPair818Input
    leaf7191InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7191LowerChecked :
    lowerCheck 24 leaf7191Box leaf7191Inputs = true := by
  rfl'

private theorem leaf7191CoversExact : CoversExact 8
    leaf7191Box leaf7191Certificate leaf7191InnerLog leaf7191Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk154RoundedFacts chi364RoundedFacts
    innerPair818RoundedFacts leaf7191RoundedFacts (by rfl)

private theorem leaf7191FlatSound : Sound leaf7191Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7191CertificateValid
    leaf7191InnerLogValid leaf7191CoversExact leaf7191LowerChecked

private noncomputable def leaf7192Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (27/32), chiHi := (55/64) }

private noncomputable def leaf7192Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109091/67108864) }, vSqrt := { lower := (8191/8192), upper := (17178329085/17176546304) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (272322095/268435456) }, upper := { exponent := 2, mantissa := (4269/4096) } }, logOuter := sk153LogOuterCertificate, logK := sk153LogKCertificate, logChi := chi365LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34354875389/34353092608) } }, logDArg := sk153LogDArgCertificate }

private noncomputable def leaf7192InnerLog : WideLogData :=
  innerPair818Data

set_option maxRecDepth 1000000 in
private theorem leaf7192LocalValidity :
    LeafFacts leaf7192Box leaf7192Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7192Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178329085/17176546304) }) = true
      norm_num [leaf7192Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7192CertificateValid :
    WideCertificateValid leaf7192Box leaf7192Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk153ValidityFacts chi365ValidityFacts
    leaf7192LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7192CoverageChecked :
    coverageCheck (innerAD leaf7192Box) leaf7192InnerLog = true := by
  rfl'

private theorem leaf7192InnerLogValid :
    leaf7192InnerLog.Valid 8 (innerAD leaf7192Box) :=
  wideLogDataValid_of_cachedCheck endpoint506PositiveFacts
    endpoint584PositiveFacts.valid leaf7192CoverageChecked

private noncomputable def leaf7192InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629951/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7192InputLogOnePlusV_eq :
    leaf7192InputLogOnePlusV = outerEnclosure 24
      (leaf7192Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7192RoundedFacts : LeafRoundedFacts 8
    leaf7192Certificate.logOnePlusV leaf7192InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7192InputLogOnePlusV_eq }

private noncomputable def leaf7192Inputs : Inputs :=
  inputsOfCaches globalInput sk153RoundedInputs
    chi365InputQChi innerPair818Input
    leaf7192InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7192LowerChecked :
    lowerCheck 24 leaf7192Box leaf7192Inputs = true := by
  rfl'

private theorem leaf7192CoversExact : CoversExact 8
    leaf7192Box leaf7192Certificate leaf7192InnerLog leaf7192Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk153RoundedFacts chi365RoundedFacts
    innerPair818RoundedFacts leaf7192RoundedFacts (by rfl)

private theorem leaf7192FlatSound : Sound leaf7192Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7192CertificateValid
    leaf7192InnerLogValid leaf7192CoversExact leaf7192LowerChecked

private noncomputable def leaf7193Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (27/32), chiHi := (55/64) }

private noncomputable def leaf7193Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109093/67108864) }, vSqrt := { lower := (8191/8192), upper := (17178329085/17176489984) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (275860821/268435456) }, upper := { exponent := 2, mantissa := (1081/1024) } }, logOuter := sk154LogOuterCertificate, logK := sk154LogKCertificate, logChi := chi365LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34354819069/34352979968) } }, logDArg := sk154LogDArgCertificate }

private noncomputable def leaf7193InnerLog : WideLogData :=
  innerPair869Data

set_option maxRecDepth 1000000 in
private theorem leaf7193LocalValidity :
    LeafFacts leaf7193Box leaf7193Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7193Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178329085/17176489984) }) = true
      norm_num [leaf7193Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7193CertificateValid :
    WideCertificateValid leaf7193Box leaf7193Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk154ValidityFacts chi365ValidityFacts
    leaf7193LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7193CoverageChecked :
    coverageCheck (innerAD leaf7193Box) leaf7193InnerLog = true := by
  rfl'

private theorem leaf7193InnerLogValid :
    leaf7193InnerLog.Valid 8 (innerAD leaf7193Box) :=
  wideLogDataValid_of_cachedCheck endpoint582PositiveFacts
    endpoint585PositiveFacts.valid leaf7193CoverageChecked

private noncomputable def leaf7193InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629979/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7193InputLogOnePlusV_eq :
    leaf7193InputLogOnePlusV = outerEnclosure 24
      (leaf7193Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7193RoundedFacts : LeafRoundedFacts 8
    leaf7193Certificate.logOnePlusV leaf7193InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7193InputLogOnePlusV_eq }

private noncomputable def leaf7193Inputs : Inputs :=
  inputsOfCaches globalInput sk154RoundedInputs
    chi365InputQChi innerPair869Input
    leaf7193InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7193LowerChecked :
    lowerCheck 24 leaf7193Box leaf7193Inputs = true := by
  rfl'

private theorem leaf7193CoversExact : CoversExact 8
    leaf7193Box leaf7193Certificate leaf7193InnerLog leaf7193Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk154RoundedFacts chi365RoundedFacts
    innerPair869RoundedFacts leaf7193RoundedFacts (by rfl)

private theorem leaf7193FlatSound : Sound leaf7193Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7193CertificateValid
    leaf7193InnerLogValid leaf7193CoversExact leaf7193LowerChecked

private noncomputable def leaf7194Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (55/64), chiHi := (7/8) }

private noncomputable def leaf7194Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109093/67108864) }, vSqrt := { lower := (8191/8192), upper := (5726109695/5725495296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (276122949/268435456) }, upper := { exponent := 2, mantissa := (541/512) } }, logOuter := sk153LogOuterCertificate, logK := sk153LogKCertificate, logChi := chi366LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (11451604991/11450990592) } }, logDArg := sk153LogDArgCertificate }

private noncomputable def leaf7194InnerLog : WideLogData :=
  innerPair869Data

set_option maxRecDepth 1000000 in
private theorem leaf7194LocalValidity :
    LeafFacts leaf7194Box leaf7194Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7194Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5726109695/5725495296) }) = true
      norm_num [leaf7194Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7194CertificateValid :
    WideCertificateValid leaf7194Box leaf7194Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk153ValidityFacts chi366ValidityFacts
    leaf7194LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7194CoverageChecked :
    coverageCheck (innerAD leaf7194Box) leaf7194InnerLog = true := by
  rfl'

private theorem leaf7194InnerLogValid :
    leaf7194InnerLog.Valid 8 (innerAD leaf7194Box) :=
  wideLogDataValid_of_cachedCheck endpoint582PositiveFacts
    endpoint585PositiveFacts.valid leaf7194CoverageChecked

private noncomputable def leaf7194InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629981/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7194InputLogOnePlusV_eq :
    leaf7194InputLogOnePlusV = outerEnclosure 24
      (leaf7194Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7194RoundedFacts : LeafRoundedFacts 8
    leaf7194Certificate.logOnePlusV leaf7194InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7194InputLogOnePlusV_eq }

private noncomputable def leaf7194Inputs : Inputs :=
  inputsOfCaches globalInput sk153RoundedInputs
    chi366InputQChi innerPair869Input
    leaf7194InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7194LowerChecked :
    lowerCheck 24 leaf7194Box leaf7194Inputs = true := by
  rfl'

private theorem leaf7194CoversExact : CoversExact 8
    leaf7194Box leaf7194Certificate leaf7194InnerLog leaf7194Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk153RoundedFacts chi366RoundedFacts
    innerPair869RoundedFacts leaf7194RoundedFacts (by rfl)

private theorem leaf7194FlatSound : Sound leaf7194Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7194CertificateValid
    leaf7194InnerLogValid leaf7194CoversExact leaf7194LowerChecked

private noncomputable def leaf7195Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (55/64), chiHi := (7/8) }

private noncomputable def leaf7195Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109095/67108864) }, vSqrt := { lower := (8191/8192), upper := (17178329085/17176428544) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (279727207/268435456) }, upper := { exponent := 2, mantissa := (137/128) } }, logOuter := sk154LogOuterCertificate, logK := sk154LogKCertificate, logChi := chi366LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34354757629/34352857088) } }, logDArg := sk154LogDArgCertificate }

private noncomputable def leaf7195InnerLog : WideLogData :=
  innerPair872Data

set_option maxRecDepth 1000000 in
private theorem leaf7195LocalValidity :
    LeafFacts leaf7195Box leaf7195Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7195Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178329085/17176428544) }) = true
      norm_num [leaf7195Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7195CertificateValid :
    WideCertificateValid leaf7195Box leaf7195Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk154ValidityFacts chi366ValidityFacts
    leaf7195LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7195CoverageChecked :
    coverageCheck (innerAD leaf7195Box) leaf7195InnerLog = true := by
  rfl'

private theorem leaf7195InnerLogValid :
    leaf7195InnerLog.Valid 8 (innerAD leaf7195Box) :=
  wideLogDataValid_of_cachedCheck endpoint583PositiveFacts
    endpoint589PositiveFacts.valid leaf7195CoverageChecked

private noncomputable def leaf7195InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11630009/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7195InputLogOnePlusV_eq :
    leaf7195InputLogOnePlusV = outerEnclosure 24
      (leaf7195Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7195RoundedFacts : LeafRoundedFacts 8
    leaf7195Certificate.logOnePlusV leaf7195InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7195InputLogOnePlusV_eq }

private noncomputable def leaf7195Inputs : Inputs :=
  inputsOfCaches globalInput sk154RoundedInputs
    chi366InputQChi innerPair872Input
    leaf7195InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7195LowerChecked :
    lowerCheck 24 leaf7195Box leaf7195Inputs = true := by
  rfl'

private theorem leaf7195CoversExact : CoversExact 8
    leaf7195Box leaf7195Certificate leaf7195InnerLog leaf7195Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk154RoundedFacts chi366RoundedFacts
    innerPair872RoundedFacts leaf7195RoundedFacts (by rfl)

private theorem leaf7195FlatSound : Sound leaf7195Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7195CertificateValid
    leaf7195InnerLogValid leaf7195CoversExact leaf7195LowerChecked

private noncomputable def leaf7196Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (3/4), chiHi := (49/64) }

private noncomputable def leaf7196Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109083/67108864) }, vSqrt := { lower := (8191/8192), upper := (11452394153/11451205632) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (255808039/134217728) }, upper := { exponent := 1, mantissa := (4013/2048) } }, logOuter := sk157LogOuterCertificate, logK := sk157LogKCertificate, logChi := chi345LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (22903599785/22902411264) } }, logDArg := sk157LogDArgCertificate }

private noncomputable def leaf7196InnerLog : WideLogData :=
  innerPair806Data

set_option maxRecDepth 1000000 in
private theorem leaf7196LocalValidity :
    LeafFacts leaf7196Box leaf7196Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7196Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (11452394153/11451205632) }) = true
      norm_num [leaf7196Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7196CertificateValid :
    WideCertificateValid leaf7196Box leaf7196Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk157ValidityFacts chi345ValidityFacts
    leaf7196LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7196CoverageChecked :
    coverageCheck (innerAD leaf7196Box) leaf7196InnerLog = true := by
  rfl'

private theorem leaf7196InnerLogValid :
    leaf7196InnerLog.Valid 8 (innerAD leaf7196Box) :=
  wideLogDataValid_of_cachedCheck endpoint502PositiveFacts
    endpoint505PositiveFacts.valid leaf7196CoverageChecked

private noncomputable def leaf7196InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629951/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7196InputLogOnePlusV_eq :
    leaf7196InputLogOnePlusV = outerEnclosure 24
      (leaf7196Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7196RoundedFacts : LeafRoundedFacts 8
    leaf7196Certificate.logOnePlusV leaf7196InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7196InputLogOnePlusV_eq }

private noncomputable def leaf7196Inputs : Inputs :=
  inputsOfCaches globalInput sk157RoundedInputs
    chi345InputQChi innerPair806Input
    leaf7196InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7196LowerChecked :
    lowerCheck 24 leaf7196Box leaf7196Inputs = true := by
  rfl'

private theorem leaf7196CoversExact : CoversExact 8
    leaf7196Box leaf7196Certificate leaf7196InnerLog leaf7196Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk157RoundedFacts chi345RoundedFacts
    innerPair806RoundedFacts leaf7196RoundedFacts (by rfl)

private theorem leaf7196FlatSound : Sound leaf7196Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7196CertificateValid
    leaf7196InnerLogValid leaf7196CoversExact leaf7196LowerChecked

private noncomputable def leaf7197Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (3/4), chiHi := (49/64) }

private noncomputable def leaf7197Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109085/67108864) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34353516544) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (258953573/134217728) }, upper := { exponent := 1, mantissa := (2031/1024) } }, logOuter := sk158LogOuterCertificate, logK := sk158LogKCertificate, logChi := chi345LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68710699003/68707033088) } }, logDArg := sk158LogDArgCertificate }

private noncomputable def leaf7197InnerLog : WideLogData :=
  innerPair809Data

set_option maxRecDepth 1000000 in
private theorem leaf7197LocalValidity :
    LeafFacts leaf7197Box leaf7197Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7197Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34353516544) }) = true
      norm_num [leaf7197Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7197CertificateValid :
    WideCertificateValid leaf7197Box leaf7197Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk158ValidityFacts chi345ValidityFacts
    leaf7197LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7197CoverageChecked :
    coverageCheck (innerAD leaf7197Box) leaf7197InnerLog = true := by
  rfl'

private theorem leaf7197InnerLogValid :
    leaf7197InnerLog.Valid 8 (innerAD leaf7197Box) :=
  wideLogDataValid_of_cachedCheck endpoint503PositiveFacts
    endpoint506PositiveFacts.valid leaf7197CoverageChecked

private noncomputable def leaf7197InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453747/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf7197InputLogOnePlusV_eq :
    leaf7197InputLogOnePlusV = outerEnclosure 24
      (leaf7197Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7197RoundedFacts : LeafRoundedFacts 8
    leaf7197Certificate.logOnePlusV leaf7197InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7197InputLogOnePlusV_eq }

private noncomputable def leaf7197Inputs : Inputs :=
  inputsOfCaches globalInput sk158RoundedInputs
    chi345InputQChi innerPair809Input
    leaf7197InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7197LowerChecked :
    lowerCheck 24 leaf7197Box leaf7197Inputs = true := by
  rfl'

private theorem leaf7197CoversExact : CoversExact 8
    leaf7197Box leaf7197Certificate leaf7197InnerLog leaf7197Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk158RoundedFacts chi345RoundedFacts
    innerPair809RoundedFacts leaf7197RoundedFacts (by rfl)

private theorem leaf7197FlatSound : Sound leaf7197Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7197CertificateValid
    leaf7197InnerLogValid leaf7197CoversExact leaf7197LowerChecked

private noncomputable def leaf7198Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (49/64), chiHi := (25/32) }

private noncomputable def leaf7198Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109085/67108864) }, vSqrt := { lower := (8191/8192), upper := (17178329085/17176745984) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (259739957/134217728) }, upper := { exponent := 1, mantissa := (2037/1024) } }, logOuter := sk157LogOuterCertificate, logK := sk157LogKCertificate, logChi := chi346LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34355075069/34353491968) } }, logDArg := sk157LogDArgCertificate }

private noncomputable def leaf7198InnerLog : WideLogData :=
  innerPair809Data

set_option maxRecDepth 1000000 in
private theorem leaf7198LocalValidity :
    LeafFacts leaf7198Box leaf7198Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7198Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178329085/17176745984) }) = true
      norm_num [leaf7198Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7198CertificateValid :
    WideCertificateValid leaf7198Box leaf7198Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk157ValidityFacts chi346ValidityFacts
    leaf7198LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7198CoverageChecked :
    coverageCheck (innerAD leaf7198Box) leaf7198InnerLog = true := by
  rfl'

private theorem leaf7198InnerLogValid :
    leaf7198InnerLog.Valid 8 (innerAD leaf7198Box) :=
  wideLogDataValid_of_cachedCheck endpoint503PositiveFacts
    endpoint506PositiveFacts.valid leaf7198CoverageChecked

private noncomputable def leaf7198InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814927/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf7198InputLogOnePlusV_eq :
    leaf7198InputLogOnePlusV = outerEnclosure 24
      (leaf7198Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7198RoundedFacts : LeafRoundedFacts 8
    leaf7198Certificate.logOnePlusV leaf7198InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7198InputLogOnePlusV_eq }

private noncomputable def leaf7198Inputs : Inputs :=
  inputsOfCaches globalInput sk157RoundedInputs
    chi346InputQChi innerPair809Input
    leaf7198InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7198LowerChecked :
    lowerCheck 24 leaf7198Box leaf7198Inputs = true := by
  rfl'

private theorem leaf7198CoversExact : CoversExact 8
    leaf7198Box leaf7198Certificate leaf7198InnerLog leaf7198Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk157RoundedFacts chi346RoundedFacts
    innerPair809RoundedFacts leaf7198RoundedFacts (by rfl)

private theorem leaf7198FlatSound : Sound leaf7198Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7198CertificateValid
    leaf7198InnerLogValid leaf7198CoversExact leaf7198LowerChecked

private noncomputable def leaf7199Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (49/64), chiHi := (25/32) }

private noncomputable def leaf7199Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109087/67108864) }, vSqrt := { lower := (8191/8192), upper := (5726109695/5725564928) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (262951023/134217728) }, upper := { exponent := 2, mantissa := (1031/1024) } }, logOuter := sk158LogOuterCertificate, logK := sk158LogKCertificate, logChi := chi346LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (11451674623/11451129856) } }, logDArg := sk158LogDArgCertificate }

private noncomputable def leaf7199InnerLog : WideLogData :=
  innerPair812Data

set_option maxRecDepth 1000000 in
private theorem leaf7199LocalValidity :
    LeafFacts leaf7199Box leaf7199Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7199Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5726109695/5725564928) }) = true
      norm_num [leaf7199Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7199CertificateValid :
    WideCertificateValid leaf7199Box leaf7199Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk158ValidityFacts chi346ValidityFacts
    leaf7199LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7199CoverageChecked :
    coverageCheck (innerAD leaf7199Box) leaf7199InnerLog = true := by
  rfl'

private theorem leaf7199InnerLogValid :
    leaf7199InnerLog.Valid 8 (innerAD leaf7199Box) :=
  wideLogDataValid_of_cachedCheck endpoint504PositiveFacts
    endpoint582PositiveFacts.valid leaf7199CoverageChecked

private noncomputable def leaf7199InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629879/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7199InputLogOnePlusV_eq :
    leaf7199InputLogOnePlusV = outerEnclosure 24
      (leaf7199Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7199RoundedFacts : LeafRoundedFacts 8
    leaf7199Certificate.logOnePlusV leaf7199InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7199InputLogOnePlusV_eq }

private noncomputable def leaf7199Inputs : Inputs :=
  inputsOfCaches globalInput sk158RoundedInputs
    chi346InputQChi innerPair812Input
    leaf7199InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7199LowerChecked :
    lowerCheck 24 leaf7199Box leaf7199Inputs = true := by
  rfl'

private theorem leaf7199CoversExact : CoversExact 8
    leaf7199Box leaf7199Certificate leaf7199InnerLog leaf7199Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk158RoundedFacts chi346RoundedFacts
    innerPair812RoundedFacts leaf7199RoundedFacts (by rfl)

private theorem leaf7199FlatSound : Sound leaf7199Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7199CertificateValid
    leaf7199InnerLogValid leaf7199CoversExact leaf7199LowerChecked

private noncomputable def leaf7200Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (25/32), chiHi := (51/64) }

private noncomputable def leaf7200Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109087/67108864) }, vSqrt := { lower := (8191/8192), upper := (3435665817/3435336704) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (263671875/134217728) }, upper := { exponent := 2, mantissa := (4135/4096) } }, logOuter := sk157LogOuterCertificate, logK := sk157LogKCertificate, logChi := chi361LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (6871002521/6870673408) } }, logDArg := sk157LogDArgCertificate }

private noncomputable def leaf7200InnerLog : WideLogData :=
  innerPair812Data

set_option maxRecDepth 1000000 in
private theorem leaf7200LocalValidity :
    LeafFacts leaf7200Box leaf7200Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7200Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (3435665817/3435336704) }) = true
      norm_num [leaf7200Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7200CertificateValid :
    WideCertificateValid leaf7200Box leaf7200Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk157ValidityFacts chi361ValidityFacts
    leaf7200LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7200CoverageChecked :
    coverageCheck (innerAD leaf7200Box) leaf7200InnerLog = true := by
  rfl'

private theorem leaf7200InnerLogValid :
    leaf7200InnerLog.Valid 8 (innerAD leaf7200Box) :=
  wideLogDataValid_of_cachedCheck endpoint504PositiveFacts
    endpoint582PositiveFacts.valid leaf7200CoverageChecked

private noncomputable def leaf7200InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907471/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf7200InputLogOnePlusV_eq :
    leaf7200InputLogOnePlusV = outerEnclosure 24
      (leaf7200Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7200RoundedFacts : LeafRoundedFacts 8
    leaf7200Certificate.logOnePlusV leaf7200InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7200InputLogOnePlusV_eq }

private noncomputable def leaf7200Inputs : Inputs :=
  inputsOfCaches globalInput sk157RoundedInputs
    chi361InputQChi innerPair812Input
    leaf7200InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7200LowerChecked :
    lowerCheck 24 leaf7200Box leaf7200Inputs = true := by
  rfl'

private theorem leaf7200CoversExact : CoversExact 8
    leaf7200Box leaf7200Certificate leaf7200InnerLog leaf7200Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk157RoundedFacts chi361RoundedFacts
    innerPair812RoundedFacts leaf7200RoundedFacts (by rfl)

private theorem leaf7200FlatSound : Sound leaf7200Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7200CertificateValid
    leaf7200InnerLogValid leaf7200CoversExact leaf7200LowerChecked

private noncomputable def leaf7201Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (25/32), chiHi := (51/64) }

private noncomputable def leaf7201Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109089/67108864) }, vSqrt := { lower := (8191/8192), upper := (17178329085/17176631296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (266948473/134217728) }, upper := { exponent := 2, mantissa := (2093/2048) } }, logOuter := sk158LogOuterCertificate, logK := sk158LogKCertificate, logChi := chi361LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34354960381/34353262592) } }, logDArg := sk158LogDArgCertificate }

private noncomputable def leaf7201InnerLog : WideLogData :=
  innerPair815Data

set_option maxRecDepth 1000000 in
private theorem leaf7201LocalValidity :
    LeafFacts leaf7201Box leaf7201Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7201Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178329085/17176631296) }) = true
      norm_num [leaf7201Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7201CertificateValid :
    WideCertificateValid leaf7201Box leaf7201Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk158ValidityFacts chi361ValidityFacts
    leaf7201LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7201CoverageChecked :
    coverageCheck (innerAD leaf7201Box) leaf7201InnerLog = true := by
  rfl'

private theorem leaf7201InnerLogValid :
    leaf7201InnerLog.Valid 8 (innerAD leaf7201Box) :=
  wideLogDataValid_of_cachedCheck endpoint505PositiveFacts
    endpoint583PositiveFacts.valid leaf7201CoverageChecked

private noncomputable def leaf7201InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814955/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf7201InputLogOnePlusV_eq :
    leaf7201InputLogOnePlusV = outerEnclosure 24
      (leaf7201Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7201RoundedFacts : LeafRoundedFacts 8
    leaf7201Certificate.logOnePlusV leaf7201InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7201InputLogOnePlusV_eq }

private noncomputable def leaf7201Inputs : Inputs :=
  inputsOfCaches globalInput sk158RoundedInputs
    chi361InputQChi innerPair815Input
    leaf7201InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7201LowerChecked :
    lowerCheck 24 leaf7201Box leaf7201Inputs = true := by
  rfl'

private theorem leaf7201CoversExact : CoversExact 8
    leaf7201Box leaf7201Certificate leaf7201InnerLog leaf7201Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk158RoundedFacts chi361RoundedFacts
    innerPair815RoundedFacts leaf7201RoundedFacts (by rfl)

private theorem leaf7201FlatSound : Sound leaf7201Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7201CertificateValid
    leaf7201InnerLogValid leaf7201CoversExact leaf7201LowerChecked

private noncomputable def leaf7202Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (51/64), chiHi := (13/16) }

private noncomputable def leaf7202Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109089/67108864) }, vSqrt := { lower := (8191/8192), upper := (5726109695/5725540352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (267603793/134217728) }, upper := { exponent := 2, mantissa := (1049/1024) } }, logOuter := sk157LogOuterCertificate, logK := sk157LogKCertificate, logChi := chi362LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (11451650047/11451080704) } }, logDArg := sk157LogDArgCertificate }

private noncomputable def leaf7202InnerLog : WideLogData :=
  innerPair815Data

set_option maxRecDepth 1000000 in
private theorem leaf7202LocalValidity :
    LeafFacts leaf7202Box leaf7202Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7202Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5726109695/5725540352) }) = true
      norm_num [leaf7202Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7202CertificateValid :
    WideCertificateValid leaf7202Box leaf7202Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk157ValidityFacts chi362ValidityFacts
    leaf7202LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7202CoverageChecked :
    coverageCheck (innerAD leaf7202Box) leaf7202InnerLog = true := by
  rfl'

private theorem leaf7202InnerLogValid :
    leaf7202InnerLog.Valid 8 (innerAD leaf7202Box) :=
  wideLogDataValid_of_cachedCheck endpoint505PositiveFacts
    endpoint583PositiveFacts.valid leaf7202CoverageChecked

private noncomputable def leaf7202InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629915/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7202InputLogOnePlusV_eq :
    leaf7202InputLogOnePlusV = outerEnclosure 24
      (leaf7202Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7202RoundedFacts : LeafRoundedFacts 8
    leaf7202Certificate.logOnePlusV leaf7202InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7202InputLogOnePlusV_eq }

private noncomputable def leaf7202Inputs : Inputs :=
  inputsOfCaches globalInput sk157RoundedInputs
    chi362InputQChi innerPair815Input
    leaf7202InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7202LowerChecked :
    lowerCheck 24 leaf7202Box leaf7202Inputs = true := by
  rfl'

private theorem leaf7202CoversExact : CoversExact 8
    leaf7202Box leaf7202Certificate leaf7202InnerLog leaf7202Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk157RoundedFacts chi362RoundedFacts
    innerPair815RoundedFacts leaf7202RoundedFacts (by rfl)

private theorem leaf7202FlatSound : Sound leaf7202Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7202CertificateValid
    leaf7202InnerLogValid leaf7202CoversExact leaf7202LowerChecked

private noncomputable def leaf7203Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (51/64), chiHi := (13/16) }

private noncomputable def leaf7203Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109091/67108864) }, vSqrt := { lower := (8191/8192), upper := (17178329085/17176567808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (270945923/268435456) }, upper := { exponent := 2, mantissa := (531/512) } }, logOuter := sk158LogOuterCertificate, logK := sk158LogKCertificate, logChi := chi362LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34354896893/34353135616) } }, logDArg := sk158LogDArgCertificate }

private noncomputable def leaf7203InnerLog : WideLogData :=
  innerPair818Data

set_option maxRecDepth 1000000 in
private theorem leaf7203LocalValidity :
    LeafFacts leaf7203Box leaf7203Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7203Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178329085/17176567808) }) = true
      norm_num [leaf7203Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7203CertificateValid :
    WideCertificateValid leaf7203Box leaf7203Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk158ValidityFacts chi362ValidityFacts
    leaf7203LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7203CoverageChecked :
    coverageCheck (innerAD leaf7203Box) leaf7203InnerLog = true := by
  rfl'

private theorem leaf7203InnerLogValid :
    leaf7203InnerLog.Valid 8 (innerAD leaf7203Box) :=
  wideLogDataValid_of_cachedCheck endpoint506PositiveFacts
    endpoint584PositiveFacts.valid leaf7203CoverageChecked

private noncomputable def leaf7203InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629941/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7203InputLogOnePlusV_eq :
    leaf7203InputLogOnePlusV = outerEnclosure 24
      (leaf7203Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7203RoundedFacts : LeafRoundedFacts 8
    leaf7203Certificate.logOnePlusV leaf7203InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7203InputLogOnePlusV_eq }

private noncomputable def leaf7203Inputs : Inputs :=
  inputsOfCaches globalInput sk158RoundedInputs
    chi362InputQChi innerPair818Input
    leaf7203InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7203LowerChecked :
    lowerCheck 24 leaf7203Box leaf7203Inputs = true := by
  rfl'

private theorem leaf7203CoversExact : CoversExact 8
    leaf7203Box leaf7203Certificate leaf7203InnerLog leaf7203Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk158RoundedFacts chi362RoundedFacts
    innerPair818RoundedFacts leaf7203RoundedFacts (by rfl)

private theorem leaf7203FlatSound : Sound leaf7203Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7203CertificateValid
    leaf7203InnerLogValid leaf7203CoversExact leaf7203LowerChecked

private noncomputable def leaf7204Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (3/4), chiHi := (49/64) }

private noncomputable def leaf7204Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109087/67108864) }, vSqrt := { lower := (8191/8192), upper := (17178329085/17176708096) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (262099107/134217728) }, upper := { exponent := 2, mantissa := (4111/4096) } }, logOuter := sk159LogOuterCertificate, logK := sk159LogKCertificate, logChi := chi345LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34355037181/34353416192) } }, logDArg := sk159LogDArgCertificate }

private noncomputable def leaf7204InnerLog : WideLogData :=
  innerPair889Data

set_option maxRecDepth 1000000 in
private theorem leaf7204LocalValidity :
    LeafFacts leaf7204Box leaf7204Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7204Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178329085/17176708096) }) = true
      norm_num [leaf7204Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7204CertificateValid :
    WideCertificateValid leaf7204Box leaf7204Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk159ValidityFacts chi345ValidityFacts
    leaf7204LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7204CoverageChecked :
    coverageCheck (innerAD leaf7204Box) leaf7204InnerLog = true := by
  rfl'

private theorem leaf7204InnerLogValid :
    leaf7204InnerLog.Valid 8 (innerAD leaf7204Box) :=
  wideLogDataValid_of_cachedCheck endpoint593PositiveFacts
    endpoint587PositiveFacts.valid leaf7204CoverageChecked

private noncomputable def leaf7204InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726867/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf7204InputLogOnePlusV_eq :
    leaf7204InputLogOnePlusV = outerEnclosure 24
      (leaf7204Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7204RoundedFacts : LeafRoundedFacts 8
    leaf7204Certificate.logOnePlusV leaf7204InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7204InputLogOnePlusV_eq }

private noncomputable def leaf7204Inputs : Inputs :=
  inputsOfCaches globalInput sk159RoundedInputs
    chi345InputQChi innerPair889Input
    leaf7204InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7204LowerChecked :
    lowerCheck 24 leaf7204Box leaf7204Inputs = true := by
  rfl'

private theorem leaf7204CoversExact : CoversExact 8
    leaf7204Box leaf7204Certificate leaf7204InnerLog leaf7204Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk159RoundedFacts chi345RoundedFacts
    innerPair889RoundedFacts leaf7204RoundedFacts (by rfl)

private theorem leaf7204FlatSound : Sound leaf7204Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7204CertificateValid
    leaf7204InnerLogValid leaf7204CoversExact leaf7204LowerChecked

private noncomputable def leaf7205Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (3/4), chiHi := (49/64) }

private noncomputable def leaf7205Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109089/67108864) }, vSqrt := { lower := (65527/65536), upper := (1145221939/1145110528) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (265244641/134217728) }, upper := { exponent := 2, mantissa := (65/64) } }, logOuter := sk160LogOuterCertificate, logK := sk160LogKCertificate, logChi := chi345LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (2290332467/2290221056) } }, logDArg := sk160LogDArgCertificate }

private noncomputable def leaf7205InnerLog : WideLogData :=
  innerPair814Data

set_option maxRecDepth 1000000 in
private theorem leaf7205LocalValidity :
    LeafFacts leaf7205Box leaf7205Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7205Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (1145221939/1145110528) }) = true
      norm_num [leaf7205Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7205CertificateValid :
    WideCertificateValid leaf7205Box leaf7205Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk160ValidityFacts chi345ValidityFacts
    leaf7205LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7205CoverageChecked :
    coverageCheck (innerAD leaf7205Box) leaf7205InnerLog = true := by
  rfl'

private theorem leaf7205InnerLogValid :
    leaf7205InnerLog.Valid 8 (innerAD leaf7205Box) :=
  wideLogDataValid_of_cachedCheck endpoint505PositiveFacts
    endpoint582PositiveFacts.valid leaf7205CoverageChecked

private noncomputable def leaf7205InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629897/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7205InputLogOnePlusV_eq :
    leaf7205InputLogOnePlusV = outerEnclosure 24
      (leaf7205Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7205RoundedFacts : LeafRoundedFacts 8
    leaf7205Certificate.logOnePlusV leaf7205InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7205InputLogOnePlusV_eq }

private noncomputable def leaf7205Inputs : Inputs :=
  inputsOfCaches globalInput sk160RoundedInputs
    chi345InputQChi innerPair814Input
    leaf7205InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7205LowerChecked :
    lowerCheck 24 leaf7205Box leaf7205Inputs = true := by
  rfl'

private theorem leaf7205CoversExact : CoversExact 8
    leaf7205Box leaf7205Certificate leaf7205InnerLog leaf7205Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk160RoundedFacts chi345RoundedFacts
    innerPair814RoundedFacts leaf7205RoundedFacts (by rfl)

private theorem leaf7205FlatSound : Sound leaf7205Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7205CertificateValid
    leaf7205InnerLogValid leaf7205CoversExact leaf7205LowerChecked

private noncomputable def leaf7206Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (49/64), chiHi := (25/32) }

private noncomputable def leaf7206Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109089/67108864) }, vSqrt := { lower := (8191/8192), upper := (17178329085/17176643584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (266162089/134217728) }, upper := { exponent := 2, mantissa := (2087/2048) } }, logOuter := sk159LogOuterCertificate, logK := sk159LogKCertificate, logChi := chi346LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34354972669/34353287168) } }, logDArg := sk159LogDArgCertificate }

private noncomputable def leaf7206InnerLog : WideLogData :=
  innerPair815Data

set_option maxRecDepth 1000000 in
private theorem leaf7206LocalValidity :
    LeafFacts leaf7206Box leaf7206Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7206Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178329085/17176643584) }) = true
      norm_num [leaf7206Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7206CertificateValid :
    WideCertificateValid leaf7206Box leaf7206Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk159ValidityFacts chi346ValidityFacts
    leaf7206LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7206CoverageChecked :
    coverageCheck (innerAD leaf7206Box) leaf7206InnerLog = true := by
  rfl'

private theorem leaf7206InnerLogValid :
    leaf7206InnerLog.Valid 8 (innerAD leaf7206Box) :=
  wideLogDataValid_of_cachedCheck endpoint505PositiveFacts
    endpoint583PositiveFacts.valid leaf7206CoverageChecked

private noncomputable def leaf7206InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726869/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf7206InputLogOnePlusV_eq :
    leaf7206InputLogOnePlusV = outerEnclosure 24
      (leaf7206Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7206RoundedFacts : LeafRoundedFacts 8
    leaf7206Certificate.logOnePlusV leaf7206InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7206InputLogOnePlusV_eq }

private noncomputable def leaf7206Inputs : Inputs :=
  inputsOfCaches globalInput sk159RoundedInputs
    chi346InputQChi innerPair815Input
    leaf7206InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7206LowerChecked :
    lowerCheck 24 leaf7206Box leaf7206Inputs = true := by
  rfl'

private theorem leaf7206CoversExact : CoversExact 8
    leaf7206Box leaf7206Certificate leaf7206InnerLog leaf7206Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk159RoundedFacts chi346RoundedFacts
    innerPair815RoundedFacts leaf7206RoundedFacts (by rfl)

private theorem leaf7206FlatSound : Sound leaf7206Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7206CertificateValid
    leaf7206InnerLogValid leaf7206CoversExact leaf7206LowerChecked

private noncomputable def leaf7207Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (49/64), chiHi := (25/32) }

private noncomputable def leaf7207Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109091/67108864) }, vSqrt := { lower := (65527/65536), upper := (17178329085/17176592384) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (269373155/268435456) }, upper := { exponent := 2, mantissa := (33/32) } }, logOuter := sk160LogOuterCertificate, logK := sk160LogKCertificate, logChi := chi346LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (34354921469/34353184768) } }, logDArg := sk160LogDArgCertificate }

private noncomputable def leaf7207InnerLog : WideLogData :=
  innerPair817Data

set_option maxRecDepth 1000000 in
private theorem leaf7207LocalValidity :
    LeafFacts leaf7207Box leaf7207Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7207Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (17178329085/17176592384) }) = true
      norm_num [leaf7207Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7207CertificateValid :
    WideCertificateValid leaf7207Box leaf7207Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk160ValidityFacts chi346ValidityFacts
    leaf7207LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7207CoverageChecked :
    coverageCheck (innerAD leaf7207Box) leaf7207InnerLog = true := by
  rfl'

private theorem leaf7207InnerLogValid :
    leaf7207InnerLog.Valid 8 (innerAD leaf7207Box) :=
  wideLogDataValid_of_cachedCheck endpoint506PositiveFacts
    endpoint583PositiveFacts.valid leaf7207CoverageChecked

private noncomputable def leaf7207InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629929/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7207InputLogOnePlusV_eq :
    leaf7207InputLogOnePlusV = outerEnclosure 24
      (leaf7207Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7207RoundedFacts : LeafRoundedFacts 8
    leaf7207Certificate.logOnePlusV leaf7207InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7207InputLogOnePlusV_eq }

private noncomputable def leaf7207Inputs : Inputs :=
  inputsOfCaches globalInput sk160RoundedInputs
    chi346InputQChi innerPair817Input
    leaf7207InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7207LowerChecked :
    lowerCheck 24 leaf7207Box leaf7207Inputs = true := by
  rfl'

private theorem leaf7207CoversExact : CoversExact 8
    leaf7207Box leaf7207Certificate leaf7207InnerLog leaf7207Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk160RoundedFacts chi346RoundedFacts
    innerPair817RoundedFacts leaf7207RoundedFacts (by rfl)

private theorem leaf7207FlatSound : Sound leaf7207Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7207CertificateValid
    leaf7207InnerLogValid leaf7207CoversExact leaf7207LowerChecked

private noncomputable def leaf7208Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (25/32), chiHi := (51/64) }

private noncomputable def leaf7208Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109091/67108864) }, vSqrt := { lower := (8191/8192), upper := (17178329085/17176579072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (270225071/268435456) }, upper := { exponent := 2, mantissa := (4237/4096) } }, logOuter := sk159LogOuterCertificate, logK := sk159LogKCertificate, logChi := chi361LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34354908157/34353158144) } }, logDArg := sk159LogDArgCertificate }

private noncomputable def leaf7208InnerLog : WideLogData :=
  innerPair818Data

set_option maxRecDepth 1000000 in
private theorem leaf7208LocalValidity :
    LeafFacts leaf7208Box leaf7208Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7208Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178329085/17176579072) }) = true
      norm_num [leaf7208Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7208CertificateValid :
    WideCertificateValid leaf7208Box leaf7208Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk159ValidityFacts chi361ValidityFacts
    leaf7208LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7208CoverageChecked :
    coverageCheck (innerAD leaf7208Box) leaf7208InnerLog = true := by
  rfl'

private theorem leaf7208InnerLogValid :
    leaf7208InnerLog.Valid 8 (innerAD leaf7208Box) :=
  wideLogDataValid_of_cachedCheck endpoint506PositiveFacts
    endpoint584PositiveFacts.valid leaf7208CoverageChecked

private noncomputable def leaf7208InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629935/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7208InputLogOnePlusV_eq :
    leaf7208InputLogOnePlusV = outerEnclosure 24
      (leaf7208Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7208RoundedFacts : LeafRoundedFacts 8
    leaf7208Certificate.logOnePlusV leaf7208InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7208InputLogOnePlusV_eq }

private noncomputable def leaf7208Inputs : Inputs :=
  inputsOfCaches globalInput sk159RoundedInputs
    chi361InputQChi innerPair818Input
    leaf7208InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7208LowerChecked :
    lowerCheck 24 leaf7208Box leaf7208Inputs = true := by
  rfl'

private theorem leaf7208CoversExact : CoversExact 8
    leaf7208Box leaf7208Certificate leaf7208InnerLog leaf7208Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk159RoundedFacts chi361RoundedFacts
    innerPair818RoundedFacts leaf7208RoundedFacts (by rfl)

private theorem leaf7208FlatSound : Sound leaf7208Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7208CertificateValid
    leaf7208InnerLogValid leaf7208CoversExact leaf7208LowerChecked

private noncomputable def leaf7209Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (25/32), chiHi := (51/64) }

private noncomputable def leaf7209Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109093/67108864) }, vSqrt := { lower := (65527/65536), upper := (17178329085/17176526848) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (273501669/268435456) }, upper := { exponent := 2, mantissa := (67/64) } }, logOuter := sk160LogOuterCertificate, logK := sk160LogKCertificate, logChi := chi361LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (34354855933/34353053696) } }, logDArg := sk160LogDArgCertificate }

private noncomputable def leaf7209InnerLog : WideLogData :=
  innerPair868Data

set_option maxRecDepth 1000000 in
private theorem leaf7209LocalValidity :
    LeafFacts leaf7209Box leaf7209Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7209Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (17178329085/17176526848) }) = true
      norm_num [leaf7209Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7209CertificateValid :
    WideCertificateValid leaf7209Box leaf7209Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk160ValidityFacts chi361ValidityFacts
    leaf7209LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7209CoverageChecked :
    coverageCheck (innerAD leaf7209Box) leaf7209InnerLog = true := by
  rfl'

private theorem leaf7209InnerLogValid :
    leaf7209InnerLog.Valid 8 (innerAD leaf7209Box) :=
  wideLogDataValid_of_cachedCheck endpoint582PositiveFacts
    endpoint584PositiveFacts.valid leaf7209CoverageChecked

private noncomputable def leaf7209InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629961/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7209InputLogOnePlusV_eq :
    leaf7209InputLogOnePlusV = outerEnclosure 24
      (leaf7209Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7209RoundedFacts : LeafRoundedFacts 8
    leaf7209Certificate.logOnePlusV leaf7209InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7209InputLogOnePlusV_eq }

private noncomputable def leaf7209Inputs : Inputs :=
  inputsOfCaches globalInput sk160RoundedInputs
    chi361InputQChi innerPair868Input
    leaf7209InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7209LowerChecked :
    lowerCheck 24 leaf7209Box leaf7209Inputs = true := by
  rfl'

private theorem leaf7209CoversExact : CoversExact 8
    leaf7209Box leaf7209Certificate leaf7209InnerLog leaf7209Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk160RoundedFacts chi361RoundedFacts
    innerPair868RoundedFacts leaf7209RoundedFacts (by rfl)

private theorem leaf7209FlatSound : Sound leaf7209Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7209CertificateValid
    leaf7209InnerLogValid leaf7209CoversExact leaf7209LowerChecked

private noncomputable def leaf7210Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (51/64), chiHi := (13/16) }

private noncomputable def leaf7210Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109093/67108864) }, vSqrt := { lower := (8191/8192), upper := (3435665817/3435302912) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (274288053/268435456) }, upper := { exponent := 2, mantissa := (1075/1024) } }, logOuter := sk159LogOuterCertificate, logK := sk159LogKCertificate, logChi := chi362LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (6870968729/6870605824) } }, logDArg := sk159LogDArgCertificate }

private noncomputable def leaf7210InnerLog : WideLogData :=
  innerPair869Data

set_option maxRecDepth 1000000 in
private theorem leaf7210LocalValidity :
    LeafFacts leaf7210Box leaf7210Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7210Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (3435665817/3435302912) }) = true
      norm_num [leaf7210Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7210CertificateValid :
    WideCertificateValid leaf7210Box leaf7210Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk159ValidityFacts chi362ValidityFacts
    leaf7210LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7210CoverageChecked :
    coverageCheck (innerAD leaf7210Box) leaf7210InnerLog = true := by
  rfl'

private theorem leaf7210InnerLogValid :
    leaf7210InnerLog.Valid 8 (innerAD leaf7210Box) :=
  wideLogDataValid_of_cachedCheck endpoint582PositiveFacts
    endpoint585PositiveFacts.valid leaf7210CoverageChecked

private noncomputable def leaf7210InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629967/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7210InputLogOnePlusV_eq :
    leaf7210InputLogOnePlusV = outerEnclosure 24
      (leaf7210Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7210RoundedFacts : LeafRoundedFacts 8
    leaf7210Certificate.logOnePlusV leaf7210InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7210InputLogOnePlusV_eq }

private noncomputable def leaf7210Inputs : Inputs :=
  inputsOfCaches globalInput sk159RoundedInputs
    chi362InputQChi innerPair869Input
    leaf7210InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7210LowerChecked :
    lowerCheck 24 leaf7210Box leaf7210Inputs = true := by
  rfl'

private theorem leaf7210CoversExact : CoversExact 8
    leaf7210Box leaf7210Certificate leaf7210InnerLog leaf7210Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk159RoundedFacts chi362RoundedFacts
    innerPair869RoundedFacts leaf7210RoundedFacts (by rfl)

private theorem leaf7210FlatSound : Sound leaf7210Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7210CertificateValid
    leaf7210InnerLogValid leaf7210CoversExact leaf7210LowerChecked

private noncomputable def leaf7211Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (51/64), chiHi := (13/16) }

private noncomputable def leaf7211Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109095/67108864) }, vSqrt := { lower := (65527/65536), upper := (5726109695/5725487104) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (277630183/268435456) }, upper := { exponent := 2, mantissa := (17/16) } }, logOuter := sk160LogOuterCertificate, logK := sk160LogKCertificate, logChi := chi362LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (11451596799/11450974208) } }, logDArg := sk160LogDArgCertificate }

private noncomputable def leaf7211InnerLog : WideLogData :=
  innerPair871Data

set_option maxRecDepth 1000000 in
private theorem leaf7211LocalValidity :
    LeafFacts leaf7211Box leaf7211Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7211Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (5726109695/5725487104) }) = true
      norm_num [leaf7211Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7211CertificateValid :
    WideCertificateValid leaf7211Box leaf7211Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk160ValidityFacts chi362ValidityFacts
    leaf7211LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7211CoverageChecked :
    coverageCheck (innerAD leaf7211Box) leaf7211InnerLog = true := by
  rfl'

private theorem leaf7211InnerLogValid :
    leaf7211InnerLog.Valid 8 (innerAD leaf7211Box) :=
  wideLogDataValid_of_cachedCheck endpoint583PositiveFacts
    endpoint585PositiveFacts.valid leaf7211CoverageChecked

private noncomputable def leaf7211InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629993/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7211InputLogOnePlusV_eq :
    leaf7211InputLogOnePlusV = outerEnclosure 24
      (leaf7211Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7211RoundedFacts : LeafRoundedFacts 8
    leaf7211Certificate.logOnePlusV leaf7211InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7211InputLogOnePlusV_eq }

private noncomputable def leaf7211Inputs : Inputs :=
  inputsOfCaches globalInput sk160RoundedInputs
    chi362InputQChi innerPair871Input
    leaf7211InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7211LowerChecked :
    lowerCheck 24 leaf7211Box leaf7211Inputs = true := by
  rfl'

private theorem leaf7211CoversExact : CoversExact 8
    leaf7211Box leaf7211Certificate leaf7211InnerLog leaf7211Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk160RoundedFacts chi362RoundedFacts
    innerPair871RoundedFacts leaf7211RoundedFacts (by rfl)

private theorem leaf7211FlatSound : Sound leaf7211Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7211CertificateValid
    leaf7211InnerLogValid leaf7211CoversExact leaf7211LowerChecked

private noncomputable def leaf7212Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (13/16), chiHi := (53/64) }

private noncomputable def leaf7212Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109091/67108864) }, vSqrt := { lower := (8191/8192), upper := (17178329085/17176558592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (271535711/268435456) }, upper := { exponent := 2, mantissa := (4257/4096) } }, logOuter := sk157LogOuterCertificate, logK := sk157LogKCertificate, logChi := chi363LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34354887677/34353117184) } }, logDArg := sk157LogDArgCertificate }

private noncomputable def leaf7212InnerLog : WideLogData :=
  innerPair818Data

set_option maxRecDepth 1000000 in
private theorem leaf7212LocalValidity :
    LeafFacts leaf7212Box leaf7212Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7212Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178329085/17176558592) }) = true
      norm_num [leaf7212Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7212CertificateValid :
    WideCertificateValid leaf7212Box leaf7212Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk157ValidityFacts chi363ValidityFacts
    leaf7212LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7212CoverageChecked :
    coverageCheck (innerAD leaf7212Box) leaf7212InnerLog = true := by
  rfl'

private theorem leaf7212InnerLogValid :
    leaf7212InnerLog.Valid 8 (innerAD leaf7212Box) :=
  wideLogDataValid_of_cachedCheck endpoint506PositiveFacts
    endpoint584PositiveFacts.valid leaf7212CoverageChecked

private noncomputable def leaf7212InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629945/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7212InputLogOnePlusV_eq :
    leaf7212InputLogOnePlusV = outerEnclosure 24
      (leaf7212Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7212RoundedFacts : LeafRoundedFacts 8
    leaf7212Certificate.logOnePlusV leaf7212InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7212InputLogOnePlusV_eq }

private noncomputable def leaf7212Inputs : Inputs :=
  inputsOfCaches globalInput sk157RoundedInputs
    chi363InputQChi innerPair818Input
    leaf7212InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7212LowerChecked :
    lowerCheck 24 leaf7212Box leaf7212Inputs = true := by
  rfl'

private theorem leaf7212CoversExact : CoversExact 8
    leaf7212Box leaf7212Certificate leaf7212InnerLog leaf7212Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk157RoundedFacts chi363RoundedFacts
    innerPair818RoundedFacts leaf7212RoundedFacts (by rfl)

private theorem leaf7212FlatSound : Sound leaf7212Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7212CertificateValid
    leaf7212InnerLogValid leaf7212CoversExact leaf7212LowerChecked

private noncomputable def leaf7213Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (13/16), chiHi := (53/64) }

private noncomputable def leaf7213Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109093/67108864) }, vSqrt := { lower := (8191/8192), upper := (1145221939/1145100288) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (274943373/268435456) }, upper := { exponent := 2, mantissa := (2155/2048) } }, logOuter := sk158LogOuterCertificate, logK := sk158LogKCertificate, logChi := chi363LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (2290322227/2290200576) } }, logDArg := sk158LogDArgCertificate }

private noncomputable def leaf7213InnerLog : WideLogData :=
  innerPair869Data

set_option maxRecDepth 1000000 in
private theorem leaf7213LocalValidity :
    LeafFacts leaf7213Box leaf7213Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7213Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (1145221939/1145100288) }) = true
      norm_num [leaf7213Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7213CertificateValid :
    WideCertificateValid leaf7213Box leaf7213Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk158ValidityFacts chi363ValidityFacts
    leaf7213LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7213CoverageChecked :
    coverageCheck (innerAD leaf7213Box) leaf7213InnerLog = true := by
  rfl'

private theorem leaf7213InnerLogValid :
    leaf7213InnerLog.Valid 8 (innerAD leaf7213Box) :=
  wideLogDataValid_of_cachedCheck endpoint582PositiveFacts
    endpoint585PositiveFacts.valid leaf7213CoverageChecked

private noncomputable def leaf7213InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907493/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf7213InputLogOnePlusV_eq :
    leaf7213InputLogOnePlusV = outerEnclosure 24
      (leaf7213Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7213RoundedFacts : LeafRoundedFacts 8
    leaf7213Certificate.logOnePlusV leaf7213InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7213InputLogOnePlusV_eq }

private noncomputable def leaf7213Inputs : Inputs :=
  inputsOfCaches globalInput sk158RoundedInputs
    chi363InputQChi innerPair869Input
    leaf7213InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7213LowerChecked :
    lowerCheck 24 leaf7213Box leaf7213Inputs = true := by
  rfl'

private theorem leaf7213CoversExact : CoversExact 8
    leaf7213Box leaf7213Certificate leaf7213InnerLog leaf7213Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk158RoundedFacts chi363RoundedFacts
    innerPair869RoundedFacts leaf7213RoundedFacts (by rfl)

private theorem leaf7213FlatSound : Sound leaf7213Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7213CertificateValid
    leaf7213InnerLogValid leaf7213CoversExact leaf7213LowerChecked

private noncomputable def leaf7214Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (53/64), chiHi := (27/32) }

private noncomputable def leaf7214Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109093/67108864) }, vSqrt := { lower := (8191/8192), upper := (17178329085/17176496128) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (275467629/268435456) }, upper := { exponent := 2, mantissa := (2159/2048) } }, logOuter := sk157LogOuterCertificate, logK := sk157LogKCertificate, logChi := chi364LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34354825213/34352992256) } }, logDArg := sk157LogDArgCertificate }

private noncomputable def leaf7214InnerLog : WideLogData :=
  innerPair869Data

set_option maxRecDepth 1000000 in
private theorem leaf7214LocalValidity :
    LeafFacts leaf7214Box leaf7214Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7214Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178329085/17176496128) }) = true
      norm_num [leaf7214Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7214CertificateValid :
    WideCertificateValid leaf7214Box leaf7214Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk157ValidityFacts chi364ValidityFacts
    leaf7214LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7214CoverageChecked :
    coverageCheck (innerAD leaf7214Box) leaf7214InnerLog = true := by
  rfl'

private theorem leaf7214InnerLogValid :
    leaf7214InnerLog.Valid 8 (innerAD leaf7214Box) :=
  wideLogDataValid_of_cachedCheck endpoint582PositiveFacts
    endpoint585PositiveFacts.valid leaf7214CoverageChecked

private noncomputable def leaf7214InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453747/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf7214InputLogOnePlusV_eq :
    leaf7214InputLogOnePlusV = outerEnclosure 24
      (leaf7214Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7214RoundedFacts : LeafRoundedFacts 8
    leaf7214Certificate.logOnePlusV leaf7214InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7214InputLogOnePlusV_eq }

private noncomputable def leaf7214Inputs : Inputs :=
  inputsOfCaches globalInput sk157RoundedInputs
    chi364InputQChi innerPair869Input
    leaf7214InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7214LowerChecked :
    lowerCheck 24 leaf7214Box leaf7214Inputs = true := by
  rfl'

private theorem leaf7214CoversExact : CoversExact 8
    leaf7214Box leaf7214Certificate leaf7214InnerLog leaf7214Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk157RoundedFacts chi364RoundedFacts
    innerPair869RoundedFacts leaf7214RoundedFacts (by rfl)

private theorem leaf7214FlatSound : Sound leaf7214Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7214CertificateValid
    leaf7214InnerLogValid leaf7214CoversExact leaf7214LowerChecked

private noncomputable def leaf7215Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (53/64), chiHi := (27/32) }

private noncomputable def leaf7215Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109095/67108864) }, vSqrt := { lower := (8191/8192), upper := (17178329085/17176440832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (278940823/268435456) }, upper := { exponent := 2, mantissa := (1093/1024) } }, logOuter := sk158LogOuterCertificate, logK := sk158LogKCertificate, logChi := chi364LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34354769917/34352881664) } }, logDArg := sk158LogDArgCertificate }

private noncomputable def leaf7215InnerLog : WideLogData :=
  innerPair872Data

set_option maxRecDepth 1000000 in
private theorem leaf7215LocalValidity :
    LeafFacts leaf7215Box leaf7215Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7215Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178329085/17176440832) }) = true
      norm_num [leaf7215Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7215CertificateValid :
    WideCertificateValid leaf7215Box leaf7215Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk158ValidityFacts chi364ValidityFacts
    leaf7215LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7215CoverageChecked :
    coverageCheck (innerAD leaf7215Box) leaf7215InnerLog = true := by
  rfl'

private theorem leaf7215InnerLogValid :
    leaf7215InnerLog.Valid 8 (innerAD leaf7215Box) :=
  wideLogDataValid_of_cachedCheck endpoint583PositiveFacts
    endpoint589PositiveFacts.valid leaf7215CoverageChecked

private noncomputable def leaf7215InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11630003/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7215InputLogOnePlusV_eq :
    leaf7215InputLogOnePlusV = outerEnclosure 24
      (leaf7215Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7215RoundedFacts : LeafRoundedFacts 8
    leaf7215Certificate.logOnePlusV leaf7215InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7215InputLogOnePlusV_eq }

private noncomputable def leaf7215Inputs : Inputs :=
  inputsOfCaches globalInput sk158RoundedInputs
    chi364InputQChi innerPair872Input
    leaf7215InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7215LowerChecked :
    lowerCheck 24 leaf7215Box leaf7215Inputs = true := by
  rfl'

private theorem leaf7215CoversExact : CoversExact 8
    leaf7215Box leaf7215Certificate leaf7215InnerLog leaf7215Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk158RoundedFacts chi364RoundedFacts
    innerPair872RoundedFacts leaf7215RoundedFacts (by rfl)

private theorem leaf7215FlatSound : Sound leaf7215Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7215CertificateValid
    leaf7215InnerLogValid leaf7215CoversExact leaf7215LowerChecked

private noncomputable def leaf7216Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (27/32), chiHi := (55/64) }

private noncomputable def leaf7216Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109095/67108864) }, vSqrt := { lower := (8191/8192), upper := (5726109695/5725477888) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (279399547/268435456) }, upper := { exponent := 2, mantissa := (4379/4096) } }, logOuter := sk157LogOuterCertificate, logK := sk157LogKCertificate, logChi := chi365LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (11451587583/11450955776) } }, logDArg := sk157LogDArgCertificate }

private noncomputable def leaf7216InnerLog : WideLogData :=
  innerPair872Data

set_option maxRecDepth 1000000 in
private theorem leaf7216LocalValidity :
    LeafFacts leaf7216Box leaf7216Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7216Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5726109695/5725477888) }) = true
      norm_num [leaf7216Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7216CertificateValid :
    WideCertificateValid leaf7216Box leaf7216Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk157ValidityFacts chi365ValidityFacts
    leaf7216LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7216CoverageChecked :
    coverageCheck (innerAD leaf7216Box) leaf7216InnerLog = true := by
  rfl'

private theorem leaf7216InnerLogValid :
    leaf7216InnerLog.Valid 8 (innerAD leaf7216Box) :=
  wideLogDataValid_of_cachedCheck endpoint583PositiveFacts
    endpoint589PositiveFacts.valid leaf7216CoverageChecked

private noncomputable def leaf7216InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5815003/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf7216InputLogOnePlusV_eq :
    leaf7216InputLogOnePlusV = outerEnclosure 24
      (leaf7216Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7216RoundedFacts : LeafRoundedFacts 8
    leaf7216Certificate.logOnePlusV leaf7216InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7216InputLogOnePlusV_eq }

private noncomputable def leaf7216Inputs : Inputs :=
  inputsOfCaches globalInput sk157RoundedInputs
    chi365InputQChi innerPair872Input
    leaf7216InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7216LowerChecked :
    lowerCheck 24 leaf7216Box leaf7216Inputs = true := by
  rfl'

private theorem leaf7216CoversExact : CoversExact 8
    leaf7216Box leaf7216Certificate leaf7216InnerLog leaf7216Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk157RoundedFacts chi365RoundedFacts
    innerPair872RoundedFacts leaf7216RoundedFacts (by rfl)

private theorem leaf7216FlatSound : Sound leaf7216Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7216CertificateValid
    leaf7216InnerLogValid leaf7216CoversExact leaf7216LowerChecked

private noncomputable def leaf7217Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (27/32), chiHi := (55/64) }

private noncomputable def leaf7217Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109097/67108864) }, vSqrt := { lower := (8191/8192), upper := (17178329085/17176377344) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (282938273/268435456) }, upper := { exponent := 2, mantissa := (2217/2048) } }, logOuter := sk158LogOuterCertificate, logK := sk158LogKCertificate, logChi := chi365LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34354706429/34352754688) } }, logDArg := sk158LogDArgCertificate }

private noncomputable def leaf7217InnerLog : WideLogData :=
  innerPair875Data

set_option maxRecDepth 1000000 in
private theorem leaf7217LocalValidity :
    LeafFacts leaf7217Box leaf7217Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7217Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178329085/17176377344) }) = true
      norm_num [leaf7217Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7217CertificateValid :
    WideCertificateValid leaf7217Box leaf7217Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk158ValidityFacts chi365ValidityFacts
    leaf7217LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7217CoverageChecked :
    coverageCheck (innerAD leaf7217Box) leaf7217InnerLog = true := by
  rfl'

private theorem leaf7217InnerLogValid :
    leaf7217InnerLog.Valid 8 (innerAD leaf7217Box) :=
  wideLogDataValid_of_cachedCheck endpoint584PositiveFacts
    endpoint590PositiveFacts.valid leaf7217CoverageChecked

private noncomputable def leaf7217InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5815017/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf7217InputLogOnePlusV_eq :
    leaf7217InputLogOnePlusV = outerEnclosure 24
      (leaf7217Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7217RoundedFacts : LeafRoundedFacts 8
    leaf7217Certificate.logOnePlusV leaf7217InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7217InputLogOnePlusV_eq }

private noncomputable def leaf7217Inputs : Inputs :=
  inputsOfCaches globalInput sk158RoundedInputs
    chi365InputQChi innerPair875Input
    leaf7217InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7217LowerChecked :
    lowerCheck 24 leaf7217Box leaf7217Inputs = true := by
  rfl'

private theorem leaf7217CoversExact : CoversExact 8
    leaf7217Box leaf7217Certificate leaf7217InnerLog leaf7217Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk158RoundedFacts chi365RoundedFacts
    innerPair875RoundedFacts leaf7217RoundedFacts (by rfl)

private theorem leaf7217FlatSound : Sound leaf7217Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7217CertificateValid
    leaf7217InnerLogValid leaf7217CoversExact leaf7217LowerChecked

private noncomputable def leaf7218Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (55/64), chiHi := (7/8) }

private noncomputable def leaf7218Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109097/67108864) }, vSqrt := { lower := (8191/8192), upper := (3435665817/3435274240) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (283331465/268435456) }, upper := { exponent := 2, mantissa := (555/512) } }, logOuter := sk157LogOuterCertificate, logK := sk157LogKCertificate, logChi := chi366LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (6870940057/6870548480) } }, logDArg := sk157LogDArgCertificate }

private noncomputable def leaf7218InnerLog : WideLogData :=
  innerPair875Data

set_option maxRecDepth 1000000 in
private theorem leaf7218LocalValidity :
    LeafFacts leaf7218Box leaf7218Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7218Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (3435665817/3435274240) }) = true
      norm_num [leaf7218Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7218CertificateValid :
    WideCertificateValid leaf7218Box leaf7218Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk157ValidityFacts chi366ValidityFacts
    leaf7218LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7218CoverageChecked :
    coverageCheck (innerAD leaf7218Box) leaf7218InnerLog = true := by
  rfl'

private theorem leaf7218InnerLogValid :
    leaf7218InnerLog.Valid 8 (innerAD leaf7218Box) :=
  wideLogDataValid_of_cachedCheck endpoint584PositiveFacts
    endpoint590PositiveFacts.valid leaf7218CoverageChecked

private noncomputable def leaf7218InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11630037/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7218InputLogOnePlusV_eq :
    leaf7218InputLogOnePlusV = outerEnclosure 24
      (leaf7218Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7218RoundedFacts : LeafRoundedFacts 8
    leaf7218Certificate.logOnePlusV leaf7218InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7218InputLogOnePlusV_eq }

private noncomputable def leaf7218Inputs : Inputs :=
  inputsOfCaches globalInput sk157RoundedInputs
    chi366InputQChi innerPair875Input
    leaf7218InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7218LowerChecked :
    lowerCheck 24 leaf7218Box leaf7218Inputs = true := by
  rfl'

private theorem leaf7218CoversExact : CoversExact 8
    leaf7218Box leaf7218Certificate leaf7218InnerLog leaf7218Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk157RoundedFacts chi366RoundedFacts
    innerPair875RoundedFacts leaf7218RoundedFacts (by rfl)

private theorem leaf7218FlatSound : Sound leaf7218Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7218CertificateValid
    leaf7218InnerLogValid leaf7218CoversExact leaf7218LowerChecked

private noncomputable def leaf7219Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (55/64), chiHi := (7/8) }

private noncomputable def leaf7219Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109099/67108864) }, vSqrt := { lower := (8191/8192), upper := (5726109695/5725437952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (286935723/268435456) }, upper := { exponent := 2, mantissa := (281/256) } }, logOuter := sk158LogOuterCertificate, logK := sk158LogKCertificate, logChi := chi366LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (11451547647/11450875904) } }, logDArg := sk158LogDArgCertificate }

private noncomputable def leaf7219InnerLog : WideLogData :=
  innerPair878Data

set_option maxRecDepth 1000000 in
private theorem leaf7219LocalValidity :
    LeafFacts leaf7219Box leaf7219Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7219Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5726109695/5725437952) }) = true
      norm_num [leaf7219Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7219CertificateValid :
    WideCertificateValid leaf7219Box leaf7219Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk158ValidityFacts chi366ValidityFacts
    leaf7219LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7219CoverageChecked :
    coverageCheck (innerAD leaf7219Box) leaf7219InnerLog = true := by
  rfl'

private theorem leaf7219InnerLogValid :
    leaf7219InnerLog.Valid 8 (innerAD leaf7219Box) :=
  wideLogDataValid_of_cachedCheck endpoint585PositiveFacts
    endpoint591PositiveFacts.valid leaf7219CoverageChecked

private noncomputable def leaf7219InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11630065/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7219InputLogOnePlusV_eq :
    leaf7219InputLogOnePlusV = outerEnclosure 24
      (leaf7219Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7219RoundedFacts : LeafRoundedFacts 8
    leaf7219Certificate.logOnePlusV leaf7219InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7219InputLogOnePlusV_eq }

private noncomputable def leaf7219Inputs : Inputs :=
  inputsOfCaches globalInput sk158RoundedInputs
    chi366InputQChi innerPair878Input
    leaf7219InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7219LowerChecked :
    lowerCheck 24 leaf7219Box leaf7219Inputs = true := by
  rfl'

private theorem leaf7219CoversExact : CoversExact 8
    leaf7219Box leaf7219Certificate leaf7219InnerLog leaf7219Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk158RoundedFacts chi366RoundedFacts
    innerPair878RoundedFacts leaf7219RoundedFacts (by rfl)

private theorem leaf7219FlatSound : Sound leaf7219Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7219CertificateValid
    leaf7219InnerLogValid leaf7219CoversExact leaf7219LowerChecked

private noncomputable def leaf7220Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (13/16), chiHi := (53/64) }

private noncomputable def leaf7220Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109095/67108864) }, vSqrt := { lower := (8191/8192), upper := (17178329085/17176450048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (278351035/268435456) }, upper := { exponent := 2, mantissa := (4363/4096) } }, logOuter := sk159LogOuterCertificate, logK := sk159LogKCertificate, logChi := chi363LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34354779133/34352900096) } }, logDArg := sk159LogDArgCertificate }

private noncomputable def leaf7220InnerLog : WideLogData :=
  innerPair872Data

set_option maxRecDepth 1000000 in
private theorem leaf7220LocalValidity :
    LeafFacts leaf7220Box leaf7220Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7220Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178329085/17176450048) }) = true
      norm_num [leaf7220Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7220CertificateValid :
    WideCertificateValid leaf7220Box leaf7220Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk159ValidityFacts chi363ValidityFacts
    leaf7220LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7220CoverageChecked :
    coverageCheck (innerAD leaf7220Box) leaf7220InnerLog = true := by
  rfl'

private theorem leaf7220InnerLogValid :
    leaf7220InnerLog.Valid 8 (innerAD leaf7220Box) :=
  wideLogDataValid_of_cachedCheck endpoint583PositiveFacts
    endpoint589PositiveFacts.valid leaf7220CoverageChecked

private noncomputable def leaf7220InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814999/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf7220InputLogOnePlusV_eq :
    leaf7220InputLogOnePlusV = outerEnclosure 24
      (leaf7220Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7220RoundedFacts : LeafRoundedFacts 8
    leaf7220Certificate.logOnePlusV leaf7220InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7220InputLogOnePlusV_eq }

private noncomputable def leaf7220Inputs : Inputs :=
  inputsOfCaches globalInput sk159RoundedInputs
    chi363InputQChi innerPair872Input
    leaf7220InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7220LowerChecked :
    lowerCheck 24 leaf7220Box leaf7220Inputs = true := by
  rfl'

private theorem leaf7220CoversExact : CoversExact 8
    leaf7220Box leaf7220Certificate leaf7220InnerLog leaf7220Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk159RoundedFacts chi363RoundedFacts
    innerPair872RoundedFacts leaf7220RoundedFacts (by rfl)

private theorem leaf7220FlatSound : Sound leaf7220Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7220CertificateValid
    leaf7220InnerLogValid leaf7220CoversExact leaf7220LowerChecked

private noncomputable def leaf7221Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (13/16), chiHi := (53/64) }

private noncomputable def leaf7221Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109097/67108864) }, vSqrt := { lower := (65527/65536), upper := (17178329085/17176395776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (281758697/268435456) }, upper := { exponent := 2, mantissa := (69/64) } }, logOuter := sk160LogOuterCertificate, logK := sk160LogKCertificate, logChi := chi363LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (34354724861/34352791552) } }, logDArg := sk160LogDArgCertificate }

private noncomputable def leaf7221InnerLog : WideLogData :=
  innerPair874Data

set_option maxRecDepth 1000000 in
private theorem leaf7221LocalValidity :
    LeafFacts leaf7221Box leaf7221Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7221Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (17178329085/17176395776) }) = true
      norm_num [leaf7221Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7221CertificateValid :
    WideCertificateValid leaf7221Box leaf7221Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk160ValidityFacts chi363ValidityFacts
    leaf7221LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7221CoverageChecked :
    coverageCheck (innerAD leaf7221Box) leaf7221InnerLog = true := by
  rfl'

private theorem leaf7221InnerLogValid :
    leaf7221InnerLog.Valid 8 (innerAD leaf7221Box) :=
  wideLogDataValid_of_cachedCheck endpoint584PositiveFacts
    endpoint589PositiveFacts.valid leaf7221CoverageChecked

private noncomputable def leaf7221InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11630025/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7221InputLogOnePlusV_eq :
    leaf7221InputLogOnePlusV = outerEnclosure 24
      (leaf7221Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7221RoundedFacts : LeafRoundedFacts 8
    leaf7221Certificate.logOnePlusV leaf7221InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7221InputLogOnePlusV_eq }

private noncomputable def leaf7221Inputs : Inputs :=
  inputsOfCaches globalInput sk160RoundedInputs
    chi363InputQChi innerPair874Input
    leaf7221InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7221LowerChecked :
    lowerCheck 24 leaf7221Box leaf7221Inputs = true := by
  rfl'

private theorem leaf7221CoversExact : CoversExact 8
    leaf7221Box leaf7221Certificate leaf7221InnerLog leaf7221Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk160RoundedFacts chi363RoundedFacts
    innerPair874RoundedFacts leaf7221RoundedFacts (by rfl)

private theorem leaf7221FlatSound : Sound leaf7221Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7221CertificateValid
    leaf7221InnerLogValid leaf7221CoversExact leaf7221LowerChecked

private noncomputable def leaf7222Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (53/64), chiHi := (27/32) }

private noncomputable def leaf7222Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109097/67108864) }, vSqrt := { lower := (8191/8192), upper := (17178329085/17176385536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (282414017/268435456) }, upper := { exponent := 2, mantissa := (2213/2048) } }, logOuter := sk159LogOuterCertificate, logK := sk159LogKCertificate, logChi := chi364LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34354714621/34352771072) } }, logDArg := sk159LogDArgCertificate }

private noncomputable def leaf7222InnerLog : WideLogData :=
  innerPair875Data

set_option maxRecDepth 1000000 in
private theorem leaf7222LocalValidity :
    LeafFacts leaf7222Box leaf7222Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7222Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178329085/17176385536) }) = true
      norm_num [leaf7222Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7222CertificateValid :
    WideCertificateValid leaf7222Box leaf7222Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk159ValidityFacts chi364ValidityFacts
    leaf7222LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7222CoverageChecked :
    coverageCheck (innerAD leaf7222Box) leaf7222InnerLog = true := by
  rfl'

private theorem leaf7222InnerLogValid :
    leaf7222InnerLog.Valid 8 (innerAD leaf7222Box) :=
  wideLogDataValid_of_cachedCheck endpoint584PositiveFacts
    endpoint590PositiveFacts.valid leaf7222CoverageChecked

private noncomputable def leaf7222InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5815015/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf7222InputLogOnePlusV_eq :
    leaf7222InputLogOnePlusV = outerEnclosure 24
      (leaf7222Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7222RoundedFacts : LeafRoundedFacts 8
    leaf7222Certificate.logOnePlusV leaf7222InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7222InputLogOnePlusV_eq }

private noncomputable def leaf7222Inputs : Inputs :=
  inputsOfCaches globalInput sk159RoundedInputs
    chi364InputQChi innerPair875Input
    leaf7222InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7222LowerChecked :
    lowerCheck 24 leaf7222Box leaf7222Inputs = true := by
  rfl'

private theorem leaf7222CoversExact : CoversExact 8
    leaf7222Box leaf7222Certificate leaf7222InnerLog leaf7222Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk159RoundedFacts chi364RoundedFacts
    innerPair875RoundedFacts leaf7222RoundedFacts (by rfl)

private theorem leaf7222FlatSound : Sound leaf7222Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7222CertificateValid
    leaf7222InnerLogValid leaf7222CoversExact leaf7222LowerChecked

private noncomputable def leaf7223Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (53/64), chiHi := (27/32) }

private noncomputable def leaf7223Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109099/67108864) }, vSqrt := { lower := (65527/65536), upper := (3435665817/3435266048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (285887211/268435456) }, upper := { exponent := 2, mantissa := (35/32) } }, logOuter := sk160LogOuterCertificate, logK := sk160LogKCertificate, logChi := chi364LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (6870931865/6870532096) } }, logDArg := sk160LogDArgCertificate }

private noncomputable def leaf7223InnerLog : WideLogData :=
  innerPair877Data

set_option maxRecDepth 1000000 in
private theorem leaf7223LocalValidity :
    LeafFacts leaf7223Box leaf7223Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7223Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (3435665817/3435266048) }) = true
      norm_num [leaf7223Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7223CertificateValid :
    WideCertificateValid leaf7223Box leaf7223Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk160ValidityFacts chi364ValidityFacts
    leaf7223LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7223CoverageChecked :
    coverageCheck (innerAD leaf7223Box) leaf7223InnerLog = true := by
  rfl'

private theorem leaf7223InnerLogValid :
    leaf7223InnerLog.Valid 8 (innerAD leaf7223Box) :=
  wideLogDataValid_of_cachedCheck endpoint585PositiveFacts
    endpoint590PositiveFacts.valid leaf7223CoverageChecked

private noncomputable def leaf7223InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11630057/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7223InputLogOnePlusV_eq :
    leaf7223InputLogOnePlusV = outerEnclosure 24
      (leaf7223Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7223RoundedFacts : LeafRoundedFacts 8
    leaf7223Certificate.logOnePlusV leaf7223InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7223InputLogOnePlusV_eq }

private noncomputable def leaf7223Inputs : Inputs :=
  inputsOfCaches globalInput sk160RoundedInputs
    chi364InputQChi innerPair877Input
    leaf7223InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7223LowerChecked :
    lowerCheck 24 leaf7223Box leaf7223Inputs = true := by
  rfl'

private theorem leaf7223CoversExact : CoversExact 8
    leaf7223Box leaf7223Certificate leaf7223InnerLog leaf7223Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk160RoundedFacts chi364RoundedFacts
    innerPair877RoundedFacts leaf7223RoundedFacts (by rfl)

private theorem leaf7223FlatSound : Sound leaf7223Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7223CertificateValid
    leaf7223InnerLogValid leaf7223CoversExact leaf7223LowerChecked

private noncomputable def leaf7224Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (27/32), chiHi := (55/64) }

private noncomputable def leaf7224Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109099/67108864) }, vSqrt := { lower := (8191/8192), upper := (17178329085/17176321024) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (286476999/268435456) }, upper := { exponent := 2, mantissa := (4489/4096) } }, logOuter := sk159LogOuterCertificate, logK := sk159LogKCertificate, logChi := chi365LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34354650109/34352642048) } }, logDArg := sk159LogDArgCertificate }

private noncomputable def leaf7224InnerLog : WideLogData :=
  innerPair878Data

set_option maxRecDepth 1000000 in
private theorem leaf7224LocalValidity :
    LeafFacts leaf7224Box leaf7224Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7224Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178329085/17176321024) }) = true
      norm_num [leaf7224Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7224CertificateValid :
    WideCertificateValid leaf7224Box leaf7224Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk159ValidityFacts chi365ValidityFacts
    leaf7224LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7224CoverageChecked :
    coverageCheck (innerAD leaf7224Box) leaf7224InnerLog = true := by
  rfl'

private theorem leaf7224InnerLogValid :
    leaf7224InnerLog.Valid 8 (innerAD leaf7224Box) :=
  wideLogDataValid_of_cachedCheck endpoint585PositiveFacts
    endpoint591PositiveFacts.valid leaf7224CoverageChecked

private noncomputable def leaf7224InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11630061/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7224InputLogOnePlusV_eq :
    leaf7224InputLogOnePlusV = outerEnclosure 24
      (leaf7224Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7224RoundedFacts : LeafRoundedFacts 8
    leaf7224Certificate.logOnePlusV leaf7224InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7224InputLogOnePlusV_eq }

private noncomputable def leaf7224Inputs : Inputs :=
  inputsOfCaches globalInput sk159RoundedInputs
    chi365InputQChi innerPair878Input
    leaf7224InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7224LowerChecked :
    lowerCheck 24 leaf7224Box leaf7224Inputs = true := by
  rfl'

private theorem leaf7224CoversExact : CoversExact 8
    leaf7224Box leaf7224Certificate leaf7224InnerLog leaf7224Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk159RoundedFacts chi365RoundedFacts
    innerPair878RoundedFacts leaf7224RoundedFacts (by rfl)

private theorem leaf7224FlatSound : Sound leaf7224Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7224CertificateValid
    leaf7224InnerLogValid leaf7224CoversExact leaf7224LowerChecked

private noncomputable def leaf7225Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (27/32), chiHi := (55/64) }

private noncomputable def leaf7225Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109101/67108864) }, vSqrt := { lower := (65527/65536), upper := (5726109695/5725421568) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (290015725/268435456) }, upper := { exponent := 2, mantissa := (71/64) } }, logOuter := sk160LogOuterCertificate, logK := sk160LogKCertificate, logChi := chi365LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (11451531263/11450843136) } }, logDArg := sk160LogDArgCertificate }

private noncomputable def leaf7225InnerLog : WideLogData :=
  innerPair881Data

set_option maxRecDepth 1000000 in
private theorem leaf7225LocalValidity :
    LeafFacts leaf7225Box leaf7225Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7225Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (5726109695/5725421568) }) = true
      norm_num [leaf7225Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7225CertificateValid :
    WideCertificateValid leaf7225Box leaf7225Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk160ValidityFacts chi365ValidityFacts
    leaf7225LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7225CoverageChecked :
    coverageCheck (innerAD leaf7225Box) leaf7225InnerLog = true := by
  rfl'

private theorem leaf7225InnerLogValid :
    leaf7225InnerLog.Valid 8 (innerAD leaf7225Box) :=
  wideLogDataValid_of_cachedCheck endpoint589PositiveFacts
    endpoint591PositiveFacts.valid leaf7225CoverageChecked

private noncomputable def leaf7225InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11630089/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7225InputLogOnePlusV_eq :
    leaf7225InputLogOnePlusV = outerEnclosure 24
      (leaf7225Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7225RoundedFacts : LeafRoundedFacts 8
    leaf7225Certificate.logOnePlusV leaf7225InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7225InputLogOnePlusV_eq }

private noncomputable def leaf7225Inputs : Inputs :=
  inputsOfCaches globalInput sk160RoundedInputs
    chi365InputQChi innerPair881Input
    leaf7225InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7225LowerChecked :
    lowerCheck 24 leaf7225Box leaf7225Inputs = true := by
  rfl'

private theorem leaf7225CoversExact : CoversExact 8
    leaf7225Box leaf7225Certificate leaf7225InnerLog leaf7225Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk160RoundedFacts chi365RoundedFacts
    innerPair881RoundedFacts leaf7225RoundedFacts (by rfl)

private theorem leaf7225FlatSound : Sound leaf7225Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7225CertificateValid
    leaf7225InnerLogValid leaf7225CoversExact leaf7225LowerChecked

private noncomputable def leaf7226Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (55/64), chiHi := (7/8) }

private noncomputable def leaf7226Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109101/67108864) }, vSqrt := { lower := (8191/8192), upper := (17178329085/17176256512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (290539981/268435456) }, upper := { exponent := 2, mantissa := (569/512) } }, logOuter := sk159LogOuterCertificate, logK := sk159LogKCertificate, logChi := chi366LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34354585597/34352513024) } }, logDArg := sk159LogDArgCertificate }

private noncomputable def leaf7226InnerLog : WideLogData :=
  innerPair882Data

set_option maxRecDepth 1000000 in
private theorem leaf7226LocalValidity :
    LeafFacts leaf7226Box leaf7226Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7226Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178329085/17176256512) }) = true
      norm_num [leaf7226Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7226CertificateValid :
    WideCertificateValid leaf7226Box leaf7226Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk159ValidityFacts chi366ValidityFacts
    leaf7226LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7226CoverageChecked :
    coverageCheck (innerAD leaf7226Box) leaf7226InnerLog = true := by
  rfl'

private theorem leaf7226InnerLogValid :
    leaf7226InnerLog.Valid 8 (innerAD leaf7226Box) :=
  wideLogDataValid_of_cachedCheck endpoint589PositiveFacts
    endpoint592PositiveFacts.valid leaf7226CoverageChecked

private noncomputable def leaf7226InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11630093/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7226InputLogOnePlusV_eq :
    leaf7226InputLogOnePlusV = outerEnclosure 24
      (leaf7226Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7226RoundedFacts : LeafRoundedFacts 8
    leaf7226Certificate.logOnePlusV leaf7226InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7226InputLogOnePlusV_eq }

private noncomputable def leaf7226Inputs : Inputs :=
  inputsOfCaches globalInput sk159RoundedInputs
    chi366InputQChi innerPair882Input
    leaf7226InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7226LowerChecked :
    lowerCheck 24 leaf7226Box leaf7226Inputs = true := by
  rfl'

private theorem leaf7226CoversExact : CoversExact 8
    leaf7226Box leaf7226Certificate leaf7226InnerLog leaf7226Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk159RoundedFacts chi366RoundedFacts
    innerPair882RoundedFacts leaf7226RoundedFacts (by rfl)

private theorem leaf7226FlatSound : Sound leaf7226Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7226CertificateValid
    leaf7226InnerLogValid leaf7226CoversExact leaf7226LowerChecked

private noncomputable def leaf7227Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (55/64), chiHi := (7/8) }

private noncomputable def leaf7227Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (8191/8192), upper := (67109103/67108864) }, vSqrt := { lower := (65527/65536), upper := (34356133881/34352398336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (294144239/268435456) }, upper := { exponent := 2, mantissa := (9/8) } }, logOuter := sk160LogOuterCertificate, logK := sk160LogKCertificate, logChi := chi366LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (68708532217/68704796672) } }, logDArg := sk160LogDArgCertificate }

private noncomputable def leaf7227InnerLog : WideLogData :=
  innerPair883Data

set_option maxRecDepth 1000000 in
private theorem leaf7227LocalValidity :
    LeafFacts leaf7227Box leaf7227Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7227Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (34356133881/34352398336) }) = true
      norm_num [leaf7227Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7227CertificateValid :
    WideCertificateValid leaf7227Box leaf7227Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk160ValidityFacts chi366ValidityFacts
    leaf7227LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7227CoverageChecked :
    coverageCheck (innerAD leaf7227Box) leaf7227InnerLog = true := by
  rfl'

private theorem leaf7227InnerLogValid :
    leaf7227InnerLog.Valid 8 (innerAD leaf7227Box) :=
  wideLogDataValid_of_cachedCheck endpoint590PositiveFacts
    endpoint592PositiveFacts.valid leaf7227CoverageChecked

private noncomputable def leaf7227InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629993/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7227InputLogOnePlusV_eq :
    leaf7227InputLogOnePlusV = outerEnclosure 24
      (leaf7227Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7227RoundedFacts : LeafRoundedFacts 8
    leaf7227Certificate.logOnePlusV leaf7227InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7227InputLogOnePlusV_eq }

private noncomputable def leaf7227Inputs : Inputs :=
  inputsOfCaches globalInput sk160RoundedInputs
    chi366InputQChi innerPair883Input
    leaf7227InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7227LowerChecked :
    lowerCheck 24 leaf7227Box leaf7227Inputs = true := by
  rfl'

private theorem leaf7227CoversExact : CoversExact 8
    leaf7227Box leaf7227Certificate leaf7227InnerLog leaf7227Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk160RoundedFacts chi366RoundedFacts
    innerPair883RoundedFacts leaf7227RoundedFacts (by rfl)

private theorem leaf7227FlatSound : Sound leaf7227Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7227CertificateValid
    leaf7227InnerLogValid leaf7227CoversExact leaf7227LowerChecked

private noncomputable def component146Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (3/4), chiHi := (49/64) }

set_option maxRecDepth 1000000 in
private theorem component146Node0_sound : Sound component146Node0Box :=
  sound_of_literal_split component146Node0Box leaf7164Box leaf7165Box
    .k (57/16) (by rfl) (by rfl)
    leaf7164FlatSound leaf7165FlatSound

private noncomputable def component146Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (49/64), chiHi := (25/32) }

set_option maxRecDepth 1000000 in
private theorem component146Node1_sound : Sound component146Node1Box :=
  sound_of_literal_split component146Node1Box leaf7166Box leaf7167Box
    .k (57/16) (by rfl) (by rfl)
    leaf7166FlatSound leaf7167FlatSound

private noncomputable def component146Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (3/4), chiHi := (25/32) }

set_option maxRecDepth 1000000 in
private theorem component146Node2_sound : Sound component146Node2Box :=
  sound_of_literal_split component146Node2Box component146Node0Box component146Node1Box
    .chi (49/64) (by rfl) (by rfl)
    component146Node0_sound component146Node1_sound

private noncomputable def component146Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (25/32), chiHi := (51/64) }

set_option maxRecDepth 1000000 in
private theorem component146Node3_sound : Sound component146Node3Box :=
  sound_of_literal_split component146Node3Box leaf7168Box leaf7169Box
    .k (57/16) (by rfl) (by rfl)
    leaf7168FlatSound leaf7169FlatSound

private noncomputable def component146Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (51/64), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component146Node4_sound : Sound component146Node4Box :=
  sound_of_literal_split component146Node4Box leaf7170Box leaf7171Box
    .k (57/16) (by rfl) (by rfl)
    leaf7170FlatSound leaf7171FlatSound

private noncomputable def component146Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (25/32), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component146Node5_sound : Sound component146Node5Box :=
  sound_of_literal_split component146Node5Box component146Node3Box component146Node4Box
    .chi (51/64) (by rfl) (by rfl)
    component146Node3_sound component146Node4_sound

private noncomputable def component146Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (3/4), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component146Node6_sound : Sound component146Node6Box :=
  sound_of_literal_split component146Node6Box component146Node2Box component146Node5Box
    .chi (25/32) (by rfl) (by rfl)
    component146Node2_sound component146Node5_sound

private noncomputable def component146Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (3/4), chiHi := (49/64) }

set_option maxRecDepth 1000000 in
private theorem component146Node7_sound : Sound component146Node7Box :=
  sound_of_literal_split component146Node7Box leaf7172Box leaf7173Box
    .k (59/16) (by rfl) (by rfl)
    leaf7172FlatSound leaf7173FlatSound

private noncomputable def component146Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (49/64), chiHi := (25/32) }

set_option maxRecDepth 1000000 in
private theorem component146Node8_sound : Sound component146Node8Box :=
  sound_of_literal_split component146Node8Box leaf7174Box leaf7175Box
    .k (59/16) (by rfl) (by rfl)
    leaf7174FlatSound leaf7175FlatSound

private noncomputable def component146Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (3/4), chiHi := (25/32) }

set_option maxRecDepth 1000000 in
private theorem component146Node9_sound : Sound component146Node9Box :=
  sound_of_literal_split component146Node9Box component146Node7Box component146Node8Box
    .chi (49/64) (by rfl) (by rfl)
    component146Node7_sound component146Node8_sound

private noncomputable def component146Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (25/32), chiHi := (51/64) }

set_option maxRecDepth 1000000 in
private theorem component146Node10_sound : Sound component146Node10Box :=
  sound_of_literal_split component146Node10Box leaf7176Box leaf7177Box
    .k (59/16) (by rfl) (by rfl)
    leaf7176FlatSound leaf7177FlatSound

private noncomputable def component146Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (51/64), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component146Node11_sound : Sound component146Node11Box :=
  sound_of_literal_split component146Node11Box leaf7178Box leaf7179Box
    .k (59/16) (by rfl) (by rfl)
    leaf7178FlatSound leaf7179FlatSound

private noncomputable def component146Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (25/32), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component146Node12_sound : Sound component146Node12Box :=
  sound_of_literal_split component146Node12Box component146Node10Box component146Node11Box
    .chi (51/64) (by rfl) (by rfl)
    component146Node10_sound component146Node11_sound

private noncomputable def component146Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (3/4), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component146Node13_sound : Sound component146Node13Box :=
  sound_of_literal_split component146Node13Box component146Node9Box component146Node12Box
    .chi (25/32) (by rfl) (by rfl)
    component146Node9_sound component146Node12_sound

private noncomputable def component146Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (15/4), chiLo := (3/4), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component146Node14_sound : Sound component146Node14Box :=
  sound_of_literal_split component146Node14Box component146Node6Box component146Node13Box
    .k (29/8) (by rfl) (by rfl)
    component146Node6_sound component146Node13_sound

private noncomputable def component146Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (13/16), chiHi := (53/64) }

set_option maxRecDepth 1000000 in
private theorem component146Node15_sound : Sound component146Node15Box :=
  sound_of_literal_split component146Node15Box leaf7180Box leaf7181Box
    .k (57/16) (by rfl) (by rfl)
    leaf7180FlatSound leaf7181FlatSound

private noncomputable def component146Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (53/64), chiHi := (27/32) }

set_option maxRecDepth 1000000 in
private theorem component146Node16_sound : Sound component146Node16Box :=
  sound_of_literal_split component146Node16Box leaf7182Box leaf7183Box
    .k (57/16) (by rfl) (by rfl)
    leaf7182FlatSound leaf7183FlatSound

private noncomputable def component146Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (13/16), chiHi := (27/32) }

set_option maxRecDepth 1000000 in
private theorem component146Node17_sound : Sound component146Node17Box :=
  sound_of_literal_split component146Node17Box component146Node15Box component146Node16Box
    .chi (53/64) (by rfl) (by rfl)
    component146Node15_sound component146Node16_sound

private noncomputable def component146Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (27/32), chiHi := (55/64) }

set_option maxRecDepth 1000000 in
private theorem component146Node18_sound : Sound component146Node18Box :=
  sound_of_literal_split component146Node18Box leaf7184Box leaf7185Box
    .k (57/16) (by rfl) (by rfl)
    leaf7184FlatSound leaf7185FlatSound

private noncomputable def component146Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (55/64), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component146Node19_sound : Sound component146Node19Box :=
  sound_of_literal_split component146Node19Box leaf7186Box leaf7187Box
    .k (57/16) (by rfl) (by rfl)
    leaf7186FlatSound leaf7187FlatSound

private noncomputable def component146Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (27/32), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component146Node20_sound : Sound component146Node20Box :=
  sound_of_literal_split component146Node20Box component146Node18Box component146Node19Box
    .chi (55/64) (by rfl) (by rfl)
    component146Node18_sound component146Node19_sound

private noncomputable def component146Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (13/16), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component146Node21_sound : Sound component146Node21Box :=
  sound_of_literal_split component146Node21Box component146Node17Box component146Node20Box
    .chi (27/32) (by rfl) (by rfl)
    component146Node17_sound component146Node20_sound

private noncomputable def component146Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (13/16), chiHi := (53/64) }

set_option maxRecDepth 1000000 in
private theorem component146Node22_sound : Sound component146Node22Box :=
  sound_of_literal_split component146Node22Box leaf7188Box leaf7189Box
    .k (59/16) (by rfl) (by rfl)
    leaf7188FlatSound leaf7189FlatSound

private noncomputable def component146Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (53/64), chiHi := (27/32) }

set_option maxRecDepth 1000000 in
private theorem component146Node23_sound : Sound component146Node23Box :=
  sound_of_literal_split component146Node23Box leaf7190Box leaf7191Box
    .k (59/16) (by rfl) (by rfl)
    leaf7190FlatSound leaf7191FlatSound

private noncomputable def component146Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (13/16), chiHi := (27/32) }

set_option maxRecDepth 1000000 in
private theorem component146Node24_sound : Sound component146Node24Box :=
  sound_of_literal_split component146Node24Box component146Node22Box component146Node23Box
    .chi (53/64) (by rfl) (by rfl)
    component146Node22_sound component146Node23_sound

private noncomputable def component146Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (27/32), chiHi := (55/64) }

set_option maxRecDepth 1000000 in
private theorem component146Node25_sound : Sound component146Node25Box :=
  sound_of_literal_split component146Node25Box leaf7192Box leaf7193Box
    .k (59/16) (by rfl) (by rfl)
    leaf7192FlatSound leaf7193FlatSound

private noncomputable def component146Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (55/64), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component146Node26_sound : Sound component146Node26Box :=
  sound_of_literal_split component146Node26Box leaf7194Box leaf7195Box
    .k (59/16) (by rfl) (by rfl)
    leaf7194FlatSound leaf7195FlatSound

private noncomputable def component146Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (27/32), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component146Node27_sound : Sound component146Node27Box :=
  sound_of_literal_split component146Node27Box component146Node25Box component146Node26Box
    .chi (55/64) (by rfl) (by rfl)
    component146Node25_sound component146Node26_sound

private noncomputable def component146Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (13/16), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component146Node28_sound : Sound component146Node28Box :=
  sound_of_literal_split component146Node28Box component146Node24Box component146Node27Box
    .chi (27/32) (by rfl) (by rfl)
    component146Node24_sound component146Node27_sound

private noncomputable def component146Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (15/4), chiLo := (13/16), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component146Node29_sound : Sound component146Node29Box :=
  sound_of_literal_split component146Node29Box component146Node21Box component146Node28Box
    .k (29/8) (by rfl) (by rfl)
    component146Node21_sound component146Node28_sound

private noncomputable def component146Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (15/4), chiLo := (3/4), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component146Node30_sound : Sound component146Node30Box :=
  sound_of_literal_split component146Node30Box component146Node14Box component146Node29Box
    .chi (13/16) (by rfl) (by rfl)
    component146Node14_sound component146Node29_sound

private noncomputable def component146Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (3/4), chiHi := (49/64) }

set_option maxRecDepth 1000000 in
private theorem component146Node31_sound : Sound component146Node31Box :=
  sound_of_literal_split component146Node31Box leaf7196Box leaf7197Box
    .k (61/16) (by rfl) (by rfl)
    leaf7196FlatSound leaf7197FlatSound

private noncomputable def component146Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (49/64), chiHi := (25/32) }

set_option maxRecDepth 1000000 in
private theorem component146Node32_sound : Sound component146Node32Box :=
  sound_of_literal_split component146Node32Box leaf7198Box leaf7199Box
    .k (61/16) (by rfl) (by rfl)
    leaf7198FlatSound leaf7199FlatSound

private noncomputable def component146Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (3/4), chiHi := (25/32) }

set_option maxRecDepth 1000000 in
private theorem component146Node33_sound : Sound component146Node33Box :=
  sound_of_literal_split component146Node33Box component146Node31Box component146Node32Box
    .chi (49/64) (by rfl) (by rfl)
    component146Node31_sound component146Node32_sound

private noncomputable def component146Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (25/32), chiHi := (51/64) }

set_option maxRecDepth 1000000 in
private theorem component146Node34_sound : Sound component146Node34Box :=
  sound_of_literal_split component146Node34Box leaf7200Box leaf7201Box
    .k (61/16) (by rfl) (by rfl)
    leaf7200FlatSound leaf7201FlatSound

private noncomputable def component146Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (51/64), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component146Node35_sound : Sound component146Node35Box :=
  sound_of_literal_split component146Node35Box leaf7202Box leaf7203Box
    .k (61/16) (by rfl) (by rfl)
    leaf7202FlatSound leaf7203FlatSound

private noncomputable def component146Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (25/32), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component146Node36_sound : Sound component146Node36Box :=
  sound_of_literal_split component146Node36Box component146Node34Box component146Node35Box
    .chi (51/64) (by rfl) (by rfl)
    component146Node34_sound component146Node35_sound

private noncomputable def component146Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (3/4), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component146Node37_sound : Sound component146Node37Box :=
  sound_of_literal_split component146Node37Box component146Node33Box component146Node36Box
    .chi (25/32) (by rfl) (by rfl)
    component146Node33_sound component146Node36_sound

private noncomputable def component146Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (3/4), chiHi := (49/64) }

set_option maxRecDepth 1000000 in
private theorem component146Node38_sound : Sound component146Node38Box :=
  sound_of_literal_split component146Node38Box leaf7204Box leaf7205Box
    .k (63/16) (by rfl) (by rfl)
    leaf7204FlatSound leaf7205FlatSound

private noncomputable def component146Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (49/64), chiHi := (25/32) }

set_option maxRecDepth 1000000 in
private theorem component146Node39_sound : Sound component146Node39Box :=
  sound_of_literal_split component146Node39Box leaf7206Box leaf7207Box
    .k (63/16) (by rfl) (by rfl)
    leaf7206FlatSound leaf7207FlatSound

private noncomputable def component146Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (3/4), chiHi := (25/32) }

set_option maxRecDepth 1000000 in
private theorem component146Node40_sound : Sound component146Node40Box :=
  sound_of_literal_split component146Node40Box component146Node38Box component146Node39Box
    .chi (49/64) (by rfl) (by rfl)
    component146Node38_sound component146Node39_sound

private noncomputable def component146Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (25/32), chiHi := (51/64) }

set_option maxRecDepth 1000000 in
private theorem component146Node41_sound : Sound component146Node41Box :=
  sound_of_literal_split component146Node41Box leaf7208Box leaf7209Box
    .k (63/16) (by rfl) (by rfl)
    leaf7208FlatSound leaf7209FlatSound

private noncomputable def component146Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (51/64), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component146Node42_sound : Sound component146Node42Box :=
  sound_of_literal_split component146Node42Box leaf7210Box leaf7211Box
    .k (63/16) (by rfl) (by rfl)
    leaf7210FlatSound leaf7211FlatSound

private noncomputable def component146Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (25/32), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component146Node43_sound : Sound component146Node43Box :=
  sound_of_literal_split component146Node43Box component146Node41Box component146Node42Box
    .chi (51/64) (by rfl) (by rfl)
    component146Node41_sound component146Node42_sound

private noncomputable def component146Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (3/4), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component146Node44_sound : Sound component146Node44Box :=
  sound_of_literal_split component146Node44Box component146Node40Box component146Node43Box
    .chi (25/32) (by rfl) (by rfl)
    component146Node40_sound component146Node43_sound

private noncomputable def component146Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (4), chiLo := (3/4), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component146Node45_sound : Sound component146Node45Box :=
  sound_of_literal_split component146Node45Box component146Node37Box component146Node44Box
    .k (31/8) (by rfl) (by rfl)
    component146Node37_sound component146Node44_sound

private noncomputable def component146Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (13/16), chiHi := (53/64) }

set_option maxRecDepth 1000000 in
private theorem component146Node46_sound : Sound component146Node46Box :=
  sound_of_literal_split component146Node46Box leaf7212Box leaf7213Box
    .k (61/16) (by rfl) (by rfl)
    leaf7212FlatSound leaf7213FlatSound

private noncomputable def component146Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (53/64), chiHi := (27/32) }

set_option maxRecDepth 1000000 in
private theorem component146Node47_sound : Sound component146Node47Box :=
  sound_of_literal_split component146Node47Box leaf7214Box leaf7215Box
    .k (61/16) (by rfl) (by rfl)
    leaf7214FlatSound leaf7215FlatSound

private noncomputable def component146Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (13/16), chiHi := (27/32) }

set_option maxRecDepth 1000000 in
private theorem component146Node48_sound : Sound component146Node48Box :=
  sound_of_literal_split component146Node48Box component146Node46Box component146Node47Box
    .chi (53/64) (by rfl) (by rfl)
    component146Node46_sound component146Node47_sound

private noncomputable def component146Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (27/32), chiHi := (55/64) }

set_option maxRecDepth 1000000 in
private theorem component146Node49_sound : Sound component146Node49Box :=
  sound_of_literal_split component146Node49Box leaf7216Box leaf7217Box
    .k (61/16) (by rfl) (by rfl)
    leaf7216FlatSound leaf7217FlatSound

private noncomputable def component146Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (55/64), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component146Node50_sound : Sound component146Node50Box :=
  sound_of_literal_split component146Node50Box leaf7218Box leaf7219Box
    .k (61/16) (by rfl) (by rfl)
    leaf7218FlatSound leaf7219FlatSound

private noncomputable def component146Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (27/32), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component146Node51_sound : Sound component146Node51Box :=
  sound_of_literal_split component146Node51Box component146Node49Box component146Node50Box
    .chi (55/64) (by rfl) (by rfl)
    component146Node49_sound component146Node50_sound

private noncomputable def component146Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (13/16), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component146Node52_sound : Sound component146Node52Box :=
  sound_of_literal_split component146Node52Box component146Node48Box component146Node51Box
    .chi (27/32) (by rfl) (by rfl)
    component146Node48_sound component146Node51_sound

private noncomputable def component146Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (13/16), chiHi := (53/64) }

set_option maxRecDepth 1000000 in
private theorem component146Node53_sound : Sound component146Node53Box :=
  sound_of_literal_split component146Node53Box leaf7220Box leaf7221Box
    .k (63/16) (by rfl) (by rfl)
    leaf7220FlatSound leaf7221FlatSound

private noncomputable def component146Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (53/64), chiHi := (27/32) }

set_option maxRecDepth 1000000 in
private theorem component146Node54_sound : Sound component146Node54Box :=
  sound_of_literal_split component146Node54Box leaf7222Box leaf7223Box
    .k (63/16) (by rfl) (by rfl)
    leaf7222FlatSound leaf7223FlatSound

private noncomputable def component146Node55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (13/16), chiHi := (27/32) }

set_option maxRecDepth 1000000 in
private theorem component146Node55_sound : Sound component146Node55Box :=
  sound_of_literal_split component146Node55Box component146Node53Box component146Node54Box
    .chi (53/64) (by rfl) (by rfl)
    component146Node53_sound component146Node54_sound

private noncomputable def component146Node56Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (27/32), chiHi := (55/64) }

set_option maxRecDepth 1000000 in
private theorem component146Node56_sound : Sound component146Node56Box :=
  sound_of_literal_split component146Node56Box leaf7224Box leaf7225Box
    .k (63/16) (by rfl) (by rfl)
    leaf7224FlatSound leaf7225FlatSound

private noncomputable def component146Node57Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (55/64), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component146Node57_sound : Sound component146Node57Box :=
  sound_of_literal_split component146Node57Box leaf7226Box leaf7227Box
    .k (63/16) (by rfl) (by rfl)
    leaf7226FlatSound leaf7227FlatSound

private noncomputable def component146Node58Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (27/32), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component146Node58_sound : Sound component146Node58Box :=
  sound_of_literal_split component146Node58Box component146Node56Box component146Node57Box
    .chi (55/64) (by rfl) (by rfl)
    component146Node56_sound component146Node57_sound

private noncomputable def component146Node59Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (13/16), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component146Node59_sound : Sound component146Node59Box :=
  sound_of_literal_split component146Node59Box component146Node55Box component146Node58Box
    .chi (27/32) (by rfl) (by rfl)
    component146Node55_sound component146Node58_sound

private noncomputable def component146Node60Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (4), chiLo := (13/16), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component146Node60_sound : Sound component146Node60Box :=
  sound_of_literal_split component146Node60Box component146Node52Box component146Node59Box
    .k (31/8) (by rfl) (by rfl)
    component146Node52_sound component146Node59_sound

private noncomputable def component146Node61Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (4), chiLo := (3/4), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component146Node61_sound : Sound component146Node61Box :=
  sound_of_literal_split component146Node61Box component146Node45Box component146Node60Box
    .chi (13/16) (by rfl) (by rfl)
    component146Node45_sound component146Node60_sound

noncomputable def component146Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (4), chiLo := (3/4), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
theorem component146_sound : Sound component146Box :=
  sound_of_literal_split component146Box component146Node30Box component146Node61Box
    .k (15/4) (by rfl) (by rfl)
    component146Node30_sound component146Node61_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
