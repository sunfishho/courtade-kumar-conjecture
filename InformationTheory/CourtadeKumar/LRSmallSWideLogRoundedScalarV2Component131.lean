import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch7
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch11
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch12
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

private noncomputable def leaf6517Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (7/8), chiHi := (29/32) }

private noncomputable def leaf6517Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554571/33554432) }, vSqrt := { lower := (32765/32768), upper := (8589426687/8588717056) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (106917367/67108864) }, upper := { exponent := 1, mantissa := (1701/1024) } }, logOuter := sk89LogOuterCertificate, logK := sk89LogKCertificate, logChi := chi92LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (17178143743/17177434112) } }, logDArg := sk89LogDArgCertificate }

private noncomputable def leaf6517InnerLog : WideLogData :=
  innerPair751Data

set_option maxRecDepth 1000000 in
private theorem leaf6517LocalValidity :
    LeafFacts leaf6517Box leaf6517Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6517Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8589426687/8588717056) }) = true
      norm_num [leaf6517Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6517CertificateValid :
    WideCertificateValid leaf6517Box leaf6517Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk89ValidityFacts chi92ValidityFacts
    leaf6517LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6517CoverageChecked :
    coverageCheck (innerAD leaf6517Box) leaf6517InnerLog = true := by
  rfl'

private theorem leaf6517InnerLogValid :
    leaf6517InnerLog.Valid 8 (innerAD leaf6517Box) :=
  wideLogDataValid_of_cachedCheck endpoint483PositiveFacts
    endpoint487PositiveFacts.valid leaf6517CoverageChecked

private noncomputable def leaf6517InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814887/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6517InputLogOnePlusV_eq :
    leaf6517InputLogOnePlusV = outerEnclosure 24
      (leaf6517Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6517RoundedFacts : LeafRoundedFacts 8
    leaf6517Certificate.logOnePlusV leaf6517InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6517InputLogOnePlusV_eq }

private noncomputable def leaf6517Inputs : Inputs :=
  inputsOfCaches globalInput sk89RoundedInputs
    chi92InputQChi innerPair751Input
    leaf6517InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6517LowerChecked :
    lowerCheck 24 leaf6517Box leaf6517Inputs = true := by
  rfl'

private theorem leaf6517CoversExact : CoversExact 8
    leaf6517Box leaf6517Certificate leaf6517InnerLog leaf6517Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk89RoundedFacts chi92RoundedFacts
    innerPair751RoundedFacts leaf6517RoundedFacts (by rfl)

private theorem leaf6517FlatSound : Sound leaf6517Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6517CertificateValid
    leaf6517InnerLogValid leaf6517CoversExact leaf6517LowerChecked

private noncomputable def leaf6518Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (7/8), chiHi := (29/32) }

private noncomputable def leaf6518Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554573/33554432) }, vSqrt := { lower := (32765/32768), upper := (8589426687/8588687360) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (108752261/67108864) }, upper := { exponent := 1, mantissa := (865/512) } }, logOuter := sk90LogOuterCertificate, logK := sk90LogKCertificate, logChi := chi92LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (17178114047/17177374720) } }, logDArg := sk90LogDArgCertificate }

private noncomputable def leaf6518InnerLog : WideLogData :=
  innerPair757Data

set_option maxRecDepth 1000000 in
private theorem leaf6518LocalValidity :
    LeafFacts leaf6518Box leaf6518Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6518Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8589426687/8588687360) }) = true
      norm_num [leaf6518Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6518CertificateValid :
    WideCertificateValid leaf6518Box leaf6518Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk90ValidityFacts chi92ValidityFacts
    leaf6518LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6518CoverageChecked :
    coverageCheck (innerAD leaf6518Box) leaf6518InnerLog = true := by
  rfl'

private theorem leaf6518InnerLogValid :
    leaf6518InnerLog.Valid 8 (innerAD leaf6518Box) :=
  wideLogDataValid_of_cachedCheck endpoint484PositiveFacts
    endpoint488PositiveFacts.valid leaf6518CoverageChecked

private noncomputable def leaf6518InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629803/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6518InputLogOnePlusV_eq :
    leaf6518InputLogOnePlusV = outerEnclosure 24
      (leaf6518Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6518RoundedFacts : LeafRoundedFacts 8
    leaf6518Certificate.logOnePlusV leaf6518InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6518InputLogOnePlusV_eq }

private noncomputable def leaf6518Inputs : Inputs :=
  inputsOfCaches globalInput sk90RoundedInputs
    chi92InputQChi innerPair757Input
    leaf6518InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6518LowerChecked :
    lowerCheck 24 leaf6518Box leaf6518Inputs = true := by
  rfl'

private theorem leaf6518CoversExact : CoversExact 8
    leaf6518Box leaf6518Certificate leaf6518InnerLog leaf6518Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk90RoundedFacts chi92RoundedFacts
    innerPair757RoundedFacts leaf6518RoundedFacts (by rfl)

private theorem leaf6518FlatSound : Sound leaf6518Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6518CertificateValid
    leaf6518InnerLogValid leaf6518CoversExact leaf6518LowerChecked

private noncomputable def leaf6519Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (29/32), chiHi := (15/16) }

private noncomputable def leaf6519Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554573/33554432) }, vSqrt := { lower := (32765/32768), upper := (8589426687/8588675072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (109538645/67108864) }, upper := { exponent := 1, mantissa := (871/512) } }, logOuter := sk89LogOuterCertificate, logK := sk89LogKCertificate, logChi := chi93LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (17178101759/17177350144) } }, logDArg := sk89LogDArgCertificate }

private noncomputable def leaf6519InnerLog : WideLogData :=
  innerPair762Data

set_option maxRecDepth 1000000 in
private theorem leaf6519LocalValidity :
    LeafFacts leaf6519Box leaf6519Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6519Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8589426687/8588675072) }) = true
      norm_num [leaf6519Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6519CertificateValid :
    WideCertificateValid leaf6519Box leaf6519Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk89ValidityFacts chi93ValidityFacts
    leaf6519LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6519CoverageChecked :
    coverageCheck (innerAD leaf6519Box) leaf6519InnerLog = true := by
  rfl'

private theorem leaf6519InnerLogValid :
    leaf6519InnerLog.Valid 8 (innerAD leaf6519Box) :=
  wideLogDataValid_of_cachedCheck endpoint485PositiveFacts
    endpoint488PositiveFacts.valid leaf6519CoverageChecked

private noncomputable def leaf6519InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629815/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6519InputLogOnePlusV_eq :
    leaf6519InputLogOnePlusV = outerEnclosure 24
      (leaf6519Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6519RoundedFacts : LeafRoundedFacts 8
    leaf6519Certificate.logOnePlusV leaf6519InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6519InputLogOnePlusV_eq }

private noncomputable def leaf6519Inputs : Inputs :=
  inputsOfCaches globalInput sk89RoundedInputs
    chi93InputQChi innerPair762Input
    leaf6519InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6519LowerChecked :
    lowerCheck 24 leaf6519Box leaf6519Inputs = true := by
  rfl'

private theorem leaf6519CoversExact : CoversExact 8
    leaf6519Box leaf6519Certificate leaf6519InnerLog leaf6519Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk89RoundedFacts chi93RoundedFacts
    innerPair762RoundedFacts leaf6519RoundedFacts (by rfl)

private theorem leaf6519FlatSound : Sound leaf6519Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6519CertificateValid
    leaf6519InnerLogValid leaf6519CoversExact leaf6519LowerChecked

private noncomputable def leaf6520Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (29/32), chiHi := (15/16) }

private noncomputable def leaf6520Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554575/33554432) }, vSqrt := { lower := (32765/32768), upper := (8589426687/8588644352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (111439071/67108864) }, upper := { exponent := 1, mantissa := (443/256) } }, logOuter := sk90LogOuterCertificate, logK := sk90LogKCertificate, logChi := chi93LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (17178071039/17177288704) } }, logDArg := sk90LogDArgCertificate }

private noncomputable def leaf6520InnerLog : WideLogData :=
  innerPair766Data

set_option maxRecDepth 1000000 in
private theorem leaf6520LocalValidity :
    LeafFacts leaf6520Box leaf6520Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6520Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8589426687/8588644352) }) = true
      norm_num [leaf6520Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6520CertificateValid :
    WideCertificateValid leaf6520Box leaf6520Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk90ValidityFacts chi93ValidityFacts
    leaf6520LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6520CoverageChecked :
    coverageCheck (innerAD leaf6520Box) leaf6520InnerLog = true := by
  rfl'

private theorem leaf6520InnerLogValid :
    leaf6520InnerLog.Valid 8 (innerAD leaf6520Box) :=
  wideLogDataValid_of_cachedCheck endpoint486PositiveFacts
    endpoint489PositiveFacts.valid leaf6520CoverageChecked

private noncomputable def leaf6520InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629845/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6520InputLogOnePlusV_eq :
    leaf6520InputLogOnePlusV = outerEnclosure 24
      (leaf6520Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6520RoundedFacts : LeafRoundedFacts 8
    leaf6520Certificate.logOnePlusV leaf6520InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6520InputLogOnePlusV_eq }

private noncomputable def leaf6520Inputs : Inputs :=
  inputsOfCaches globalInput sk90RoundedInputs
    chi93InputQChi innerPair766Input
    leaf6520InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6520LowerChecked :
    lowerCheck 24 leaf6520Box leaf6520Inputs = true := by
  rfl'

private theorem leaf6520CoversExact : CoversExact 8
    leaf6520Box leaf6520Certificate leaf6520InnerLog leaf6520Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk90RoundedFacts chi93RoundedFacts
    innerPair766RoundedFacts leaf6520RoundedFacts (by rfl)

private theorem leaf6520FlatSound : Sound leaf6520Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6520CertificateValid
    leaf6520InnerLogValid leaf6520CoversExact leaf6520LowerChecked

private noncomputable def leaf6521Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (7/8), chiHi := (29/32) }

private noncomputable def leaf6521Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554575/33554432) }, vSqrt := { lower := (32765/32768), upper := (954380743/954295296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (110587155/67108864) }, upper := { exponent := 1, mantissa := (1759/1024) } }, logOuter := sk91LogOuterCertificate, logK := sk91LogKCertificate, logChi := chi92LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (1908676039/1908590592) } }, logDArg := sk91LogDArgCertificate }

private noncomputable def leaf6521InnerLog : WideLogData :=
  innerPair762Data

set_option maxRecDepth 1000000 in
private theorem leaf6521LocalValidity :
    LeafFacts leaf6521Box leaf6521Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6521Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (954380743/954295296) }) = true
      norm_num [leaf6521Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6521CertificateValid :
    WideCertificateValid leaf6521Box leaf6521Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk91ValidityFacts chi92ValidityFacts
    leaf6521LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6521CoverageChecked :
    coverageCheck (innerAD leaf6521Box) leaf6521InnerLog = true := by
  rfl'

private theorem leaf6521InnerLogValid :
    leaf6521InnerLog.Valid 8 (innerAD leaf6521Box) :=
  wideLogDataValid_of_cachedCheck endpoint485PositiveFacts
    endpoint488PositiveFacts.valid leaf6521CoverageChecked

private noncomputable def leaf6521InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453729/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf6521InputLogOnePlusV_eq :
    leaf6521InputLogOnePlusV = outerEnclosure 24
      (leaf6521Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6521RoundedFacts : LeafRoundedFacts 8
    leaf6521Certificate.logOnePlusV leaf6521InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6521InputLogOnePlusV_eq }

private noncomputable def leaf6521Inputs : Inputs :=
  inputsOfCaches globalInput sk91RoundedInputs
    chi92InputQChi innerPair762Input
    leaf6521InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6521LowerChecked :
    lowerCheck 24 leaf6521Box leaf6521Inputs = true := by
  rfl'

private theorem leaf6521CoversExact : CoversExact 8
    leaf6521Box leaf6521Certificate leaf6521InnerLog leaf6521Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk91RoundedFacts chi92RoundedFacts
    innerPair762RoundedFacts leaf6521RoundedFacts (by rfl)

private theorem leaf6521FlatSound : Sound leaf6521Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6521CertificateValid
    leaf6521InnerLogValid leaf6521CoversExact leaf6521LowerChecked

private noncomputable def leaf6522Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (7/8), chiHi := (29/32) }

private noncomputable def leaf6522Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554577/33554432) }, vSqrt := { lower := (32765/32768), upper := (34357182459/34354511872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (112422049/67108864) }, upper := { exponent := 1, mantissa := (447/256) } }, logOuter := sk92LogOuterCertificate, logK := sk92LogKCertificate, logChi := chi92LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68711694331/68709023744) } }, logDArg := sk92LogDArgCertificate }

private noncomputable def leaf6522InnerLog : WideLogData :=
  innerPair766Data

set_option maxRecDepth 1000000 in
private theorem leaf6522LocalValidity :
    LeafFacts leaf6522Box leaf6522Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6522Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34357182459/34354511872) }) = true
      norm_num [leaf6522Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6522CertificateValid :
    WideCertificateValid leaf6522Box leaf6522Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk92ValidityFacts chi92ValidityFacts
    leaf6522LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6522CoverageChecked :
    coverageCheck (innerAD leaf6522Box) leaf6522InnerLog = true := by
  rfl'

private theorem leaf6522InnerLogValid :
    leaf6522InnerLog.Valid 8 (innerAD leaf6522Box) :=
  wideLogDataValid_of_cachedCheck endpoint486PositiveFacts
    endpoint489PositiveFacts.valid leaf6522CoverageChecked

private noncomputable def leaf6522InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629733/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6522InputLogOnePlusV_eq :
    leaf6522InputLogOnePlusV = outerEnclosure 24
      (leaf6522Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6522RoundedFacts : LeafRoundedFacts 8
    leaf6522Certificate.logOnePlusV leaf6522InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6522InputLogOnePlusV_eq }

private noncomputable def leaf6522Inputs : Inputs :=
  inputsOfCaches globalInput sk92RoundedInputs
    chi92InputQChi innerPair766Input
    leaf6522InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6522LowerChecked :
    lowerCheck 24 leaf6522Box leaf6522Inputs = true := by
  rfl'

private theorem leaf6522CoversExact : CoversExact 8
    leaf6522Box leaf6522Certificate leaf6522InnerLog leaf6522Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk92RoundedFacts chi92RoundedFacts
    innerPair766RoundedFacts leaf6522RoundedFacts (by rfl)

private theorem leaf6522FlatSound : Sound leaf6522Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6522CertificateValid
    leaf6522InnerLogValid leaf6522CoversExact leaf6522LowerChecked

private noncomputable def leaf6523Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (29/32), chiHi := (15/16) }

private noncomputable def leaf6523Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (33554577/33554432) }, vSqrt := { lower := (32765/32768), upper := (34357182459/34354454528) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (113339497/67108864) }, upper := { exponent := 1, mantissa := (901/512) } }, logOuter := sk91LogOuterCertificate, logK := sk91LogKCertificate, logChi := chi93LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68711636987/68708909056) } }, logDArg := sk91LogDArgCertificate }

private noncomputable def leaf6523InnerLog : WideLogData :=
  innerPair771Data

set_option maxRecDepth 1000000 in
private theorem leaf6523LocalValidity :
    LeafFacts leaf6523Box leaf6523Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6523Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34357182459/34354454528) }) = true
      norm_num [leaf6523Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6523CertificateValid :
    WideCertificateValid leaf6523Box leaf6523Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk91ValidityFacts chi93ValidityFacts
    leaf6523LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6523CoverageChecked :
    coverageCheck (innerAD leaf6523Box) leaf6523InnerLog = true := by
  rfl'

private theorem leaf6523InnerLogValid :
    leaf6523InnerLog.Valid 8 (innerAD leaf6523Box) :=
  wideLogDataValid_of_cachedCheck endpoint487PositiveFacts
    endpoint498PositiveFacts.valid leaf6523CoverageChecked

private noncomputable def leaf6523InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629747/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6523InputLogOnePlusV_eq :
    leaf6523InputLogOnePlusV = outerEnclosure 24
      (leaf6523Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6523RoundedFacts : LeafRoundedFacts 8
    leaf6523Certificate.logOnePlusV leaf6523InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6523InputLogOnePlusV_eq }

private noncomputable def leaf6523Inputs : Inputs :=
  inputsOfCaches globalInput sk91RoundedInputs
    chi93InputQChi innerPair771Input
    leaf6523InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6523LowerChecked :
    lowerCheck 24 leaf6523Box leaf6523Inputs = true := by
  rfl'

private theorem leaf6523CoversExact : CoversExact 8
    leaf6523Box leaf6523Certificate leaf6523InnerLog leaf6523Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk91RoundedFacts chi93RoundedFacts
    innerPair771RoundedFacts leaf6523RoundedFacts (by rfl)

private theorem leaf6523FlatSound : Sound leaf6523Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6523CertificateValid
    leaf6523InnerLogValid leaf6523CoversExact leaf6523LowerChecked

private noncomputable def leaf6524Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (29/32), chiHi := (15/16) }

private noncomputable def leaf6524Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (33554579/33554432) }, vSqrt := { lower := (32765/32768), upper := (34357182459/34354331648) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (115239923/67108864) }, upper := { exponent := 1, mantissa := (229/128) } }, logOuter := sk92LogOuterCertificate, logK := sk92LogKCertificate, logChi := chi93LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68711514107/68708663296) } }, logDArg := sk92LogDArgCertificate }

private noncomputable def leaf6524InnerLog : WideLogData :=
  innerPair773Data

set_option maxRecDepth 1000000 in
private theorem leaf6524LocalValidity :
    LeafFacts leaf6524Box leaf6524Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6524Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34357182459/34354331648) }) = true
      norm_num [leaf6524Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6524CertificateValid :
    WideCertificateValid leaf6524Box leaf6524Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk92ValidityFacts chi93ValidityFacts
    leaf6524LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6524CoverageChecked :
    coverageCheck (innerAD leaf6524Box) leaf6524InnerLog = true := by
  rfl'

private theorem leaf6524InnerLogValid :
    leaf6524InnerLog.Valid 8 (innerAD leaf6524Box) :=
  wideLogDataValid_of_cachedCheck endpoint487PositiveFacts
    endpoint500PositiveFacts.valid leaf6524CoverageChecked

private noncomputable def leaf6524InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629777/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6524InputLogOnePlusV_eq :
    leaf6524InputLogOnePlusV = outerEnclosure 24
      (leaf6524Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6524RoundedFacts : LeafRoundedFacts 8
    leaf6524Certificate.logOnePlusV leaf6524InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6524InputLogOnePlusV_eq }

private noncomputable def leaf6524Inputs : Inputs :=
  inputsOfCaches globalInput sk92RoundedInputs
    chi93InputQChi innerPair773Input
    leaf6524InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6524LowerChecked :
    lowerCheck 24 leaf6524Box leaf6524Inputs = true := by
  rfl'

private theorem leaf6524CoversExact : CoversExact 8
    leaf6524Box leaf6524Certificate leaf6524InnerLog leaf6524Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk92RoundedFacts chi93RoundedFacts
    innerPair773RoundedFacts leaf6524RoundedFacts (by rfl)

private theorem leaf6524FlatSound : Sound leaf6524Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6524CertificateValid
    leaf6524InnerLogValid leaf6524CoversExact leaf6524LowerChecked

private noncomputable def leaf6525Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (15/16), chiHi := (31/32) }

private noncomputable def leaf6525Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554575/33554432) }, vSqrt := { lower := (32765/32768), upper := (11452394153/11451510784) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (112159923/67108864) }, upper := { exponent := 1, mantissa := (1783/1024) } }, logOuter := sk89LogOuterCertificate, logK := sk89LogKCertificate, logChi := chi94LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (22903904937/22903021568) } }, logDArg := sk89LogDArgCertificate }

private noncomputable def leaf6525InnerLog : WideLogData :=
  innerPair766Data

set_option maxRecDepth 1000000 in
private theorem leaf6525LocalValidity :
    LeafFacts leaf6525Box leaf6525Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6525Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (11452394153/11451510784) }) = true
      norm_num [leaf6525Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6525CertificateValid :
    WideCertificateValid leaf6525Box leaf6525Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk89ValidityFacts chi94ValidityFacts
    leaf6525LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6525CoverageChecked :
    coverageCheck (innerAD leaf6525Box) leaf6525InnerLog = true := by
  rfl'

private theorem leaf6525InnerLogValid :
    leaf6525InnerLog.Valid 8 (innerAD leaf6525Box) :=
  wideLogDataValid_of_cachedCheck endpoint486PositiveFacts
    endpoint489PositiveFacts.valid leaf6525CoverageChecked

private noncomputable def leaf6525InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (363429/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf6525InputLogOnePlusV_eq :
    leaf6525InputLogOnePlusV = outerEnclosure 24
      (leaf6525Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6525RoundedFacts : LeafRoundedFacts 8
    leaf6525Certificate.logOnePlusV leaf6525InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6525InputLogOnePlusV_eq }

private noncomputable def leaf6525Inputs : Inputs :=
  inputsOfCaches globalInput sk89RoundedInputs
    chi94InputQChi innerPair766Input
    leaf6525InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6525LowerChecked :
    lowerCheck 24 leaf6525Box leaf6525Inputs = true := by
  rfl'

private theorem leaf6525CoversExact : CoversExact 8
    leaf6525Box leaf6525Certificate leaf6525InnerLog leaf6525Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk89RoundedFacts chi94RoundedFacts
    innerPair766RoundedFacts leaf6525RoundedFacts (by rfl)

private theorem leaf6525FlatSound : Sound leaf6525Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6525CertificateValid
    leaf6525InnerLogValid leaf6525CoversExact leaf6525LowerChecked

private noncomputable def leaf6526Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (15/16), chiHi := (31/32) }

private noncomputable def leaf6526Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (33554577/33554432) }, vSqrt := { lower := (32765/32768), upper := (34357182459/34354405376) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (114125881/67108864) }, upper := { exponent := 1, mantissa := (907/512) } }, logOuter := sk90LogOuterCertificate, logK := sk90LogKCertificate, logChi := chi94LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68711587835/68708810752) } }, logDArg := sk90LogDArgCertificate }

private noncomputable def leaf6526InnerLog : WideLogData :=
  innerPair771Data

set_option maxRecDepth 1000000 in
private theorem leaf6526LocalValidity :
    LeafFacts leaf6526Box leaf6526Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6526Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34357182459/34354405376) }) = true
      norm_num [leaf6526Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6526CertificateValid :
    WideCertificateValid leaf6526Box leaf6526Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk90ValidityFacts chi94ValidityFacts
    leaf6526LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6526CoverageChecked :
    coverageCheck (innerAD leaf6526Box) leaf6526InnerLog = true := by
  rfl'

private theorem leaf6526InnerLogValid :
    leaf6526InnerLog.Valid 8 (innerAD leaf6526Box) :=
  wideLogDataValid_of_cachedCheck endpoint487PositiveFacts
    endpoint498PositiveFacts.valid leaf6526CoverageChecked

private noncomputable def leaf6526InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629759/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6526InputLogOnePlusV_eq :
    leaf6526InputLogOnePlusV = outerEnclosure 24
      (leaf6526Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6526RoundedFacts : LeafRoundedFacts 8
    leaf6526Certificate.logOnePlusV leaf6526InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6526InputLogOnePlusV_eq }

private noncomputable def leaf6526Inputs : Inputs :=
  inputsOfCaches globalInput sk90RoundedInputs
    chi94InputQChi innerPair771Input
    leaf6526InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6526LowerChecked :
    lowerCheck 24 leaf6526Box leaf6526Inputs = true := by
  rfl'

private theorem leaf6526CoversExact : CoversExact 8
    leaf6526Box leaf6526Certificate leaf6526InnerLog leaf6526Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk90RoundedFacts chi94RoundedFacts
    innerPair771RoundedFacts leaf6526RoundedFacts (by rfl)

private theorem leaf6526FlatSound : Sound leaf6526Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6526CertificateValid
    leaf6526InnerLogValid leaf6526CoversExact leaf6526LowerChecked

private noncomputable def leaf6527Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (31/32), chiHi := (1) }

private noncomputable def leaf6527Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (33554577/33554432) }, vSqrt := { lower := (32765/32768), upper := (34357182459/34354364416) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (114781201/67108864) }, upper := { exponent := 1, mantissa := (57/32) } }, logOuter := sk89LogOuterCertificate, logK := sk89LogKCertificate, logChi := chi95LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68711546875/68708728832) } }, logDArg := sk89LogDArgCertificate }

private noncomputable def leaf6527InnerLog : WideLogData :=
  innerPair771Data

set_option maxRecDepth 1000000 in
private theorem leaf6527LocalValidity :
    LeafFacts leaf6527Box leaf6527Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6527Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34357182459/34354364416) }) = true
      norm_num [leaf6527Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6527CertificateValid :
    WideCertificateValid leaf6527Box leaf6527Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk89ValidityFacts chi95ValidityFacts
    leaf6527LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6527CoverageChecked :
    coverageCheck (innerAD leaf6527Box) leaf6527InnerLog = true := by
  rfl'

private theorem leaf6527InnerLogValid :
    leaf6527InnerLog.Valid 8 (innerAD leaf6527Box) :=
  wideLogDataValid_of_cachedCheck endpoint487PositiveFacts
    endpoint498PositiveFacts.valid leaf6527CoverageChecked

private noncomputable def leaf6527InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629769/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6527InputLogOnePlusV_eq :
    leaf6527InputLogOnePlusV = outerEnclosure 24
      (leaf6527Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6527RoundedFacts : LeafRoundedFacts 8
    leaf6527Certificate.logOnePlusV leaf6527InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6527InputLogOnePlusV_eq }

private noncomputable def leaf6527Inputs : Inputs :=
  inputsOfCaches globalInput sk89RoundedInputs
    chi95InputQChi innerPair771Input
    leaf6527InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6527LowerChecked :
    lowerCheck 24 leaf6527Box leaf6527Inputs = true := by
  rfl'

private theorem leaf6527CoversExact : CoversExact 8
    leaf6527Box leaf6527Certificate leaf6527InnerLog leaf6527Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk89RoundedFacts chi95RoundedFacts
    innerPair771RoundedFacts leaf6527RoundedFacts (by rfl)

private theorem leaf6527FlatSound : Sound leaf6527Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6527CertificateValid
    leaf6527InnerLogValid leaf6527CoversExact leaf6527LowerChecked

private noncomputable def leaf6528Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (31/32), chiHi := (1) }

private noncomputable def leaf6528Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (33554579/33554432) }, vSqrt := { lower := (32765/32768), upper := (34357182459/34354233344) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (116812691/67108864) }, upper := { exponent := 1, mantissa := (29/16) } }, logOuter := sk90LogOuterCertificate, logK := sk90LogKCertificate, logChi := chi95LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68711415803/68708466688) } }, logDArg := sk90LogDArgCertificate }

private noncomputable def leaf6528InnerLog : WideLogData :=
  innerPair776Data

set_option maxRecDepth 1000000 in
private theorem leaf6528LocalValidity :
    LeafFacts leaf6528Box leaf6528Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6528Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34357182459/34354233344) }) = true
      norm_num [leaf6528Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6528CertificateValid :
    WideCertificateValid leaf6528Box leaf6528Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk90ValidityFacts chi95ValidityFacts
    leaf6528LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6528CoverageChecked :
    coverageCheck (innerAD leaf6528Box) leaf6528InnerLog = true := by
  rfl'

private theorem leaf6528InnerLogValid :
    leaf6528InnerLog.Valid 8 (innerAD leaf6528Box) :=
  wideLogDataValid_of_cachedCheck endpoint488PositiveFacts
    endpoint500PositiveFacts.valid leaf6528CoverageChecked

private noncomputable def leaf6528InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629801/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6528InputLogOnePlusV_eq :
    leaf6528InputLogOnePlusV = outerEnclosure 24
      (leaf6528Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6528RoundedFacts : LeafRoundedFacts 8
    leaf6528Certificate.logOnePlusV leaf6528InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6528InputLogOnePlusV_eq }

private noncomputable def leaf6528Inputs : Inputs :=
  inputsOfCaches globalInput sk90RoundedInputs
    chi95InputQChi innerPair776Input
    leaf6528InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6528LowerChecked :
    lowerCheck 24 leaf6528Box leaf6528Inputs = true := by
  rfl'

private theorem leaf6528CoversExact : CoversExact 8
    leaf6528Box leaf6528Certificate leaf6528InnerLog leaf6528Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk90RoundedFacts chi95RoundedFacts
    innerPair776RoundedFacts leaf6528RoundedFacts (by rfl)

private theorem leaf6528FlatSound : Sound leaf6528Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6528CertificateValid
    leaf6528InnerLogValid leaf6528CoversExact leaf6528LowerChecked

private noncomputable def leaf6529Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (15/16), chiHi := (31/32) }

private noncomputable def leaf6529Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (33554579/33554432) }, vSqrt := { lower := (32765/32768), upper := (34357182459/34354278400) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (116091839/67108864) }, upper := { exponent := 1, mantissa := (1845/1024) } }, logOuter := sk91LogOuterCertificate, logK := sk91LogKCertificate, logChi := chi94LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68711460859/68708556800) } }, logDArg := sk91LogDArgCertificate }

private noncomputable def leaf6529InnerLog : WideLogData :=
  innerPair776Data

set_option maxRecDepth 1000000 in
private theorem leaf6529LocalValidity :
    LeafFacts leaf6529Box leaf6529Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6529Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34357182459/34354278400) }) = true
      norm_num [leaf6529Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6529CertificateValid :
    WideCertificateValid leaf6529Box leaf6529Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk91ValidityFacts chi94ValidityFacts
    leaf6529LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6529CoverageChecked :
    coverageCheck (innerAD leaf6529Box) leaf6529InnerLog = true := by
  rfl'

private theorem leaf6529InnerLogValid :
    leaf6529InnerLog.Valid 8 (innerAD leaf6529Box) :=
  wideLogDataValid_of_cachedCheck endpoint488PositiveFacts
    endpoint500PositiveFacts.valid leaf6529CoverageChecked

private noncomputable def leaf6529InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814895/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6529InputLogOnePlusV_eq :
    leaf6529InputLogOnePlusV = outerEnclosure 24
      (leaf6529Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6529RoundedFacts : LeafRoundedFacts 8
    leaf6529Certificate.logOnePlusV leaf6529InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6529InputLogOnePlusV_eq }

private noncomputable def leaf6529Inputs : Inputs :=
  inputsOfCaches globalInput sk91RoundedInputs
    chi94InputQChi innerPair776Input
    leaf6529InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6529LowerChecked :
    lowerCheck 24 leaf6529Box leaf6529Inputs = true := by
  rfl'

private theorem leaf6529CoversExact : CoversExact 8
    leaf6529Box leaf6529Certificate leaf6529InnerLog leaf6529Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk91RoundedFacts chi94RoundedFacts
    innerPair776RoundedFacts leaf6529RoundedFacts (by rfl)

private theorem leaf6529FlatSound : Sound leaf6529Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6529CertificateValid
    leaf6529InnerLogValid leaf6529CoversExact leaf6529LowerChecked

private noncomputable def leaf6530Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (15/16), chiHi := (31/32) }

private noncomputable def leaf6530Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (33554581/33554432) }, vSqrt := { lower := (32765/32768), upper := (11452394153/11451383808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (118057797/67108864) }, upper := { exponent := 1, mantissa := (469/256) } }, logOuter := sk92LogOuterCertificate, logK := sk92LogKCertificate, logChi := chi94LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (22903777961/22902767616) } }, logDArg := sk92LogDArgCertificate }

private noncomputable def leaf6530InnerLog : WideLogData :=
  innerPair779Data

set_option maxRecDepth 1000000 in
private theorem leaf6530LocalValidity :
    LeafFacts leaf6530Box leaf6530Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6530Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (11452394153/11451383808) }) = true
      norm_num [leaf6530Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6530CertificateValid :
    WideCertificateValid leaf6530Box leaf6530Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk92ValidityFacts chi94ValidityFacts
    leaf6530LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6530CoverageChecked :
    coverageCheck (innerAD leaf6530Box) leaf6530InnerLog = true := by
  rfl'

private theorem leaf6530InnerLogValid :
    leaf6530InnerLog.Valid 8 (innerAD leaf6530Box) :=
  wideLogDataValid_of_cachedCheck endpoint489PositiveFacts
    endpoint501PositiveFacts.valid leaf6530CoverageChecked

private noncomputable def leaf6530InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629821/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6530InputLogOnePlusV_eq :
    leaf6530InputLogOnePlusV = outerEnclosure 24
      (leaf6530Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6530RoundedFacts : LeafRoundedFacts 8
    leaf6530Certificate.logOnePlusV leaf6530InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6530InputLogOnePlusV_eq }

private noncomputable def leaf6530Inputs : Inputs :=
  inputsOfCaches globalInput sk92RoundedInputs
    chi94InputQChi innerPair779Input
    leaf6530InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6530LowerChecked :
    lowerCheck 24 leaf6530Box leaf6530Inputs = true := by
  rfl'

private theorem leaf6530CoversExact : CoversExact 8
    leaf6530Box leaf6530Certificate leaf6530InnerLog leaf6530Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk92RoundedFacts chi94RoundedFacts
    innerPair779RoundedFacts leaf6530RoundedFacts (by rfl)

private theorem leaf6530FlatSound : Sound leaf6530Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6530CertificateValid
    leaf6530InnerLogValid leaf6530CoversExact leaf6530LowerChecked

private noncomputable def leaf6531Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (31/32), chiHi := (1) }

private noncomputable def leaf6531Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (33554581/33554432) }, vSqrt := { lower := (32765/32768), upper := (11452394153/11451367424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (118844181/67108864) }, upper := { exponent := 1, mantissa := (59/32) } }, logOuter := sk91LogOuterCertificate, logK := sk91LogKCertificate, logChi := chi95LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (22903761577/22902734848) } }, logDArg := sk91LogDArgCertificate }

private noncomputable def leaf6531InnerLog : WideLogData :=
  innerPair779Data

set_option maxRecDepth 1000000 in
private theorem leaf6531LocalValidity :
    LeafFacts leaf6531Box leaf6531Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6531Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (11452394153/11451367424) }) = true
      norm_num [leaf6531Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6531CertificateValid :
    WideCertificateValid leaf6531Box leaf6531Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk91ValidityFacts chi95ValidityFacts
    leaf6531LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6531CoverageChecked :
    coverageCheck (innerAD leaf6531Box) leaf6531InnerLog = true := by
  rfl'

private theorem leaf6531InnerLogValid :
    leaf6531InnerLog.Valid 8 (innerAD leaf6531Box) :=
  wideLogDataValid_of_cachedCheck endpoint489PositiveFacts
    endpoint501PositiveFacts.valid leaf6531CoverageChecked

private noncomputable def leaf6531InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629833/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6531InputLogOnePlusV_eq :
    leaf6531InputLogOnePlusV = outerEnclosure 24
      (leaf6531Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6531RoundedFacts : LeafRoundedFacts 8
    leaf6531Certificate.logOnePlusV leaf6531InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6531InputLogOnePlusV_eq }

private noncomputable def leaf6531Inputs : Inputs :=
  inputsOfCaches globalInput sk91RoundedInputs
    chi95InputQChi innerPair779Input
    leaf6531InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6531LowerChecked :
    lowerCheck 24 leaf6531Box leaf6531Inputs = true := by
  rfl'

private theorem leaf6531CoversExact : CoversExact 8
    leaf6531Box leaf6531Certificate leaf6531InnerLog leaf6531Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk91RoundedFacts chi95RoundedFacts
    innerPair779RoundedFacts leaf6531RoundedFacts (by rfl)

private theorem leaf6531FlatSound : Sound leaf6531Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6531CertificateValid
    leaf6531InnerLogValid leaf6531CoversExact leaf6531LowerChecked

private noncomputable def leaf6532Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (31/32), chiHi := (1) }

private noncomputable def leaf6532Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (33554583/33554432) }, vSqrt := { lower := (32765/32768), upper := (34357182459/34353971200) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (120875671/67108864) }, upper := { exponent := 1, mantissa := (15/8) } }, logOuter := sk92LogOuterCertificate, logK := sk92LogKCertificate, logChi := chi95LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68711153659/68707942400) } }, logDArg := sk92LogDArgCertificate }

private noncomputable def leaf6532InnerLog : WideLogData :=
  innerPair795Data

set_option maxRecDepth 1000000 in
private theorem leaf6532LocalValidity :
    LeafFacts leaf6532Box leaf6532Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6532Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34357182459/34353971200) }) = true
      norm_num [leaf6532Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6532CertificateValid :
    WideCertificateValid leaf6532Box leaf6532Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk92ValidityFacts chi95ValidityFacts
    leaf6532LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6532CoverageChecked :
    coverageCheck (innerAD leaf6532Box) leaf6532InnerLog = true := by
  rfl'

private theorem leaf6532InnerLogValid :
    leaf6532InnerLog.Valid 8 (innerAD leaf6532Box) :=
  wideLogDataValid_of_cachedCheck endpoint498PositiveFacts
    endpoint502PositiveFacts.valid leaf6532CoverageChecked

private noncomputable def leaf6532InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629865/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6532InputLogOnePlusV_eq :
    leaf6532InputLogOnePlusV = outerEnclosure 24
      (leaf6532Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6532RoundedFacts : LeafRoundedFacts 8
    leaf6532Certificate.logOnePlusV leaf6532InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6532InputLogOnePlusV_eq }

private noncomputable def leaf6532Inputs : Inputs :=
  inputsOfCaches globalInput sk92RoundedInputs
    chi95InputQChi innerPair795Input
    leaf6532InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6532LowerChecked :
    lowerCheck 24 leaf6532Box leaf6532Inputs = true := by
  rfl'

private theorem leaf6532CoversExact : CoversExact 8
    leaf6532Box leaf6532Certificate leaf6532InnerLog leaf6532Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk92RoundedFacts chi95RoundedFacts
    innerPair795RoundedFacts leaf6532RoundedFacts (by rfl)

private theorem leaf6532FlatSound : Sound leaf6532Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6532CertificateValid
    leaf6532InnerLogValid leaf6532CoversExact leaf6532LowerChecked

private noncomputable def leaf6533Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (7/8), chiHi := (29/32) }

private noncomputable def leaf6533Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (33554579/33554432) }, vSqrt := { lower := (32765/32768), upper := (1808272761/1808125952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (114256943/67108864) }, upper := { exponent := 1, mantissa := (1817/1024) } }, logOuter := sk95LogOuterCertificate, logK := sk95LogKCertificate, logChi := chi92LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (3616398713/3616251904) } }, logDArg := sk95LogDArgCertificate }

private noncomputable def leaf6533InnerLog : WideLogData :=
  innerPair771Data

set_option maxRecDepth 1000000 in
private theorem leaf6533LocalValidity :
    LeafFacts leaf6533Box leaf6533Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6533Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (1808272761/1808125952) }) = true
      norm_num [leaf6533Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6533CertificateValid :
    WideCertificateValid leaf6533Box leaf6533Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk95ValidityFacts chi92ValidityFacts
    leaf6533LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6533CoverageChecked :
    coverageCheck (innerAD leaf6533Box) leaf6533InnerLog = true := by
  rfl'

private theorem leaf6533InnerLogValid :
    leaf6533InnerLog.Valid 8 (innerAD leaf6533Box) :=
  wideLogDataValid_of_cachedCheck endpoint487PositiveFacts
    endpoint498PositiveFacts.valid leaf6533CoverageChecked

private noncomputable def leaf6533InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814881/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6533InputLogOnePlusV_eq :
    leaf6533InputLogOnePlusV = outerEnclosure 24
      (leaf6533Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6533RoundedFacts : LeafRoundedFacts 8
    leaf6533Certificate.logOnePlusV leaf6533InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6533InputLogOnePlusV_eq }

private noncomputable def leaf6533Inputs : Inputs :=
  inputsOfCaches globalInput sk95RoundedInputs
    chi92InputQChi innerPair771Input
    leaf6533InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6533LowerChecked :
    lowerCheck 24 leaf6533Box leaf6533Inputs = true := by
  rfl'

private theorem leaf6533CoversExact : CoversExact 8
    leaf6533Box leaf6533Certificate leaf6533InnerLog leaf6533Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk95RoundedFacts chi92RoundedFacts
    innerPair771RoundedFacts leaf6533RoundedFacts (by rfl)

private theorem leaf6533FlatSound : Sound leaf6533Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6533CertificateValid
    leaf6533InnerLogValid leaf6533CoversExact leaf6533LowerChecked

private noncomputable def leaf6534Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (7/8), chiHi := (29/32) }

private noncomputable def leaf6534Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (33554581/33554432) }, vSqrt := { lower := (32765/32768), upper := (11452394153/11451424768) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (116091837/67108864) }, upper := { exponent := 1, mantissa := (923/512) } }, logOuter := sk96LogOuterCertificate, logK := sk96LogKCertificate, logChi := chi92LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (22903818921/22902849536) } }, logDArg := sk96LogDArgCertificate }

private noncomputable def leaf6534InnerLog : WideLogData :=
  innerPair776Data

set_option maxRecDepth 1000000 in
private theorem leaf6534LocalValidity :
    LeafFacts leaf6534Box leaf6534Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6534Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (11452394153/11451424768) }) = true
      norm_num [leaf6534Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6534CertificateValid :
    WideCertificateValid leaf6534Box leaf6534Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk96ValidityFacts chi92ValidityFacts
    leaf6534LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6534CoverageChecked :
    coverageCheck (innerAD leaf6534Box) leaf6534InnerLog = true := by
  rfl'

private theorem leaf6534InnerLogValid :
    leaf6534InnerLog.Valid 8 (innerAD leaf6534Box) :=
  wideLogDataValid_of_cachedCheck endpoint488PositiveFacts
    endpoint500PositiveFacts.valid leaf6534CoverageChecked

private noncomputable def leaf6534InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629791/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6534InputLogOnePlusV_eq :
    leaf6534InputLogOnePlusV = outerEnclosure 24
      (leaf6534Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6534RoundedFacts : LeafRoundedFacts 8
    leaf6534Certificate.logOnePlusV leaf6534InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6534InputLogOnePlusV_eq }

private noncomputable def leaf6534Inputs : Inputs :=
  inputsOfCaches globalInput sk96RoundedInputs
    chi92InputQChi innerPair776Input
    leaf6534InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6534LowerChecked :
    lowerCheck 24 leaf6534Box leaf6534Inputs = true := by
  rfl'

private theorem leaf6534CoversExact : CoversExact 8
    leaf6534Box leaf6534Certificate leaf6534InnerLog leaf6534Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk96RoundedFacts chi92RoundedFacts
    innerPair776RoundedFacts leaf6534RoundedFacts (by rfl)

private theorem leaf6534FlatSound : Sound leaf6534Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6534CertificateValid
    leaf6534InnerLogValid leaf6534CoversExact leaf6534LowerChecked

private noncomputable def leaf6535Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (29/32), chiHi := (15/16) }

private noncomputable def leaf6535Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (33554581/33554432) }, vSqrt := { lower := (32765/32768), upper := (34357182459/34354208768) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (117140349/67108864) }, upper := { exponent := 1, mantissa := (931/512) } }, logOuter := sk95LogOuterCertificate, logK := sk95LogKCertificate, logChi := chi93LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68711391227/68708417536) } }, logDArg := sk95LogDArgCertificate }

private noncomputable def leaf6535InnerLog : WideLogData :=
  innerPair777Data

set_option maxRecDepth 1000000 in
private theorem leaf6535LocalValidity :
    LeafFacts leaf6535Box leaf6535Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6535Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34357182459/34354208768) }) = true
      norm_num [leaf6535Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6535CertificateValid :
    WideCertificateValid leaf6535Box leaf6535Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk95ValidityFacts chi93ValidityFacts
    leaf6535LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6535CoverageChecked :
    coverageCheck (innerAD leaf6535Box) leaf6535InnerLog = true := by
  rfl'

private theorem leaf6535InnerLogValid :
    leaf6535InnerLog.Valid 8 (innerAD leaf6535Box) :=
  wideLogDataValid_of_cachedCheck endpoint488PositiveFacts
    endpoint501PositiveFacts.valid leaf6535CoverageChecked

private noncomputable def leaf6535InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629807/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6535InputLogOnePlusV_eq :
    leaf6535InputLogOnePlusV = outerEnclosure 24
      (leaf6535Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6535RoundedFacts : LeafRoundedFacts 8
    leaf6535Certificate.logOnePlusV leaf6535InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6535InputLogOnePlusV_eq }

private noncomputable def leaf6535Inputs : Inputs :=
  inputsOfCaches globalInput sk95RoundedInputs
    chi93InputQChi innerPair777Input
    leaf6535InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6535LowerChecked :
    lowerCheck 24 leaf6535Box leaf6535Inputs = true := by
  rfl'

private theorem leaf6535CoversExact : CoversExact 8
    leaf6535Box leaf6535Certificate leaf6535InnerLog leaf6535Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk95RoundedFacts chi93RoundedFacts
    innerPair777RoundedFacts leaf6535RoundedFacts (by rfl)

private theorem leaf6535FlatSound : Sound leaf6535Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6535CertificateValid
    leaf6535InnerLogValid leaf6535CoversExact leaf6535LowerChecked

private noncomputable def leaf6536Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (29/32), chiHi := (15/16) }

private noncomputable def leaf6536Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (33554583/33554432) }, vSqrt := { lower := (32765/32768), upper := (34357182459/34354085888) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (119040775/67108864) }, upper := { exponent := 1, mantissa := (473/256) } }, logOuter := sk96LogOuterCertificate, logK := sk96LogKCertificate, logChi := chi93LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68711268347/68708171776) } }, logDArg := sk96LogDArgCertificate }

private noncomputable def leaf6536InnerLog : WideLogData :=
  innerPair780Data

set_option maxRecDepth 1000000 in
private theorem leaf6536LocalValidity :
    LeafFacts leaf6536Box leaf6536Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6536Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34357182459/34354085888) }) = true
      norm_num [leaf6536Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6536CertificateValid :
    WideCertificateValid leaf6536Box leaf6536Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk96ValidityFacts chi93ValidityFacts
    leaf6536LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6536CoverageChecked :
    coverageCheck (innerAD leaf6536Box) leaf6536InnerLog = true := by
  rfl'

private theorem leaf6536InnerLogValid :
    leaf6536InnerLog.Valid 8 (innerAD leaf6536Box) :=
  wideLogDataValid_of_cachedCheck endpoint489PositiveFacts
    endpoint502PositiveFacts.valid leaf6536CoverageChecked

private noncomputable def leaf6536InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629837/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6536InputLogOnePlusV_eq :
    leaf6536InputLogOnePlusV = outerEnclosure 24
      (leaf6536Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6536RoundedFacts : LeafRoundedFacts 8
    leaf6536Certificate.logOnePlusV leaf6536InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6536InputLogOnePlusV_eq }

private noncomputable def leaf6536Inputs : Inputs :=
  inputsOfCaches globalInput sk96RoundedInputs
    chi93InputQChi innerPair780Input
    leaf6536InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6536LowerChecked :
    lowerCheck 24 leaf6536Box leaf6536Inputs = true := by
  rfl'

private theorem leaf6536CoversExact : CoversExact 8
    leaf6536Box leaf6536Certificate leaf6536InnerLog leaf6536Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk96RoundedFacts chi93RoundedFacts
    innerPair780RoundedFacts leaf6536RoundedFacts (by rfl)

private theorem leaf6536FlatSound : Sound leaf6536Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6536CertificateValid
    leaf6536InnerLogValid leaf6536CoversExact leaf6536LowerChecked

private noncomputable def leaf6537Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (7/8), chiHi := (29/32) }

private noncomputable def leaf6537Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (33554583/33554432) }, vSqrt := { lower := (65529/65536), upper := (34357182459/34354155520) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (117926731/67108864) }, upper := { exponent := 1, mantissa := (1875/1024) } }, logOuter := sk97LogOuterCertificate, logK := sk97LogKCertificate, logChi := chi92LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68711337979/68708311040) } }, logDArg := sk97LogDArgCertificate }

private noncomputable def leaf6537InnerLog : WideLogData :=
  innerPair779Data

set_option maxRecDepth 1000000 in
private theorem leaf6537LocalValidity :
    LeafFacts leaf6537Box leaf6537Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6537Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34357182459/34354155520) }) = true
      norm_num [leaf6537Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6537CertificateValid :
    WideCertificateValid leaf6537Box leaf6537Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk97ValidityFacts chi92ValidityFacts
    leaf6537LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6537CoverageChecked :
    coverageCheck (innerAD leaf6537Box) leaf6537InnerLog = true := by
  rfl'

private theorem leaf6537InnerLogValid :
    leaf6537InnerLog.Valid 8 (innerAD leaf6537Box) :=
  wideLogDataValid_of_cachedCheck endpoint489PositiveFacts
    endpoint501PositiveFacts.valid leaf6537CoverageChecked

private noncomputable def leaf6537InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907455/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6537InputLogOnePlusV_eq :
    leaf6537InputLogOnePlusV = outerEnclosure 24
      (leaf6537Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6537RoundedFacts : LeafRoundedFacts 8
    leaf6537Certificate.logOnePlusV leaf6537InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6537InputLogOnePlusV_eq }

private noncomputable def leaf6537Inputs : Inputs :=
  inputsOfCaches globalInput sk97RoundedInputs
    chi92InputQChi innerPair779Input
    leaf6537InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6537LowerChecked :
    lowerCheck 24 leaf6537Box leaf6537Inputs = true := by
  rfl'

private theorem leaf6537CoversExact : CoversExact 8
    leaf6537Box leaf6537Certificate leaf6537InnerLog leaf6537Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk97RoundedFacts chi92RoundedFacts
    innerPair779RoundedFacts leaf6537RoundedFacts (by rfl)

private theorem leaf6537FlatSound : Sound leaf6537Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6537CertificateValid
    leaf6537InnerLogValid leaf6537CoversExact leaf6537LowerChecked

private noncomputable def leaf6538Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (7/8), chiHi := (29/32) }

private noncomputable def leaf6538Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (33554585/33554432) }, vSqrt := { lower := (65529/65536), upper := (34357182459/34354036736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (119761625/67108864) }, upper := { exponent := 1, mantissa := (119/64) } }, logOuter := sk98LogOuterCertificate, logK := sk98LogKCertificate, logChi := chi92LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68711219195/68708073472) } }, logDArg := sk98LogDArgCertificate }

private noncomputable def leaf6538InnerLog : WideLogData :=
  innerPair795Data

set_option maxRecDepth 1000000 in
private theorem leaf6538LocalValidity :
    LeafFacts leaf6538Box leaf6538Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6538Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34357182459/34354036736) }) = true
      norm_num [leaf6538Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6538CertificateValid :
    WideCertificateValid leaf6538Box leaf6538Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk98ValidityFacts chi92ValidityFacts
    leaf6538LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6538CoverageChecked :
    coverageCheck (innerAD leaf6538Box) leaf6538InnerLog = true := by
  rfl'

private theorem leaf6538InnerLogValid :
    leaf6538InnerLog.Valid 8 (innerAD leaf6538Box) :=
  wideLogDataValid_of_cachedCheck endpoint498PositiveFacts
    endpoint502PositiveFacts.valid leaf6538CoverageChecked

private noncomputable def leaf6538InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629849/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6538InputLogOnePlusV_eq :
    leaf6538InputLogOnePlusV = outerEnclosure 24
      (leaf6538Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6538RoundedFacts : LeafRoundedFacts 8
    leaf6538Certificate.logOnePlusV leaf6538InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6538InputLogOnePlusV_eq }

private noncomputable def leaf6538Inputs : Inputs :=
  inputsOfCaches globalInput sk98RoundedInputs
    chi92InputQChi innerPair795Input
    leaf6538InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6538LowerChecked :
    lowerCheck 24 leaf6538Box leaf6538Inputs = true := by
  rfl'

private theorem leaf6538CoversExact : CoversExact 8
    leaf6538Box leaf6538Certificate leaf6538InnerLog leaf6538Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk98RoundedFacts chi92RoundedFacts
    innerPair795RoundedFacts leaf6538RoundedFacts (by rfl)

private theorem leaf6538FlatSound : Sound leaf6538Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6538CertificateValid
    leaf6538InnerLogValid leaf6538CoversExact leaf6538LowerChecked

private noncomputable def leaf6539Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (29/32), chiHi := (15/16) }

private noncomputable def leaf6539Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (33554585/33554432) }, vSqrt := { lower := (65529/65536), upper := (34357182459/34353963008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (120941201/67108864) }, upper := { exponent := 1, mantissa := (961/512) } }, logOuter := sk97LogOuterCertificate, logK := sk97LogKCertificate, logChi := chi93LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68711145467/68707926016) } }, logDArg := sk97LogDArgCertificate }

private noncomputable def leaf6539InnerLog : WideLogData :=
  innerPair796Data

set_option maxRecDepth 1000000 in
private theorem leaf6539LocalValidity :
    LeafFacts leaf6539Box leaf6539Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6539Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34357182459/34353963008) }) = true
      norm_num [leaf6539Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6539CertificateValid :
    WideCertificateValid leaf6539Box leaf6539Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk97ValidityFacts chi93ValidityFacts
    leaf6539LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6539CoverageChecked :
    coverageCheck (innerAD leaf6539Box) leaf6539InnerLog = true := by
  rfl'

private theorem leaf6539InnerLogValid :
    leaf6539InnerLog.Valid 8 (innerAD leaf6539Box) :=
  wideLogDataValid_of_cachedCheck endpoint498PositiveFacts
    endpoint503PositiveFacts.valid leaf6539CoverageChecked

private noncomputable def leaf6539InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629867/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6539InputLogOnePlusV_eq :
    leaf6539InputLogOnePlusV = outerEnclosure 24
      (leaf6539Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6539RoundedFacts : LeafRoundedFacts 8
    leaf6539Certificate.logOnePlusV leaf6539InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6539InputLogOnePlusV_eq }

private noncomputable def leaf6539Inputs : Inputs :=
  inputsOfCaches globalInput sk97RoundedInputs
    chi93InputQChi innerPair796Input
    leaf6539InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6539LowerChecked :
    lowerCheck 24 leaf6539Box leaf6539Inputs = true := by
  rfl'

private theorem leaf6539CoversExact : CoversExact 8
    leaf6539Box leaf6539Certificate leaf6539InnerLog leaf6539Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk97RoundedFacts chi93RoundedFacts
    innerPair796RoundedFacts leaf6539RoundedFacts (by rfl)

private theorem leaf6539FlatSound : Sound leaf6539Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6539CertificateValid
    leaf6539InnerLogValid leaf6539CoversExact leaf6539LowerChecked

private noncomputable def leaf6540Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (29/32), chiHi := (15/16) }

private noncomputable def leaf6540Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (33554587/33554432) }, vSqrt := { lower := (65529/65536), upper := (34357182459/34353840128) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (122841627/67108864) }, upper := { exponent := 1, mantissa := (61/32) } }, logOuter := sk98LogOuterCertificate, logK := sk98LogKCertificate, logChi := chi93LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68711022587/68707680256) } }, logDArg := sk98LogDArgCertificate }

private noncomputable def leaf6540InnerLog : WideLogData :=
  innerPair799Data

set_option maxRecDepth 1000000 in
private theorem leaf6540LocalValidity :
    LeafFacts leaf6540Box leaf6540Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6540Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34357182459/34353840128) }) = true
      norm_num [leaf6540Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6540CertificateValid :
    WideCertificateValid leaf6540Box leaf6540Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk98ValidityFacts chi93ValidityFacts
    leaf6540LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6540CoverageChecked :
    coverageCheck (innerAD leaf6540Box) leaf6540InnerLog = true := by
  rfl'

private theorem leaf6540InnerLogValid :
    leaf6540InnerLog.Valid 8 (innerAD leaf6540Box) :=
  wideLogDataValid_of_cachedCheck endpoint500PositiveFacts
    endpoint503PositiveFacts.valid leaf6540CoverageChecked

private noncomputable def leaf6540InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629897/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6540InputLogOnePlusV_eq :
    leaf6540InputLogOnePlusV = outerEnclosure 24
      (leaf6540Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6540RoundedFacts : LeafRoundedFacts 8
    leaf6540Certificate.logOnePlusV leaf6540InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6540InputLogOnePlusV_eq }

private noncomputable def leaf6540Inputs : Inputs :=
  inputsOfCaches globalInput sk98RoundedInputs
    chi93InputQChi innerPair799Input
    leaf6540InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6540LowerChecked :
    lowerCheck 24 leaf6540Box leaf6540Inputs = true := by
  rfl'

private theorem leaf6540CoversExact : CoversExact 8
    leaf6540Box leaf6540Certificate leaf6540InnerLog leaf6540Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk98RoundedFacts chi93RoundedFacts
    innerPair799RoundedFacts leaf6540RoundedFacts (by rfl)

private theorem leaf6540FlatSound : Sound leaf6540Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6540CertificateValid
    leaf6540InnerLogValid leaf6540CoversExact leaf6540LowerChecked

private noncomputable def leaf6541Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (15/16), chiHi := (31/32) }

private noncomputable def leaf6541Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (33554583/33554432) }, vSqrt := { lower := (32765/32768), upper := (34357182459/34354024448) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (120023755/67108864) }, upper := { exponent := 1, mantissa := (1907/1024) } }, logOuter := sk95LogOuterCertificate, logK := sk95LogKCertificate, logChi := chi94LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68711206907/68708048896) } }, logDArg := sk95LogDArgCertificate }

private noncomputable def leaf6541InnerLog : WideLogData :=
  innerPair795Data

set_option maxRecDepth 1000000 in
private theorem leaf6541LocalValidity :
    LeafFacts leaf6541Box leaf6541Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6541Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34357182459/34354024448) }) = true
      norm_num [leaf6541Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6541CertificateValid :
    WideCertificateValid leaf6541Box leaf6541Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk95ValidityFacts chi94ValidityFacts
    leaf6541LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6541CoverageChecked :
    coverageCheck (innerAD leaf6541Box) leaf6541InnerLog = true := by
  rfl'

private theorem leaf6541InnerLogValid :
    leaf6541InnerLog.Valid 8 (innerAD leaf6541Box) :=
  wideLogDataValid_of_cachedCheck endpoint498PositiveFacts
    endpoint502PositiveFacts.valid leaf6541CoverageChecked

private noncomputable def leaf6541InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907463/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6541InputLogOnePlusV_eq :
    leaf6541InputLogOnePlusV = outerEnclosure 24
      (leaf6541Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6541RoundedFacts : LeafRoundedFacts 8
    leaf6541Certificate.logOnePlusV leaf6541InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6541InputLogOnePlusV_eq }

private noncomputable def leaf6541Inputs : Inputs :=
  inputsOfCaches globalInput sk95RoundedInputs
    chi94InputQChi innerPair795Input
    leaf6541InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6541LowerChecked :
    lowerCheck 24 leaf6541Box leaf6541Inputs = true := by
  rfl'

private theorem leaf6541CoversExact : CoversExact 8
    leaf6541Box leaf6541Certificate leaf6541InnerLog leaf6541Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk95RoundedFacts chi94RoundedFacts
    innerPair795RoundedFacts leaf6541RoundedFacts (by rfl)

private theorem leaf6541FlatSound : Sound leaf6541Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6541CertificateValid
    leaf6541InnerLogValid leaf6541CoversExact leaf6541LowerChecked

private noncomputable def leaf6542Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (15/16), chiHi := (31/32) }

private noncomputable def leaf6542Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (33554585/33554432) }, vSqrt := { lower := (32765/32768), upper := (34357182459/34353897472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (121989713/67108864) }, upper := { exponent := 1, mantissa := (969/512) } }, logOuter := sk96LogOuterCertificate, logK := sk96LogKCertificate, logChi := chi94LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68711079931/68707794944) } }, logDArg := sk96LogDArgCertificate }

private noncomputable def leaf6542InnerLog : WideLogData :=
  innerPair799Data

set_option maxRecDepth 1000000 in
private theorem leaf6542LocalValidity :
    LeafFacts leaf6542Box leaf6542Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6542Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34357182459/34353897472) }) = true
      norm_num [leaf6542Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6542CertificateValid :
    WideCertificateValid leaf6542Box leaf6542Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk96ValidityFacts chi94ValidityFacts
    leaf6542LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6542CoverageChecked :
    coverageCheck (innerAD leaf6542Box) leaf6542InnerLog = true := by
  rfl'

private theorem leaf6542InnerLogValid :
    leaf6542InnerLog.Valid 8 (innerAD leaf6542Box) :=
  wideLogDataValid_of_cachedCheck endpoint500PositiveFacts
    endpoint503PositiveFacts.valid leaf6542CoverageChecked

private noncomputable def leaf6542InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629883/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6542InputLogOnePlusV_eq :
    leaf6542InputLogOnePlusV = outerEnclosure 24
      (leaf6542Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6542RoundedFacts : LeafRoundedFacts 8
    leaf6542Certificate.logOnePlusV leaf6542InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6542InputLogOnePlusV_eq }

private noncomputable def leaf6542Inputs : Inputs :=
  inputsOfCaches globalInput sk96RoundedInputs
    chi94InputQChi innerPair799Input
    leaf6542InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6542LowerChecked :
    lowerCheck 24 leaf6542Box leaf6542Inputs = true := by
  rfl'

private theorem leaf6542CoversExact : CoversExact 8
    leaf6542Box leaf6542Certificate leaf6542InnerLog leaf6542Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk96RoundedFacts chi94RoundedFacts
    innerPair799RoundedFacts leaf6542RoundedFacts (by rfl)

private theorem leaf6542FlatSound : Sound leaf6542Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6542CertificateValid
    leaf6542InnerLogValid leaf6542CoversExact leaf6542LowerChecked

private noncomputable def leaf6543Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (31/32), chiHi := (1) }

private noncomputable def leaf6543Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (33554585/33554432) }, vSqrt := { lower := (32765/32768), upper := (34357182459/34353840128) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (122907161/67108864) }, upper := { exponent := 1, mantissa := (61/32) } }, logOuter := sk95LogOuterCertificate, logK := sk95LogKCertificate, logChi := chi95LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68711022587/68707680256) } }, logDArg := sk95LogDArgCertificate }

private noncomputable def leaf6543InnerLog : WideLogData :=
  innerPair799Data

set_option maxRecDepth 1000000 in
private theorem leaf6543LocalValidity :
    LeafFacts leaf6543Box leaf6543Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6543Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34357182459/34353840128) }) = true
      norm_num [leaf6543Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6543CertificateValid :
    WideCertificateValid leaf6543Box leaf6543Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk95ValidityFacts chi95ValidityFacts
    leaf6543LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6543CoverageChecked :
    coverageCheck (innerAD leaf6543Box) leaf6543InnerLog = true := by
  rfl'

private theorem leaf6543InnerLogValid :
    leaf6543InnerLog.Valid 8 (innerAD leaf6543Box) :=
  wideLogDataValid_of_cachedCheck endpoint500PositiveFacts
    endpoint503PositiveFacts.valid leaf6543CoverageChecked

private noncomputable def leaf6543InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629897/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6543InputLogOnePlusV_eq :
    leaf6543InputLogOnePlusV = outerEnclosure 24
      (leaf6543Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6543RoundedFacts : LeafRoundedFacts 8
    leaf6543Certificate.logOnePlusV leaf6543InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6543InputLogOnePlusV_eq }

private noncomputable def leaf6543Inputs : Inputs :=
  inputsOfCaches globalInput sk95RoundedInputs
    chi95InputQChi innerPair799Input
    leaf6543InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6543LowerChecked :
    lowerCheck 24 leaf6543Box leaf6543Inputs = true := by
  rfl'

private theorem leaf6543CoversExact : CoversExact 8
    leaf6543Box leaf6543Certificate leaf6543InnerLog leaf6543Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk95RoundedFacts chi95RoundedFacts
    innerPair799RoundedFacts leaf6543RoundedFacts (by rfl)

private theorem leaf6543FlatSound : Sound leaf6543Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6543CertificateValid
    leaf6543InnerLogValid leaf6543CoversExact leaf6543LowerChecked

private noncomputable def leaf6544Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (31/32), chiHi := (1) }

private noncomputable def leaf6544Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (33554587/33554432) }, vSqrt := { lower := (32765/32768), upper := (11452394153/11451236352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (124938651/67108864) }, upper := { exponent := 1, mantissa := (31/16) } }, logOuter := sk96LogOuterCertificate, logK := sk96LogKCertificate, logChi := chi95LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (22903630505/22902472704) } }, logDArg := sk96LogDArgCertificate }

private noncomputable def leaf6544InnerLog : WideLogData :=
  innerPair802Data

set_option maxRecDepth 1000000 in
private theorem leaf6544LocalValidity :
    LeafFacts leaf6544Box leaf6544Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6544Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (11452394153/11451236352) }) = true
      norm_num [leaf6544Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6544CertificateValid :
    WideCertificateValid leaf6544Box leaf6544Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk96ValidityFacts chi95ValidityFacts
    leaf6544LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6544CoverageChecked :
    coverageCheck (innerAD leaf6544Box) leaf6544InnerLog = true := by
  rfl'

private theorem leaf6544InnerLogValid :
    leaf6544InnerLog.Valid 8 (innerAD leaf6544Box) :=
  wideLogDataValid_of_cachedCheck endpoint501PositiveFacts
    endpoint504PositiveFacts.valid leaf6544CoverageChecked

private noncomputable def leaf6544InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629929/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6544InputLogOnePlusV_eq :
    leaf6544InputLogOnePlusV = outerEnclosure 24
      (leaf6544Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6544RoundedFacts : LeafRoundedFacts 8
    leaf6544Certificate.logOnePlusV leaf6544InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6544InputLogOnePlusV_eq }

private noncomputable def leaf6544Inputs : Inputs :=
  inputsOfCaches globalInput sk96RoundedInputs
    chi95InputQChi innerPair802Input
    leaf6544InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6544LowerChecked :
    lowerCheck 24 leaf6544Box leaf6544Inputs = true := by
  rfl'

private theorem leaf6544CoversExact : CoversExact 8
    leaf6544Box leaf6544Certificate leaf6544InnerLog leaf6544Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk96RoundedFacts chi95RoundedFacts
    innerPair802RoundedFacts leaf6544RoundedFacts (by rfl)

private theorem leaf6544FlatSound : Sound leaf6544Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6544CertificateValid
    leaf6544InnerLogValid leaf6544CoversExact leaf6544LowerChecked

private noncomputable def leaf6545Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (15/16), chiHi := (31/32) }

private noncomputable def leaf6545Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (33554587/33554432) }, vSqrt := { lower := (65529/65536), upper := (602757587/602697728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (123955671/67108864) }, upper := { exponent := 1, mantissa := (1969/1024) } }, logOuter := sk97LogOuterCertificate, logK := sk97LogKCertificate, logChi := chi94LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (1205455315/1205395456) } }, logDArg := sk97LogDArgCertificate }

private noncomputable def leaf6545InnerLog : WideLogData :=
  innerPair802Data

set_option maxRecDepth 1000000 in
private theorem leaf6545LocalValidity :
    LeafFacts leaf6545Box leaf6545Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6545Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (602757587/602697728) }) = true
      norm_num [leaf6545Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6545CertificateValid :
    WideCertificateValid leaf6545Box leaf6545Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk97ValidityFacts chi94ValidityFacts
    leaf6545LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6545CoverageChecked :
    coverageCheck (innerAD leaf6545Box) leaf6545InnerLog = true := by
  rfl'

private theorem leaf6545InnerLogValid :
    leaf6545InnerLog.Valid 8 (innerAD leaf6545Box) :=
  wideLogDataValid_of_cachedCheck endpoint501PositiveFacts
    endpoint504PositiveFacts.valid leaf6545CoverageChecked

private noncomputable def leaf6545InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814957/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6545InputLogOnePlusV_eq :
    leaf6545InputLogOnePlusV = outerEnclosure 24
      (leaf6545Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6545RoundedFacts : LeafRoundedFacts 8
    leaf6545Certificate.logOnePlusV leaf6545InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6545InputLogOnePlusV_eq }

private noncomputable def leaf6545Inputs : Inputs :=
  inputsOfCaches globalInput sk97RoundedInputs
    chi94InputQChi innerPair802Input
    leaf6545InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6545LowerChecked :
    lowerCheck 24 leaf6545Box leaf6545Inputs = true := by
  rfl'

private theorem leaf6545CoversExact : CoversExact 8
    leaf6545Box leaf6545Certificate leaf6545InnerLog leaf6545Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk97RoundedFacts chi94RoundedFacts
    innerPair802RoundedFacts leaf6545RoundedFacts (by rfl)

private theorem leaf6545FlatSound : Sound leaf6545Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6545CertificateValid
    leaf6545InnerLogValid leaf6545CoversExact leaf6545LowerChecked

private noncomputable def leaf6546Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (15/16), chiHi := (31/32) }

private noncomputable def leaf6546Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (33554589/33554432) }, vSqrt := { lower := (65529/65536), upper := (34357182459/34353643520) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (125921629/67108864) }, upper := { exponent := 1, mantissa := (125/64) } }, logOuter := sk98LogOuterCertificate, logK := sk98LogKCertificate, logChi := chi94LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68710825979/68707287040) } }, logDArg := sk98LogDArgCertificate }

private noncomputable def leaf6546InnerLog : WideLogData :=
  innerPair806Data

set_option maxRecDepth 1000000 in
private theorem leaf6546LocalValidity :
    LeafFacts leaf6546Box leaf6546Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6546Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34357182459/34353643520) }) = true
      norm_num [leaf6546Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6546CertificateValid :
    WideCertificateValid leaf6546Box leaf6546Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk98ValidityFacts chi94ValidityFacts
    leaf6546LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6546CoverageChecked :
    coverageCheck (innerAD leaf6546Box) leaf6546InnerLog = true := by
  rfl'

private theorem leaf6546InnerLogValid :
    leaf6546InnerLog.Valid 8 (innerAD leaf6546Box) :=
  wideLogDataValid_of_cachedCheck endpoint502PositiveFacts
    endpoint505PositiveFacts.valid leaf6546CoverageChecked

private noncomputable def leaf6546InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629945/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6546InputLogOnePlusV_eq :
    leaf6546InputLogOnePlusV = outerEnclosure 24
      (leaf6546Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6546RoundedFacts : LeafRoundedFacts 8
    leaf6546Certificate.logOnePlusV leaf6546InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6546InputLogOnePlusV_eq }

private noncomputable def leaf6546Inputs : Inputs :=
  inputsOfCaches globalInput sk98RoundedInputs
    chi94InputQChi innerPair806Input
    leaf6546InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6546LowerChecked :
    lowerCheck 24 leaf6546Box leaf6546Inputs = true := by
  rfl'

private theorem leaf6546CoversExact : CoversExact 8
    leaf6546Box leaf6546Certificate leaf6546InnerLog leaf6546Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk98RoundedFacts chi94RoundedFacts
    innerPair806RoundedFacts leaf6546RoundedFacts (by rfl)

private theorem leaf6546FlatSound : Sound leaf6546Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6546CertificateValid
    leaf6546InnerLogValid leaf6546CoversExact leaf6546LowerChecked

private noncomputable def leaf6547Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (31/32), chiHi := (1) }

private noncomputable def leaf6547Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (33554589/33554432) }, vSqrt := { lower := (65529/65536), upper := (34357182459/34353577984) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (126970141/67108864) }, upper := { exponent := 1, mantissa := (63/32) } }, logOuter := sk97LogOuterCertificate, logK := sk97LogKCertificate, logChi := chi95LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68710760443/68707155968) } }, logDArg := sk97LogDArgCertificate }

private noncomputable def leaf6547InnerLog : WideLogData :=
  innerPair806Data

set_option maxRecDepth 1000000 in
private theorem leaf6547LocalValidity :
    LeafFacts leaf6547Box leaf6547Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6547Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34357182459/34353577984) }) = true
      norm_num [leaf6547Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6547CertificateValid :
    WideCertificateValid leaf6547Box leaf6547Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk97ValidityFacts chi95ValidityFacts
    leaf6547LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6547CoverageChecked :
    coverageCheck (innerAD leaf6547Box) leaf6547InnerLog = true := by
  rfl'

private theorem leaf6547InnerLogValid :
    leaf6547InnerLog.Valid 8 (innerAD leaf6547Box) :=
  wideLogDataValid_of_cachedCheck endpoint502PositiveFacts
    endpoint505PositiveFacts.valid leaf6547CoverageChecked

private noncomputable def leaf6547InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629961/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6547InputLogOnePlusV_eq :
    leaf6547InputLogOnePlusV = outerEnclosure 24
      (leaf6547Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6547RoundedFacts : LeafRoundedFacts 8
    leaf6547Certificate.logOnePlusV leaf6547InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6547InputLogOnePlusV_eq }

private noncomputable def leaf6547Inputs : Inputs :=
  inputsOfCaches globalInput sk97RoundedInputs
    chi95InputQChi innerPair806Input
    leaf6547InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6547LowerChecked :
    lowerCheck 24 leaf6547Box leaf6547Inputs = true := by
  rfl'

private theorem leaf6547CoversExact : CoversExact 8
    leaf6547Box leaf6547Certificate leaf6547InnerLog leaf6547Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk97RoundedFacts chi95RoundedFacts
    innerPair806RoundedFacts leaf6547RoundedFacts (by rfl)

private theorem leaf6547FlatSound : Sound leaf6547Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6547CertificateValid
    leaf6547InnerLogValid leaf6547CoversExact leaf6547LowerChecked

private noncomputable def leaf6548Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (31/32), chiHi := (1) }

private noncomputable def leaf6548Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (33554591/33554432) }, vSqrt := { lower := (65529/65536), upper := (17178329085/17176723456) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (129001631/67108864) }, upper := { exponent := 2, mantissa := (1) } }, logOuter := sk98LogOuterCertificate, logK := sk98LogKCertificate, logChi := chi95LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (34355052541/34353446912) } }, logDArg := sk98LogDArgCertificate }

private noncomputable def leaf6548InnerLog : WideLogData :=
  innerPair809Data

set_option maxRecDepth 1000000 in
private theorem leaf6548LocalValidity :
    LeafFacts leaf6548Box leaf6548Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6548Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (17178329085/17176723456) }) = true
      norm_num [leaf6548Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6548CertificateValid :
    WideCertificateValid leaf6548Box leaf6548Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk98ValidityFacts chi95ValidityFacts
    leaf6548LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6548CoverageChecked :
    coverageCheck (innerAD leaf6548Box) leaf6548InnerLog = true := by
  rfl'

private theorem leaf6548InnerLogValid :
    leaf6548InnerLog.Valid 8 (innerAD leaf6548Box) :=
  wideLogDataValid_of_cachedCheck endpoint503PositiveFacts
    endpoint506PositiveFacts.valid leaf6548CoverageChecked

private noncomputable def leaf6548InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629865/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6548InputLogOnePlusV_eq :
    leaf6548InputLogOnePlusV = outerEnclosure 24
      (leaf6548Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6548RoundedFacts : LeafRoundedFacts 8
    leaf6548Certificate.logOnePlusV leaf6548InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6548InputLogOnePlusV_eq }

private noncomputable def leaf6548Inputs : Inputs :=
  inputsOfCaches globalInput sk98RoundedInputs
    chi95InputQChi innerPair809Input
    leaf6548InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6548LowerChecked :
    lowerCheck 24 leaf6548Box leaf6548Inputs = true := by
  rfl'

private theorem leaf6548CoversExact : CoversExact 8
    leaf6548Box leaf6548Certificate leaf6548InnerLog leaf6548Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk98RoundedFacts chi95RoundedFacts
    innerPair809RoundedFacts leaf6548RoundedFacts (by rfl)

private theorem leaf6548FlatSound : Sound leaf6548Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6548CertificateValid
    leaf6548InnerLogValid leaf6548CoversExact leaf6548LowerChecked

private noncomputable def component131Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (7/8), chiHi := (29/32) }

set_option maxRecDepth 1000000 in
private theorem component131Node0_sound : Sound component131Node0Box :=
  sound_of_literal_split component131Node0Box leaf6517Box leaf6518Box
    .k (41/16) (by rfl) (by rfl)
    leaf6517FlatSound leaf6518FlatSound

private noncomputable def component131Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (29/32), chiHi := (15/16) }

set_option maxRecDepth 1000000 in
private theorem component131Node1_sound : Sound component131Node1Box :=
  sound_of_literal_split component131Node1Box leaf6519Box leaf6520Box
    .k (41/16) (by rfl) (by rfl)
    leaf6519FlatSound leaf6520FlatSound

private noncomputable def component131Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (7/8), chiHi := (15/16) }

set_option maxRecDepth 1000000 in
private theorem component131Node2_sound : Sound component131Node2Box :=
  sound_of_literal_split component131Node2Box component131Node0Box component131Node1Box
    .chi (29/32) (by rfl) (by rfl)
    component131Node0_sound component131Node1_sound

private noncomputable def component131Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (7/8), chiHi := (29/32) }

set_option maxRecDepth 1000000 in
private theorem component131Node3_sound : Sound component131Node3Box :=
  sound_of_literal_split component131Node3Box leaf6521Box leaf6522Box
    .k (43/16) (by rfl) (by rfl)
    leaf6521FlatSound leaf6522FlatSound

private noncomputable def component131Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (29/32), chiHi := (15/16) }

set_option maxRecDepth 1000000 in
private theorem component131Node4_sound : Sound component131Node4Box :=
  sound_of_literal_split component131Node4Box leaf6523Box leaf6524Box
    .k (43/16) (by rfl) (by rfl)
    leaf6523FlatSound leaf6524FlatSound

private noncomputable def component131Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (7/8), chiHi := (15/16) }

set_option maxRecDepth 1000000 in
private theorem component131Node5_sound : Sound component131Node5Box :=
  sound_of_literal_split component131Node5Box component131Node3Box component131Node4Box
    .chi (29/32) (by rfl) (by rfl)
    component131Node3_sound component131Node4_sound

private noncomputable def component131Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (11/4), chiLo := (7/8), chiHi := (15/16) }

set_option maxRecDepth 1000000 in
private theorem component131Node6_sound : Sound component131Node6Box :=
  sound_of_literal_split component131Node6Box component131Node2Box component131Node5Box
    .k (21/8) (by rfl) (by rfl)
    component131Node2_sound component131Node5_sound

private noncomputable def component131Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (15/16), chiHi := (31/32) }

set_option maxRecDepth 1000000 in
private theorem component131Node7_sound : Sound component131Node7Box :=
  sound_of_literal_split component131Node7Box leaf6525Box leaf6526Box
    .k (41/16) (by rfl) (by rfl)
    leaf6525FlatSound leaf6526FlatSound

private noncomputable def component131Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (31/32), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component131Node8_sound : Sound component131Node8Box :=
  sound_of_literal_split component131Node8Box leaf6527Box leaf6528Box
    .k (41/16) (by rfl) (by rfl)
    leaf6527FlatSound leaf6528FlatSound

private noncomputable def component131Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (15/16), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component131Node9_sound : Sound component131Node9Box :=
  sound_of_literal_split component131Node9Box component131Node7Box component131Node8Box
    .chi (31/32) (by rfl) (by rfl)
    component131Node7_sound component131Node8_sound

private noncomputable def component131Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (15/16), chiHi := (31/32) }

set_option maxRecDepth 1000000 in
private theorem component131Node10_sound : Sound component131Node10Box :=
  sound_of_literal_split component131Node10Box leaf6529Box leaf6530Box
    .k (43/16) (by rfl) (by rfl)
    leaf6529FlatSound leaf6530FlatSound

private noncomputable def component131Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (31/32), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component131Node11_sound : Sound component131Node11Box :=
  sound_of_literal_split component131Node11Box leaf6531Box leaf6532Box
    .k (43/16) (by rfl) (by rfl)
    leaf6531FlatSound leaf6532FlatSound

private noncomputable def component131Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (15/16), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component131Node12_sound : Sound component131Node12Box :=
  sound_of_literal_split component131Node12Box component131Node10Box component131Node11Box
    .chi (31/32) (by rfl) (by rfl)
    component131Node10_sound component131Node11_sound

private noncomputable def component131Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (11/4), chiLo := (15/16), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component131Node13_sound : Sound component131Node13Box :=
  sound_of_literal_split component131Node13Box component131Node9Box component131Node12Box
    .k (21/8) (by rfl) (by rfl)
    component131Node9_sound component131Node12_sound

private noncomputable def component131Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (11/4), chiLo := (7/8), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component131Node14_sound : Sound component131Node14Box :=
  sound_of_literal_split component131Node14Box component131Node6Box component131Node13Box
    .chi (15/16) (by rfl) (by rfl)
    component131Node6_sound component131Node13_sound

private noncomputable def component131Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (7/8), chiHi := (29/32) }

set_option maxRecDepth 1000000 in
private theorem component131Node15_sound : Sound component131Node15Box :=
  sound_of_literal_split component131Node15Box leaf6533Box leaf6534Box
    .k (45/16) (by rfl) (by rfl)
    leaf6533FlatSound leaf6534FlatSound

private noncomputable def component131Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (29/32), chiHi := (15/16) }

set_option maxRecDepth 1000000 in
private theorem component131Node16_sound : Sound component131Node16Box :=
  sound_of_literal_split component131Node16Box leaf6535Box leaf6536Box
    .k (45/16) (by rfl) (by rfl)
    leaf6535FlatSound leaf6536FlatSound

private noncomputable def component131Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (7/8), chiHi := (15/16) }

set_option maxRecDepth 1000000 in
private theorem component131Node17_sound : Sound component131Node17Box :=
  sound_of_literal_split component131Node17Box component131Node15Box component131Node16Box
    .chi (29/32) (by rfl) (by rfl)
    component131Node15_sound component131Node16_sound

private noncomputable def component131Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (7/8), chiHi := (29/32) }

set_option maxRecDepth 1000000 in
private theorem component131Node18_sound : Sound component131Node18Box :=
  sound_of_literal_split component131Node18Box leaf6537Box leaf6538Box
    .k (47/16) (by rfl) (by rfl)
    leaf6537FlatSound leaf6538FlatSound

private noncomputable def component131Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (29/32), chiHi := (15/16) }

set_option maxRecDepth 1000000 in
private theorem component131Node19_sound : Sound component131Node19Box :=
  sound_of_literal_split component131Node19Box leaf6539Box leaf6540Box
    .k (47/16) (by rfl) (by rfl)
    leaf6539FlatSound leaf6540FlatSound

private noncomputable def component131Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (7/8), chiHi := (15/16) }

set_option maxRecDepth 1000000 in
private theorem component131Node20_sound : Sound component131Node20Box :=
  sound_of_literal_split component131Node20Box component131Node18Box component131Node19Box
    .chi (29/32) (by rfl) (by rfl)
    component131Node18_sound component131Node19_sound

private noncomputable def component131Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (3), chiLo := (7/8), chiHi := (15/16) }

set_option maxRecDepth 1000000 in
private theorem component131Node21_sound : Sound component131Node21Box :=
  sound_of_literal_split component131Node21Box component131Node17Box component131Node20Box
    .k (23/8) (by rfl) (by rfl)
    component131Node17_sound component131Node20_sound

private noncomputable def component131Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (15/16), chiHi := (31/32) }

set_option maxRecDepth 1000000 in
private theorem component131Node22_sound : Sound component131Node22Box :=
  sound_of_literal_split component131Node22Box leaf6541Box leaf6542Box
    .k (45/16) (by rfl) (by rfl)
    leaf6541FlatSound leaf6542FlatSound

private noncomputable def component131Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (31/32), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component131Node23_sound : Sound component131Node23Box :=
  sound_of_literal_split component131Node23Box leaf6543Box leaf6544Box
    .k (45/16) (by rfl) (by rfl)
    leaf6543FlatSound leaf6544FlatSound

private noncomputable def component131Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (15/16), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component131Node24_sound : Sound component131Node24Box :=
  sound_of_literal_split component131Node24Box component131Node22Box component131Node23Box
    .chi (31/32) (by rfl) (by rfl)
    component131Node22_sound component131Node23_sound

private noncomputable def component131Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (15/16), chiHi := (31/32) }

set_option maxRecDepth 1000000 in
private theorem component131Node25_sound : Sound component131Node25Box :=
  sound_of_literal_split component131Node25Box leaf6545Box leaf6546Box
    .k (47/16) (by rfl) (by rfl)
    leaf6545FlatSound leaf6546FlatSound

private noncomputable def component131Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (31/32), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component131Node26_sound : Sound component131Node26Box :=
  sound_of_literal_split component131Node26Box leaf6547Box leaf6548Box
    .k (47/16) (by rfl) (by rfl)
    leaf6547FlatSound leaf6548FlatSound

private noncomputable def component131Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (15/16), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component131Node27_sound : Sound component131Node27Box :=
  sound_of_literal_split component131Node27Box component131Node25Box component131Node26Box
    .chi (31/32) (by rfl) (by rfl)
    component131Node25_sound component131Node26_sound

private noncomputable def component131Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (3), chiLo := (15/16), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component131Node28_sound : Sound component131Node28Box :=
  sound_of_literal_split component131Node28Box component131Node24Box component131Node27Box
    .k (23/8) (by rfl) (by rfl)
    component131Node24_sound component131Node27_sound

private noncomputable def component131Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (3), chiLo := (7/8), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component131Node29_sound : Sound component131Node29Box :=
  sound_of_literal_split component131Node29Box component131Node21Box component131Node28Box
    .chi (15/16) (by rfl) (by rfl)
    component131Node21_sound component131Node28_sound

noncomputable def component131Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (3), chiLo := (7/8), chiHi := (1) }

set_option maxRecDepth 1000000 in
theorem component131_sound : Sound component131Box :=
  sound_of_literal_split component131Box component131Node14Box component131Node29Box
    .k (11/4) (by rfl) (by rfl)
    component131Node14_sound component131Node29_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
