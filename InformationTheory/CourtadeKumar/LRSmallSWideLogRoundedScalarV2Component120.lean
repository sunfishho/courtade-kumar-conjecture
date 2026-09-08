import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch6
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch7
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch10
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch11
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

private noncomputable def leaf5973Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (13/32), chiHi := (105/256) }

private noncomputable def leaf5973Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871363/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712971776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1354677055/1073741824) }, upper := { exponent := 1, mantissa := (20897/16384) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi313LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429368317/137425943552) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf5973InnerLog : WideLogData :=
  innerPair293Data

set_option maxRecDepth 1000000 in
private theorem leaf5973LocalValidity :
    LeafFacts leaf5973Box leaf5973Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5973Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712971776) }) = true
      norm_num [leaf5973Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5973CertificateValid :
    WideCertificateValid leaf5973Box leaf5973Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi313ValidityFacts
    leaf5973LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5973CoverageChecked :
    coverageCheck (innerAD leaf5973Box) leaf5973InnerLog = true := by
  rfl'

private theorem leaf5973InnerLogValid :
    leaf5973InnerLog.Valid 8 (innerAD leaf5973Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint90PositiveFacts.valid leaf5973CoverageChecked

private noncomputable def leaf5973InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629499/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5973InputLogOnePlusV_eq :
    leaf5973InputLogOnePlusV = outerEnclosure 24
      (leaf5973Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5973RoundedFacts : LeafRoundedFacts 8
    leaf5973Certificate.logOnePlusV leaf5973InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5973InputLogOnePlusV_eq }

private noncomputable def leaf5973Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi313InputQChi innerPair293Input
    leaf5973InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5973LowerChecked :
    lowerCheck 24 leaf5973Box leaf5973Inputs = true := by
  rfl'

private theorem leaf5973CoversExact : CoversExact 8
    leaf5973Box leaf5973Certificate leaf5973InnerLog leaf5973Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi313RoundedFacts
    innerPair293RoundedFacts leaf5973RoundedFacts (by rfl)

private theorem leaf5973FlatSound : Sound leaf5973Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5973CertificateValid
    leaf5973InnerLogValid leaf5973CoversExact leaf5973LowerChecked

private noncomputable def leaf5974Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (105/256), chiHi := (53/128) }

private noncomputable def leaf5974Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871365/536870912) }, vSqrt := { lower := (8191/8192), upper := (310933921/310918144) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1362540893/1073741824) }, upper := { exponent := 1, mantissa := (10509/8192) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi314LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (621852065/621836288) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf5974InnerLog : WideLogData :=
  innerPair294Data

set_option maxRecDepth 1000000 in
private theorem leaf5974LocalValidity :
    LeafFacts leaf5974Box leaf5974Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5974Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (310933921/310918144) }) = true
      norm_num [leaf5974Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5974CertificateValid :
    WideCertificateValid leaf5974Box leaf5974Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi314ValidityFacts
    leaf5974LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5974CoverageChecked :
    coverageCheck (innerAD leaf5974Box) leaf5974InnerLog = true := by
  rfl'

private theorem leaf5974InnerLogValid :
    leaf5974InnerLog.Valid 8 (innerAD leaf5974Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint91PositiveFacts.valid leaf5974CoverageChecked

private noncomputable def leaf5974InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814753/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5974InputLogOnePlusV_eq :
    leaf5974InputLogOnePlusV = outerEnclosure 24
      (leaf5974Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5974RoundedFacts : LeafRoundedFacts 8
    leaf5974Certificate.logOnePlusV leaf5974InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5974InputLogOnePlusV_eq }

private noncomputable def leaf5974Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi314InputQChi innerPair294Input
    leaf5974InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5974LowerChecked :
    lowerCheck 24 leaf5974Box leaf5974Inputs = true := by
  rfl'

private theorem leaf5974CoversExact : CoversExact 8
    leaf5974Box leaf5974Certificate leaf5974InnerLog leaf5974Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi314RoundedFacts
    innerPair294RoundedFacts leaf5974RoundedFacts (by rfl)

private theorem leaf5974FlatSound : Sound leaf5974Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5974CertificateValid
    leaf5974InnerLogValid leaf5974CoversExact leaf5974LowerChecked

private noncomputable def leaf5975Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (13/32), chiHi := (105/256) }

private noncomputable def leaf5975Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871365/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712918016) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1361492381/1073741824) }, upper := { exponent := 1, mantissa := (10501/8192) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi313LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429314557/137425836032) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf5975InnerLog : WideLogData :=
  innerPair681Data

set_option maxRecDepth 1000000 in
private theorem leaf5975LocalValidity :
    LeafFacts leaf5975Box leaf5975Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5975Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712918016) }) = true
      norm_num [leaf5975Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5975CertificateValid :
    WideCertificateValid leaf5975Box leaf5975Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi313ValidityFacts
    leaf5975LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5975CoverageChecked :
    coverageCheck (innerAD leaf5975Box) leaf5975InnerLog = true := by
  rfl'

private theorem leaf5975InnerLogValid :
    leaf5975InnerLog.Valid 8 (innerAD leaf5975Box) :=
  wideLogDataValid_of_cachedCheck endpoint434PositiveFacts
    endpoint435PositiveFacts.valid leaf5975CoverageChecked

private noncomputable def leaf5975InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629505/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5975InputLogOnePlusV_eq :
    leaf5975InputLogOnePlusV = outerEnclosure 24
      (leaf5975Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5975RoundedFacts : LeafRoundedFacts 8
    leaf5975Certificate.logOnePlusV leaf5975InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5975InputLogOnePlusV_eq }

private noncomputable def leaf5975Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi313InputQChi innerPair681Input
    leaf5975InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5975LowerChecked :
    lowerCheck 24 leaf5975Box leaf5975Inputs = true := by
  rfl'

private theorem leaf5975CoversExact : CoversExact 8
    leaf5975Box leaf5975Certificate leaf5975InnerLog leaf5975Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi313RoundedFacts
    innerPair681RoundedFacts leaf5975RoundedFacts (by rfl)

private theorem leaf5975FlatSound : Sound leaf5975Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5975CertificateValid
    leaf5975InnerLogValid leaf5975CoversExact leaf5975LowerChecked

private noncomputable def leaf5976Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (105/256), chiHi := (53/128) }

private noncomputable def leaf5976Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871367/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712855552) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1369421751/1073741824) }, upper := { exponent := 1, mantissa := (5281/4096) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi314LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429252093/137425711104) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf5976InnerLog : WideLogData :=
  innerPair294Data

set_option maxRecDepth 1000000 in
private theorem leaf5976LocalValidity :
    LeafFacts leaf5976Box leaf5976Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5976Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712855552) }) = true
      norm_num [leaf5976Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5976CertificateValid :
    WideCertificateValid leaf5976Box leaf5976Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi314ValidityFacts
    leaf5976LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5976CoverageChecked :
    coverageCheck (innerAD leaf5976Box) leaf5976InnerLog = true := by
  rfl'

private theorem leaf5976InnerLogValid :
    leaf5976InnerLog.Valid 8 (innerAD leaf5976Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint91PositiveFacts.valid leaf5976CoverageChecked

private noncomputable def leaf5976InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629513/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5976InputLogOnePlusV_eq :
    leaf5976InputLogOnePlusV = outerEnclosure 24
      (leaf5976Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5976RoundedFacts : LeafRoundedFacts 8
    leaf5976Certificate.logOnePlusV leaf5976InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5976InputLogOnePlusV_eq }

private noncomputable def leaf5976Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi314InputQChi innerPair294Input
    leaf5976InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5976LowerChecked :
    lowerCheck 24 leaf5976Box leaf5976Inputs = true := by
  rfl'

private theorem leaf5976CoversExact : CoversExact 8
    leaf5976Box leaf5976Certificate leaf5976InnerLog leaf5976Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi314RoundedFacts
    innerPair294RoundedFacts leaf5976RoundedFacts (by rfl)

private theorem leaf5976FlatSound : Sound leaf5976Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5976CertificateValid
    leaf5976InnerLogValid leaf5976CoversExact leaf5976LowerChecked

private noncomputable def leaf5977Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (53/128), chiHi := (27/64) }

private noncomputable def leaf5977Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435805/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712785920) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (685185861/536870912) }, upper := { exponent := 1, mantissa := (5315/4096) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi264LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429182461/137425571840) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf5977InnerLog : WideLogData :=
  innerPair701Data

set_option maxRecDepth 1000000 in
private theorem leaf5977LocalValidity :
    LeafFacts leaf5977Box leaf5977Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5977Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712785920) }) = true
      norm_num [leaf5977Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5977CertificateValid :
    WideCertificateValid leaf5977Box leaf5977Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi264ValidityFacts
    leaf5977LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5977CoverageChecked :
    coverageCheck (innerAD leaf5977Box) leaf5977InnerLog = true := by
  rfl'

private theorem leaf5977InnerLogValid :
    leaf5977InnerLog.Valid 8 (innerAD leaf5977Box) :=
  wideLogDataValid_of_cachedCheck endpoint445PositiveFacts
    endpoint446PositiveFacts.valid leaf5977CoverageChecked

private noncomputable def leaf5977InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814761/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5977InputLogOnePlusV_eq :
    leaf5977InputLogOnePlusV = outerEnclosure 24
      (leaf5977Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5977RoundedFacts : LeafRoundedFacts 8
    leaf5977Certificate.logOnePlusV leaf5977InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5977InputLogOnePlusV_eq }

private noncomputable def leaf5977Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi264InputQChi innerPair701Input
    leaf5977InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5977LowerChecked :
    lowerCheck 24 leaf5977Box leaf5977Inputs = true := by
  rfl'

private theorem leaf5977CoversExact : CoversExact 8
    leaf5977Box leaf5977Certificate leaf5977InnerLog leaf5977Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi264RoundedFacts
    innerPair701RoundedFacts leaf5977RoundedFacts (by rfl)

private theorem leaf5977FlatSound : Sound leaf5977Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5977CertificateValid
    leaf5977InnerLogValid leaf5977CoversExact leaf5977LowerChecked

private noncomputable def leaf5978Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (53/128), chiHi := (27/64) }

private noncomputable def leaf5978Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435807/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712730624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (688659055/536870912) }, upper := { exponent := 1, mantissa := (2671/2048) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi264LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429127165/137425461248) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf5978InnerLog : WideLogData :=
  innerPair344Data

set_option maxRecDepth 1000000 in
private theorem leaf5978LocalValidity :
    LeafFacts leaf5978Box leaf5978Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5978Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712730624) }) = true
      norm_num [leaf5978Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5978CertificateValid :
    WideCertificateValid leaf5978Box leaf5978Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi264ValidityFacts
    leaf5978LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5978CoverageChecked :
    coverageCheck (innerAD leaf5978Box) leaf5978InnerLog = true := by
  rfl'

private theorem leaf5978InnerLogValid :
    leaf5978InnerLog.Valid 8 (innerAD leaf5978Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint444PositiveFacts.valid leaf5978CoverageChecked

private noncomputable def leaf5978InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453691/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5978InputLogOnePlusV_eq :
    leaf5978InputLogOnePlusV = outerEnclosure 24
      (leaf5978Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5978RoundedFacts : LeafRoundedFacts 8
    leaf5978Certificate.logOnePlusV leaf5978InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5978InputLogOnePlusV_eq }

private noncomputable def leaf5978Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi264InputQChi innerPair344Input
    leaf5978InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5978LowerChecked :
    lowerCheck 24 leaf5978Box leaf5978Inputs = true := by
  rfl'

private theorem leaf5978CoversExact : CoversExact 8
    leaf5978Box leaf5978Certificate leaf5978InnerLog leaf5978Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi264RoundedFacts
    innerPair344RoundedFacts leaf5978RoundedFacts (by rfl)

private theorem leaf5978FlatSound : Sound leaf5978Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5978CertificateValid
    leaf5978InnerLogValid leaf5978CoversExact leaf5978LowerChecked

private noncomputable def leaf5979Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (13/32), chiHi := (105/256) }

private noncomputable def leaf5979Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871367/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712864256) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1368307707/1073741824) }, upper := { exponent := 1, mantissa := (21107/16384) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi313LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429260797/137425728512) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf5979InnerLog : WideLogData :=
  innerPair294Data

set_option maxRecDepth 1000000 in
private theorem leaf5979LocalValidity :
    LeafFacts leaf5979Box leaf5979Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5979Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712864256) }) = true
      norm_num [leaf5979Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5979CertificateValid :
    WideCertificateValid leaf5979Box leaf5979Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi313ValidityFacts
    leaf5979LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5979CoverageChecked :
    coverageCheck (innerAD leaf5979Box) leaf5979InnerLog = true := by
  rfl'

private theorem leaf5979InnerLogValid :
    leaf5979InnerLog.Valid 8 (innerAD leaf5979Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint91PositiveFacts.valid leaf5979CoverageChecked

private noncomputable def leaf5979InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453689/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5979InputLogOnePlusV_eq :
    leaf5979InputLogOnePlusV = outerEnclosure 24
      (leaf5979Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5979RoundedFacts : LeafRoundedFacts 8
    leaf5979Certificate.logOnePlusV leaf5979InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5979InputLogOnePlusV_eq }

private noncomputable def leaf5979Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi313InputQChi innerPair294Input
    leaf5979InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5979LowerChecked :
    lowerCheck 24 leaf5979Box leaf5979Inputs = true := by
  rfl'

private theorem leaf5979CoversExact : CoversExact 8
    leaf5979Box leaf5979Certificate leaf5979InnerLog leaf5979Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi313RoundedFacts
    innerPair294RoundedFacts leaf5979RoundedFacts (by rfl)

private theorem leaf5979FlatSound : Sound leaf5979Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5979CertificateValid
    leaf5979InnerLogValid leaf5979CoversExact leaf5979LowerChecked

private noncomputable def leaf5980Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (105/256), chiHi := (53/128) }

private noncomputable def leaf5980Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871369/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712801280) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1376302609/1073741824) }, upper := { exponent := 1, mantissa := (10615/8192) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi314LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429197821/137425602560) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf5980InnerLog : WideLogData :=
  innerPair339Data

set_option maxRecDepth 1000000 in
private theorem leaf5980LocalValidity :
    LeafFacts leaf5980Box leaf5980Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5980Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712801280) }) = true
      norm_num [leaf5980Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5980CertificateValid :
    WideCertificateValid leaf5980Box leaf5980Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi314ValidityFacts
    leaf5980LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5980CoverageChecked :
    coverageCheck (innerAD leaf5980Box) leaf5980InnerLog = true := by
  rfl'

private theorem leaf5980InnerLogValid :
    leaf5980InnerLog.Valid 8 (innerAD leaf5980Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint91PositiveFacts.valid leaf5980CoverageChecked

private noncomputable def leaf5980InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726845/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf5980InputLogOnePlusV_eq :
    leaf5980InputLogOnePlusV = outerEnclosure 24
      (leaf5980Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5980RoundedFacts : LeafRoundedFacts 8
    leaf5980Certificate.logOnePlusV leaf5980InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5980InputLogOnePlusV_eq }

private noncomputable def leaf5980Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi314InputQChi innerPair339Input
    leaf5980InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5980LowerChecked :
    lowerCheck 24 leaf5980Box leaf5980Inputs = true := by
  rfl'

private theorem leaf5980CoversExact : CoversExact 8
    leaf5980Box leaf5980Certificate leaf5980InnerLog leaf5980Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi314RoundedFacts
    innerPair339RoundedFacts leaf5980RoundedFacts (by rfl)

private theorem leaf5980FlatSound : Sound leaf5980Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5980CertificateValid
    leaf5980InnerLogValid leaf5980CoversExact leaf5980LowerChecked

private noncomputable def leaf5981Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (13/32), chiHi := (105/256) }

private noncomputable def leaf5981Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871369/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712810496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1375123033/1073741824) }, upper := { exponent := 1, mantissa := (5303/4096) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi313LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429207037/137425620992) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf5981InnerLog : WideLogData :=
  innerPair294Data

set_option maxRecDepth 1000000 in
private theorem leaf5981LocalValidity :
    LeafFacts leaf5981Box leaf5981Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5981Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712810496) }) = true
      norm_num [leaf5981Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5981CertificateValid :
    WideCertificateValid leaf5981Box leaf5981Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi313ValidityFacts
    leaf5981LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5981CoverageChecked :
    coverageCheck (innerAD leaf5981Box) leaf5981InnerLog = true := by
  rfl'

private theorem leaf5981InnerLogValid :
    leaf5981InnerLog.Valid 8 (innerAD leaf5981Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint91PositiveFacts.valid leaf5981CoverageChecked

private noncomputable def leaf5981InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629519/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5981InputLogOnePlusV_eq :
    leaf5981InputLogOnePlusV = outerEnclosure 24
      (leaf5981Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5981RoundedFacts : LeafRoundedFacts 8
    leaf5981Certificate.logOnePlusV leaf5981InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5981InputLogOnePlusV_eq }

private noncomputable def leaf5981Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi313InputQChi innerPair294Input
    leaf5981InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5981LowerChecked :
    lowerCheck 24 leaf5981Box leaf5981Inputs = true := by
  rfl'

private theorem leaf5981CoversExact : CoversExact 8
    leaf5981Box leaf5981Certificate leaf5981InnerLog leaf5981Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi313RoundedFacts
    innerPair294RoundedFacts leaf5981RoundedFacts (by rfl)

private theorem leaf5981FlatSound : Sound leaf5981Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5981CertificateValid
    leaf5981InnerLogValid leaf5981CoversExact leaf5981LowerChecked

private noncomputable def leaf5982Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (105/256), chiHi := (53/128) }

private noncomputable def leaf5982Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871371/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712747008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1383183467/1073741824) }, upper := { exponent := 1, mantissa := (2667/2048) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi314LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429143549/137425494016) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf5982InnerLog : WideLogData :=
  innerPair339Data

set_option maxRecDepth 1000000 in
private theorem leaf5982LocalValidity :
    LeafFacts leaf5982Box leaf5982Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5982Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712747008) }) = true
      norm_num [leaf5982Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5982CertificateValid :
    WideCertificateValid leaf5982Box leaf5982Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi314ValidityFacts
    leaf5982LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5982CoverageChecked :
    coverageCheck (innerAD leaf5982Box) leaf5982InnerLog = true := by
  rfl'

private theorem leaf5982InnerLogValid :
    leaf5982InnerLog.Valid 8 (innerAD leaf5982Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint91PositiveFacts.valid leaf5982CoverageChecked

private noncomputable def leaf5982InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814763/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5982InputLogOnePlusV_eq :
    leaf5982InputLogOnePlusV = outerEnclosure 24
      (leaf5982Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5982RoundedFacts : LeafRoundedFacts 8
    leaf5982Certificate.logOnePlusV leaf5982InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5982InputLogOnePlusV_eq }

private noncomputable def leaf5982Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi314InputQChi innerPair339Input
    leaf5982InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5982LowerChecked :
    lowerCheck 24 leaf5982Box leaf5982Inputs = true := by
  rfl'

private theorem leaf5982CoversExact : CoversExact 8
    leaf5982Box leaf5982Certificate leaf5982InnerLog leaf5982Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi314RoundedFacts
    innerPair339RoundedFacts leaf5982RoundedFacts (by rfl)

private theorem leaf5982FlatSound : Sound leaf5982Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5982CertificateValid
    leaf5982InnerLogValid leaf5982CoversExact leaf5982LowerChecked

private noncomputable def leaf5983Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (53/128), chiHi := (107/256) }

private noncomputable def leaf5983Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871371/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712738304) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1384297511/1073741824) }, upper := { exponent := 1, mantissa := (21353/16384) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi315LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429134845/137425476608) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf5983InnerLog : WideLogData :=
  innerPair339Data

set_option maxRecDepth 1000000 in
private theorem leaf5983LocalValidity :
    LeafFacts leaf5983Box leaf5983Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5983Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712738304) }) = true
      norm_num [leaf5983Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5983CertificateValid :
    WideCertificateValid leaf5983Box leaf5983Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi315ValidityFacts
    leaf5983LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5983CoverageChecked :
    coverageCheck (innerAD leaf5983Box) leaf5983InnerLog = true := by
  rfl'

private theorem leaf5983InnerLogValid :
    leaf5983InnerLog.Valid 8 (innerAD leaf5983Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint91PositiveFacts.valid leaf5983CoverageChecked

private noncomputable def leaf5983InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629527/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5983InputLogOnePlusV_eq :
    leaf5983InputLogOnePlusV = outerEnclosure 24
      (leaf5983Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5983RoundedFacts : LeafRoundedFacts 8
    leaf5983Certificate.logOnePlusV leaf5983InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5983InputLogOnePlusV_eq }

private noncomputable def leaf5983Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi315InputQChi innerPair339Input
    leaf5983InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5983LowerChecked :
    lowerCheck 24 leaf5983Box leaf5983Inputs = true := by
  rfl'

private theorem leaf5983CoversExact : CoversExact 8
    leaf5983Box leaf5983Certificate leaf5983InnerLog leaf5983Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi315RoundedFacts
    innerPair339RoundedFacts leaf5983RoundedFacts (by rfl)

private theorem leaf5983FlatSound : Sound leaf5983Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5983CertificateValid
    leaf5983InnerLogValid leaf5983CoversExact leaf5983LowerChecked

private noncomputable def leaf5984Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (107/256), chiHi := (27/64) }

private noncomputable def leaf5984Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871373/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712675328) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1392292413/1073741824) }, upper := { exponent := 1, mantissa := (5369/4096) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi316LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429071869/137425350656) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf5984InnerLog : WideLogData :=
  innerPair339Data

set_option maxRecDepth 1000000 in
private theorem leaf5984LocalValidity :
    LeafFacts leaf5984Box leaf5984Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5984Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712675328) }) = true
      norm_num [leaf5984Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5984CertificateValid :
    WideCertificateValid leaf5984Box leaf5984Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi316ValidityFacts
    leaf5984LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5984CoverageChecked :
    coverageCheck (innerAD leaf5984Box) leaf5984InnerLog = true := by
  rfl'

private theorem leaf5984InnerLogValid :
    leaf5984InnerLog.Valid 8 (innerAD leaf5984Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint91PositiveFacts.valid leaf5984CoverageChecked

private noncomputable def leaf5984InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629535/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5984InputLogOnePlusV_eq :
    leaf5984InputLogOnePlusV = outerEnclosure 24
      (leaf5984Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5984RoundedFacts : LeafRoundedFacts 8
    leaf5984Certificate.logOnePlusV leaf5984InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5984InputLogOnePlusV_eq }

private noncomputable def leaf5984Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi316InputQChi innerPair339Input
    leaf5984InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5984LowerChecked :
    lowerCheck 24 leaf5984Box leaf5984Inputs = true := by
  rfl'

private theorem leaf5984CoversExact : CoversExact 8
    leaf5984Box leaf5984Certificate leaf5984InnerLog leaf5984Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi316RoundedFacts
    innerPair339RoundedFacts leaf5984RoundedFacts (by rfl)

private theorem leaf5984FlatSound : Sound leaf5984Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5984CertificateValid
    leaf5984InnerLogValid leaf5984CoversExact leaf5984LowerChecked

private noncomputable def leaf5985Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (53/128), chiHi := (107/256) }

private noncomputable def leaf5985Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871373/536870912) }, vSqrt := { lower := (8191/8192), upper := (310933921/310917120) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1391243901/1073741824) }, upper := { exponent := 1, mantissa := (5365/4096) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi315LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (621851041/621834240) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf5985InnerLog : WideLogData :=
  innerPair339Data

set_option maxRecDepth 1000000 in
private theorem leaf5985LocalValidity :
    LeafFacts leaf5985Box leaf5985Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5985Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (310933921/310917120) }) = true
      norm_num [leaf5985Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5985CertificateValid :
    WideCertificateValid leaf5985Box leaf5985Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi315ValidityFacts
    leaf5985LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5985CoverageChecked :
    coverageCheck (innerAD leaf5985Box) leaf5985InnerLog = true := by
  rfl'

private theorem leaf5985InnerLogValid :
    leaf5985InnerLog.Valid 8 (innerAD leaf5985Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint91PositiveFacts.valid leaf5985CoverageChecked

private noncomputable def leaf5985InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814767/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5985InputLogOnePlusV_eq :
    leaf5985InputLogOnePlusV = outerEnclosure 24
      (leaf5985Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5985RoundedFacts : LeafRoundedFacts 8
    leaf5985Certificate.logOnePlusV leaf5985InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5985InputLogOnePlusV_eq }

private noncomputable def leaf5985Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi315InputQChi innerPair339Input
    leaf5985InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5985LowerChecked :
    lowerCheck 24 leaf5985Box leaf5985Inputs = true := by
  rfl'

private theorem leaf5985CoversExact : CoversExact 8
    leaf5985Box leaf5985Certificate leaf5985InnerLog leaf5985Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi315RoundedFacts
    innerPair339RoundedFacts leaf5985RoundedFacts (by rfl)

private theorem leaf5985FlatSound : Sound leaf5985Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5985CertificateValid
    leaf5985InnerLogValid leaf5985CoversExact leaf5985LowerChecked

private noncomputable def leaf5986Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (107/256), chiHi := (27/64) }

private noncomputable def leaf5986Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871375/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712620032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1399304335/1073741824) }, upper := { exponent := 1, mantissa := (1349/1024) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi316LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429016573/137425240064) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf5986InnerLog : WideLogData :=
  innerPair340Data

set_option maxRecDepth 1000000 in
private theorem leaf5986LocalValidity :
    LeafFacts leaf5986Box leaf5986Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5986Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712620032) }) = true
      norm_num [leaf5986Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5986CertificateValid :
    WideCertificateValid leaf5986Box leaf5986Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi316ValidityFacts
    leaf5986LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5986CoverageChecked :
    coverageCheck (innerAD leaf5986Box) leaf5986InnerLog = true := by
  rfl'

private theorem leaf5986InnerLogValid :
    leaf5986InnerLog.Valid 8 (innerAD leaf5986Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint92PositiveFacts.valid leaf5986CoverageChecked

private noncomputable def leaf5986InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814771/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5986InputLogOnePlusV_eq :
    leaf5986InputLogOnePlusV = outerEnclosure 24
      (leaf5986Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5986RoundedFacts : LeafRoundedFacts 8
    leaf5986Certificate.logOnePlusV leaf5986InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5986InputLogOnePlusV_eq }

private noncomputable def leaf5986Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi316InputQChi innerPair340Input
    leaf5986InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5986LowerChecked :
    lowerCheck 24 leaf5986Box leaf5986Inputs = true := by
  rfl'

private theorem leaf5986CoversExact : CoversExact 8
    leaf5986Box leaf5986Certificate leaf5986InnerLog leaf5986Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi316RoundedFacts
    innerPair340RoundedFacts leaf5986RoundedFacts (by rfl)

private theorem leaf5986FlatSound : Sound leaf5986Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5986CertificateValid
    leaf5986InnerLogValid leaf5986CoversExact leaf5986LowerChecked

private noncomputable def leaf5987Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (27/64), chiHi := (55/128) }

private noncomputable def leaf5987Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435807/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712662016) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (693049699/536870912) }, upper := { exponent := 1, mantissa := (10751/8192) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi265LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429058557/137425324032) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf5987InnerLog : WideLogData :=
  innerPair339Data

set_option maxRecDepth 1000000 in
private theorem leaf5987LocalValidity :
    LeafFacts leaf5987Box leaf5987Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5987Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712662016) }) = true
      norm_num [leaf5987Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5987CertificateValid :
    WideCertificateValid leaf5987Box leaf5987Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi265ValidityFacts
    leaf5987LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5987CoverageChecked :
    coverageCheck (innerAD leaf5987Box) leaf5987InnerLog = true := by
  rfl'

private theorem leaf5987InnerLogValid :
    leaf5987InnerLog.Valid 8 (innerAD leaf5987Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint91PositiveFacts.valid leaf5987CoverageChecked

private noncomputable def leaf5987InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629537/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5987InputLogOnePlusV_eq :
    leaf5987InputLogOnePlusV = outerEnclosure 24
      (leaf5987Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5987RoundedFacts : LeafRoundedFacts 8
    leaf5987Certificate.logOnePlusV leaf5987InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5987InputLogOnePlusV_eq }

private noncomputable def leaf5987Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi265InputQChi innerPair339Input
    leaf5987InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5987LowerChecked :
    lowerCheck 24 leaf5987Box leaf5987Inputs = true := by
  rfl'

private theorem leaf5987CoversExact : CoversExact 8
    leaf5987Box leaf5987Certificate leaf5987InnerLog leaf5987Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi265RoundedFacts
    innerPair339RoundedFacts leaf5987RoundedFacts (by rfl)

private theorem leaf5987FlatSound : Sound leaf5987Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5987CertificateValid
    leaf5987InnerLogValid leaf5987CoversExact leaf5987LowerChecked

private noncomputable def leaf5988Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (27/64), chiHi := (55/128) }

private noncomputable def leaf5988Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435809/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712605696) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (696588425/536870912) }, upper := { exponent := 1, mantissa := (5403/4096) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi265LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429002237/137425211392) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf5988InnerLog : WideLogData :=
  innerPair688Data

set_option maxRecDepth 1000000 in
private theorem leaf5988LocalValidity :
    LeafFacts leaf5988Box leaf5988Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5988Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712605696) }) = true
      norm_num [leaf5988Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5988CertificateValid :
    WideCertificateValid leaf5988Box leaf5988Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi265ValidityFacts
    leaf5988LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5988CoverageChecked :
    coverageCheck (innerAD leaf5988Box) leaf5988InnerLog = true := by
  rfl'

private theorem leaf5988InnerLogValid :
    leaf5988InnerLog.Valid 8 (innerAD leaf5988Box) :=
  wideLogDataValid_of_cachedCheck endpoint436PositiveFacts
    endpoint95PositiveFacts.valid leaf5988CoverageChecked

private noncomputable def leaf5988InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453693/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5988InputLogOnePlusV_eq :
    leaf5988InputLogOnePlusV = outerEnclosure 24
      (leaf5988Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5988RoundedFacts : LeafRoundedFacts 8
    leaf5988Certificate.logOnePlusV leaf5988InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5988InputLogOnePlusV_eq }

private noncomputable def leaf5988Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi265InputQChi innerPair688Input
    leaf5988InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5988LowerChecked :
    lowerCheck 24 leaf5988Box leaf5988Inputs = true := by
  rfl'

private theorem leaf5988CoversExact : CoversExact 8
    leaf5988Box leaf5988Certificate leaf5988InnerLog leaf5988Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi265RoundedFacts
    innerPair688RoundedFacts leaf5988RoundedFacts (by rfl)

private theorem leaf5988FlatSound : Sound leaf5988Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5988CertificateValid
    leaf5988InnerLogValid leaf5988CoversExact leaf5988LowerChecked

private noncomputable def leaf5989Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (55/128), chiHi := (7/16) }

private noncomputable def leaf5989Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435809/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712538112) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (700913537/536870912) }, upper := { exponent := 1, mantissa := (1359/1024) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi266LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428934653/137425076224) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf5989InnerLog : WideLogData :=
  innerPair699Data

set_option maxRecDepth 1000000 in
private theorem leaf5989LocalValidity :
    LeafFacts leaf5989Box leaf5989Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5989Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712538112) }) = true
      norm_num [leaf5989Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5989CertificateValid :
    WideCertificateValid leaf5989Box leaf5989Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi266ValidityFacts
    leaf5989LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5989CoverageChecked :
    coverageCheck (innerAD leaf5989Box) leaf5989InnerLog = true := by
  rfl'

private theorem leaf5989InnerLogValid :
    leaf5989InnerLog.Valid 8 (innerAD leaf5989Box) :=
  wideLogDataValid_of_cachedCheck endpoint444PositiveFacts
    endpoint447PositiveFacts.valid leaf5989CoverageChecked

private noncomputable def leaf5989InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726847/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf5989InputLogOnePlusV_eq :
    leaf5989InputLogOnePlusV = outerEnclosure 24
      (leaf5989Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5989RoundedFacts : LeafRoundedFacts 8
    leaf5989Certificate.logOnePlusV leaf5989InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5989InputLogOnePlusV_eq }

private noncomputable def leaf5989Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi266InputQChi innerPair699Input
    leaf5989InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5989LowerChecked :
    lowerCheck 24 leaf5989Box leaf5989Inputs = true := by
  rfl'

private theorem leaf5989CoversExact : CoversExact 8
    leaf5989Box leaf5989Certificate leaf5989InnerLog leaf5989Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi266RoundedFacts
    innerPair699RoundedFacts leaf5989RoundedFacts (by rfl)

private theorem leaf5989FlatSound : Sound leaf5989Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5989CertificateValid
    leaf5989InnerLogValid leaf5989CoversExact leaf5989LowerChecked

private noncomputable def leaf5990Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (55/128), chiHi := (7/16) }

private noncomputable def leaf5990Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435811/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712480768) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (704517795/536870912) }, upper := { exponent := 1, mantissa := (683/512) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi266LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428877309/137424961536) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf5990InnerLog : WideLogData :=
  innerPair700Data

set_option maxRecDepth 1000000 in
private theorem leaf5990LocalValidity :
    LeafFacts leaf5990Box leaf5990Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5990Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712480768) }) = true
      norm_num [leaf5990Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5990CertificateValid :
    WideCertificateValid leaf5990Box leaf5990Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi266ValidityFacts
    leaf5990LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5990CoverageChecked :
    coverageCheck (innerAD leaf5990Box) leaf5990InnerLog = true := by
  rfl'

private theorem leaf5990InnerLogValid :
    leaf5990InnerLog.Valid 8 (innerAD leaf5990Box) :=
  wideLogDataValid_of_cachedCheck endpoint444PositiveFacts
    endpoint448PositiveFacts.valid leaf5990CoverageChecked

private noncomputable def leaf5990InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629559/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5990InputLogOnePlusV_eq :
    leaf5990InputLogOnePlusV = outerEnclosure 24
      (leaf5990Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5990RoundedFacts : LeafRoundedFacts 8
    leaf5990Certificate.logOnePlusV leaf5990InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5990InputLogOnePlusV_eq }

private noncomputable def leaf5990Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi266InputQChi innerPair700Input
    leaf5990InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5990LowerChecked :
    lowerCheck 24 leaf5990Box leaf5990Inputs = true := by
  rfl'

private theorem leaf5990CoversExact : CoversExact 8
    leaf5990Box leaf5990Certificate leaf5990InnerLog leaf5990Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi266RoundedFacts
    innerPair700RoundedFacts leaf5990RoundedFacts (by rfl)

private theorem leaf5990FlatSound : Sound leaf5990Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5990CertificateValid
    leaf5990InnerLogValid leaf5990CoversExact leaf5990LowerChecked

private noncomputable def leaf5991Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (27/64), chiHi := (55/128) }

private noncomputable def leaf5991Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435811/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712549376) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (700127151/536870912) }, upper := { exponent := 1, mantissa := (10861/8192) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi265LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428945917/137425098752) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf5991InnerLog : WideLogData :=
  innerPair689Data

set_option maxRecDepth 1000000 in
private theorem leaf5991LocalValidity :
    LeafFacts leaf5991Box leaf5991Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5991Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712549376) }) = true
      norm_num [leaf5991Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5991CertificateValid :
    WideCertificateValid leaf5991Box leaf5991Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi265ValidityFacts
    leaf5991LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5991CoverageChecked :
    coverageCheck (innerAD leaf5991Box) leaf5991InnerLog = true := by
  rfl'

private theorem leaf5991InnerLogValid :
    leaf5991InnerLog.Valid 8 (innerAD leaf5991Box) :=
  wideLogDataValid_of_cachedCheck endpoint436PositiveFacts
    endpoint447PositiveFacts.valid leaf5991CoverageChecked

private noncomputable def leaf5991InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814775/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5991InputLogOnePlusV_eq :
    leaf5991InputLogOnePlusV = outerEnclosure 24
      (leaf5991Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5991RoundedFacts : LeafRoundedFacts 8
    leaf5991Certificate.logOnePlusV leaf5991InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5991InputLogOnePlusV_eq }

private noncomputable def leaf5991Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi265InputQChi innerPair689Input
    leaf5991InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5991LowerChecked :
    lowerCheck 24 leaf5991Box leaf5991Inputs = true := by
  rfl'

private theorem leaf5991CoversExact : CoversExact 8
    leaf5991Box leaf5991Certificate leaf5991InnerLog leaf5991Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi265RoundedFacts
    innerPair689RoundedFacts leaf5991RoundedFacts (by rfl)

private theorem leaf5991FlatSound : Sound leaf5991Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5991CertificateValid
    leaf5991InnerLogValid leaf5991CoversExact leaf5991LowerChecked

private noncomputable def leaf5992Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (27/64), chiHi := (55/128) }

private noncomputable def leaf5992Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435813/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712493056) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (703665877/536870912) }, upper := { exponent := 1, mantissa := (2729/2048) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi265LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428889597/137424986112) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf5992InnerLog : WideLogData :=
  innerPair707Data

set_option maxRecDepth 1000000 in
private theorem leaf5992LocalValidity :
    LeafFacts leaf5992Box leaf5992Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5992Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712493056) }) = true
      norm_num [leaf5992Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5992CertificateValid :
    WideCertificateValid leaf5992Box leaf5992Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi265ValidityFacts
    leaf5992LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5992CoverageChecked :
    coverageCheck (innerAD leaf5992Box) leaf5992InnerLog = true := by
  rfl'

private theorem leaf5992InnerLogValid :
    leaf5992InnerLog.Valid 8 (innerAD leaf5992Box) :=
  wideLogDataValid_of_cachedCheck endpoint449PositiveFacts
    endpoint450PositiveFacts.valid leaf5992CoverageChecked

private noncomputable def leaf5992InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629557/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5992InputLogOnePlusV_eq :
    leaf5992InputLogOnePlusV = outerEnclosure 24
      (leaf5992Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5992RoundedFacts : LeafRoundedFacts 8
    leaf5992Certificate.logOnePlusV leaf5992InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5992InputLogOnePlusV_eq }

private noncomputable def leaf5992Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi265InputQChi innerPair707Input
    leaf5992InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5992LowerChecked :
    lowerCheck 24 leaf5992Box leaf5992Inputs = true := by
  rfl'

private theorem leaf5992CoversExact : CoversExact 8
    leaf5992Box leaf5992Certificate leaf5992InnerLog leaf5992Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi265RoundedFacts
    innerPair707RoundedFacts leaf5992RoundedFacts (by rfl)

private theorem leaf5992FlatSound : Sound leaf5992Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5992CertificateValid
    leaf5992InnerLogValid leaf5992CoversExact leaf5992LowerChecked

private noncomputable def leaf5993Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (55/128), chiHi := (7/16) }

private noncomputable def leaf5993Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435813/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712423424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (708122053/536870912) }, upper := { exponent := 1, mantissa := (1373/1024) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi266LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428819965/137424846848) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf5993InnerLog : WideLogData :=
  innerPair345Data

set_option maxRecDepth 1000000 in
private theorem leaf5993LocalValidity :
    LeafFacts leaf5993Box leaf5993Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5993Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712423424) }) = true
      norm_num [leaf5993Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5993CertificateValid :
    WideCertificateValid leaf5993Box leaf5993Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi266ValidityFacts
    leaf5993LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5993CoverageChecked :
    coverageCheck (innerAD leaf5993Box) leaf5993InnerLog = true := by
  rfl'

private theorem leaf5993InnerLogValid :
    leaf5993InnerLog.Valid 8 (innerAD leaf5993Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint92PositiveFacts.valid leaf5993CoverageChecked

private noncomputable def leaf5993InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814783/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5993InputLogOnePlusV_eq :
    leaf5993InputLogOnePlusV = outerEnclosure 24
      (leaf5993Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5993RoundedFacts : LeafRoundedFacts 8
    leaf5993Certificate.logOnePlusV leaf5993InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5993InputLogOnePlusV_eq }

private noncomputable def leaf5993Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi266InputQChi innerPair345Input
    leaf5993InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5993LowerChecked :
    lowerCheck 24 leaf5993Box leaf5993Inputs = true := by
  rfl'

private theorem leaf5993CoversExact : CoversExact 8
    leaf5993Box leaf5993Certificate leaf5993InnerLog leaf5993Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi266RoundedFacts
    innerPair345RoundedFacts leaf5993RoundedFacts (by rfl)

private theorem leaf5993FlatSound : Sound leaf5993Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5993CertificateValid
    leaf5993InnerLogValid leaf5993CoversExact leaf5993LowerChecked

private noncomputable def leaf5994Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (55/128), chiHi := (7/16) }

private noncomputable def leaf5994Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435815/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712366080) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (711726311/536870912) }, upper := { exponent := 1, mantissa := (345/256) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi266LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428762621/137424732160) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf5994InnerLog : WideLogData :=
  innerPair365Data

set_option maxRecDepth 1000000 in
private theorem leaf5994LocalValidity :
    LeafFacts leaf5994Box leaf5994Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5994Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712366080) }) = true
      norm_num [leaf5994Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5994CertificateValid :
    WideCertificateValid leaf5994Box leaf5994Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi266ValidityFacts
    leaf5994LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5994CoverageChecked :
    coverageCheck (innerAD leaf5994Box) leaf5994InnerLog = true := by
  rfl'

private theorem leaf5994InnerLogValid :
    leaf5994InnerLog.Valid 8 (innerAD leaf5994Box) :=
  wideLogDataValid_of_cachedCheck endpoint95PositiveFacts
    endpoint451PositiveFacts.valid leaf5994CoverageChecked

private noncomputable def leaf5994InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629573/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5994InputLogOnePlusV_eq :
    leaf5994InputLogOnePlusV = outerEnclosure 24
      (leaf5994Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5994RoundedFacts : LeafRoundedFacts 8
    leaf5994Certificate.logOnePlusV leaf5994InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5994InputLogOnePlusV_eq }

private noncomputable def leaf5994Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi266InputQChi innerPair365Input
    leaf5994InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5994LowerChecked :
    lowerCheck 24 leaf5994Box leaf5994Inputs = true := by
  rfl'

private theorem leaf5994CoversExact : CoversExact 8
    leaf5994Box leaf5994Certificate leaf5994InnerLog leaf5994Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi266RoundedFacts
    innerPair365RoundedFacts leaf5994RoundedFacts (by rfl)

private theorem leaf5994FlatSound : Sound leaf5994Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5994CertificateValid
    leaf5994InnerLogValid leaf5994CoversExact leaf5994LowerChecked

private noncomputable def leaf5995Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (13/32), chiHi := (105/256) }

private noncomputable def leaf5995Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871371/536870912) }, vSqrt := { lower := (8191/8192), upper := (5285876657/5285596672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1381938359/1073741824) }, upper := { exponent := 1, mantissa := (21317/16384) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi313LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (10571473329/10571193344) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf5995InnerLog : WideLogData :=
  innerPair339Data

set_option maxRecDepth 1000000 in
private theorem leaf5995LocalValidity :
    LeafFacts leaf5995Box leaf5995Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5995Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5285876657/5285596672) }) = true
      norm_num [leaf5995Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5995CertificateValid :
    WideCertificateValid leaf5995Box leaf5995Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi313ValidityFacts
    leaf5995LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5995CoverageChecked :
    coverageCheck (innerAD leaf5995Box) leaf5995InnerLog = true := by
  rfl'

private theorem leaf5995InnerLogValid :
    leaf5995InnerLog.Valid 8 (innerAD leaf5995Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint91PositiveFacts.valid leaf5995CoverageChecked

private noncomputable def leaf5995InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629525/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5995InputLogOnePlusV_eq :
    leaf5995InputLogOnePlusV = outerEnclosure 24
      (leaf5995Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5995RoundedFacts : LeafRoundedFacts 8
    leaf5995Certificate.logOnePlusV leaf5995InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5995InputLogOnePlusV_eq }

private noncomputable def leaf5995Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi313InputQChi innerPair339Input
    leaf5995InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5995LowerChecked :
    lowerCheck 24 leaf5995Box leaf5995Inputs = true := by
  rfl'

private theorem leaf5995CoversExact : CoversExact 8
    leaf5995Box leaf5995Certificate leaf5995InnerLog leaf5995Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi313RoundedFacts
    innerPair339RoundedFacts leaf5995RoundedFacts (by rfl)

private theorem leaf5995FlatSound : Sound leaf5995Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5995CertificateValid
    leaf5995InnerLogValid leaf5995CoversExact leaf5995LowerChecked

private noncomputable def leaf5996Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (105/256), chiHi := (53/128) }

private noncomputable def leaf5996Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871373/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712692736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1390064325/1073741824) }, upper := { exponent := 1, mantissa := (10721/8192) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi314LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429089277/137425385472) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf5996InnerLog : WideLogData :=
  innerPair339Data

set_option maxRecDepth 1000000 in
private theorem leaf5996LocalValidity :
    LeafFacts leaf5996Box leaf5996Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5996Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712692736) }) = true
      norm_num [leaf5996Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5996CertificateValid :
    WideCertificateValid leaf5996Box leaf5996Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi314ValidityFacts
    leaf5996LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5996CoverageChecked :
    coverageCheck (innerAD leaf5996Box) leaf5996InnerLog = true := by
  rfl'

private theorem leaf5996InnerLogValid :
    leaf5996InnerLog.Valid 8 (innerAD leaf5996Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint91PositiveFacts.valid leaf5996CoverageChecked

private noncomputable def leaf5996InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629533/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5996InputLogOnePlusV_eq :
    leaf5996InputLogOnePlusV = outerEnclosure 24
      (leaf5996Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5996RoundedFacts : LeafRoundedFacts 8
    leaf5996Certificate.logOnePlusV leaf5996InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5996InputLogOnePlusV_eq }

private noncomputable def leaf5996Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi314InputQChi innerPair339Input
    leaf5996InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5996LowerChecked :
    lowerCheck 24 leaf5996Box leaf5996Inputs = true := by
  rfl'

private theorem leaf5996CoversExact : CoversExact 8
    leaf5996Box leaf5996Certificate leaf5996InnerLog leaf5996Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi314RoundedFacts
    innerPair339RoundedFacts leaf5996RoundedFacts (by rfl)

private theorem leaf5996FlatSound : Sound leaf5996Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5996CertificateValid
    leaf5996InnerLogValid leaf5996CoversExact leaf5996LowerChecked

private noncomputable def leaf5997Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (13/32), chiHi := (105/256) }

private noncomputable def leaf5997Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871373/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712702976) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1388753685/1073741824) }, upper := { exponent := 1, mantissa := (10711/8192) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi313LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429099517/137425405952) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf5997InnerLog : WideLogData :=
  innerPair339Data

set_option maxRecDepth 1000000 in
private theorem leaf5997LocalValidity :
    LeafFacts leaf5997Box leaf5997Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5997Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712702976) }) = true
      norm_num [leaf5997Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5997CertificateValid :
    WideCertificateValid leaf5997Box leaf5997Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi313ValidityFacts
    leaf5997LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5997CoverageChecked :
    coverageCheck (innerAD leaf5997Box) leaf5997InnerLog = true := by
  rfl'

private theorem leaf5997InnerLogValid :
    leaf5997InnerLog.Valid 8 (innerAD leaf5997Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint91PositiveFacts.valid leaf5997CoverageChecked

private noncomputable def leaf5997InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907383/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5997InputLogOnePlusV_eq :
    leaf5997InputLogOnePlusV = outerEnclosure 24
      (leaf5997Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5997RoundedFacts : LeafRoundedFacts 8
    leaf5997Certificate.logOnePlusV leaf5997InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5997InputLogOnePlusV_eq }

private noncomputable def leaf5997Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi313InputQChi innerPair339Input
    leaf5997InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5997LowerChecked :
    lowerCheck 24 leaf5997Box leaf5997Inputs = true := by
  rfl'

private theorem leaf5997CoversExact : CoversExact 8
    leaf5997Box leaf5997Certificate leaf5997InnerLog leaf5997Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi313RoundedFacts
    innerPair339RoundedFacts leaf5997RoundedFacts (by rfl)

private theorem leaf5997FlatSound : Sound leaf5997Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5997CertificateValid
    leaf5997InnerLogValid leaf5997CoversExact leaf5997LowerChecked

private noncomputable def leaf5998Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (105/256), chiHi := (53/128) }

private noncomputable def leaf5998Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871375/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712638464) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1396945183/1073741824) }, upper := { exponent := 1, mantissa := (5387/4096) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi314LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429035005/137425276928) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf5998InnerLog : WideLogData :=
  innerPair688Data

set_option maxRecDepth 1000000 in
private theorem leaf5998LocalValidity :
    LeafFacts leaf5998Box leaf5998Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5998Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712638464) }) = true
      norm_num [leaf5998Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5998CertificateValid :
    WideCertificateValid leaf5998Box leaf5998Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi314ValidityFacts
    leaf5998LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5998CoverageChecked :
    coverageCheck (innerAD leaf5998Box) leaf5998InnerLog = true := by
  rfl'

private theorem leaf5998InnerLogValid :
    leaf5998InnerLog.Valid 8 (innerAD leaf5998Box) :=
  wideLogDataValid_of_cachedCheck endpoint436PositiveFacts
    endpoint95PositiveFacts.valid leaf5998CoverageChecked

private noncomputable def leaf5998InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907385/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5998InputLogOnePlusV_eq :
    leaf5998InputLogOnePlusV = outerEnclosure 24
      (leaf5998Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5998RoundedFacts : LeafRoundedFacts 8
    leaf5998Certificate.logOnePlusV leaf5998InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5998InputLogOnePlusV_eq }

private noncomputable def leaf5998Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi314InputQChi innerPair688Input
    leaf5998InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5998LowerChecked :
    lowerCheck 24 leaf5998Box leaf5998Inputs = true := by
  rfl'

private theorem leaf5998CoversExact : CoversExact 8
    leaf5998Box leaf5998Certificate leaf5998InnerLog leaf5998Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi314RoundedFacts
    innerPair688RoundedFacts leaf5998RoundedFacts (by rfl)

private theorem leaf5998FlatSound : Sound leaf5998Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5998CertificateValid
    leaf5998InnerLogValid leaf5998CoversExact leaf5998LowerChecked

private noncomputable def leaf5999Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (53/128), chiHi := (107/256) }

private noncomputable def leaf5999Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871375/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712628736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1398190291/1073741824) }, upper := { exponent := 1, mantissa := (21567/16384) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi315LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429025277/137425257472) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf5999InnerLog : WideLogData :=
  innerPair340Data

set_option maxRecDepth 1000000 in
private theorem leaf5999LocalValidity :
    LeafFacts leaf5999Box leaf5999Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5999Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712628736) }) = true
      norm_num [leaf5999Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5999CertificateValid :
    WideCertificateValid leaf5999Box leaf5999Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi315ValidityFacts
    leaf5999LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5999CoverageChecked :
    coverageCheck (innerAD leaf5999Box) leaf5999InnerLog = true := by
  rfl'

private theorem leaf5999InnerLogValid :
    leaf5999InnerLog.Valid 8 (innerAD leaf5999Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint92PositiveFacts.valid leaf5999CoverageChecked

private noncomputable def leaf5999InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629541/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5999InputLogOnePlusV_eq :
    leaf5999InputLogOnePlusV = outerEnclosure 24
      (leaf5999Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5999RoundedFacts : LeafRoundedFacts 8
    leaf5999Certificate.logOnePlusV leaf5999InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5999InputLogOnePlusV_eq }

private noncomputable def leaf5999Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi315InputQChi innerPair340Input
    leaf5999InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5999LowerChecked :
    lowerCheck 24 leaf5999Box leaf5999Inputs = true := by
  rfl'

private theorem leaf5999CoversExact : CoversExact 8
    leaf5999Box leaf5999Certificate leaf5999InnerLog leaf5999Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi315RoundedFacts
    innerPair340RoundedFacts leaf5999RoundedFacts (by rfl)

private theorem leaf5999FlatSound : Sound leaf5999Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5999CertificateValid
    leaf5999InnerLogValid leaf5999CoversExact leaf5999LowerChecked

private noncomputable def leaf6000Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (107/256), chiHi := (27/64) }

private noncomputable def leaf6000Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871377/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712564736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1406316257/1073741824) }, upper := { exponent := 1, mantissa := (5423/4096) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi316LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428961277/137425129472) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf6000InnerLog : WideLogData :=
  innerPair340Data

set_option maxRecDepth 1000000 in
private theorem leaf6000LocalValidity :
    LeafFacts leaf6000Box leaf6000Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6000Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712564736) }) = true
      norm_num [leaf6000Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6000CertificateValid :
    WideCertificateValid leaf6000Box leaf6000Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi316ValidityFacts
    leaf6000LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6000CoverageChecked :
    coverageCheck (innerAD leaf6000Box) leaf6000InnerLog = true := by
  rfl'

private theorem leaf6000InnerLogValid :
    leaf6000InnerLog.Valid 8 (innerAD leaf6000Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint92PositiveFacts.valid leaf6000CoverageChecked

private noncomputable def leaf6000InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629549/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6000InputLogOnePlusV_eq :
    leaf6000InputLogOnePlusV = outerEnclosure 24
      (leaf6000Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6000RoundedFacts : LeafRoundedFacts 8
    leaf6000Certificate.logOnePlusV leaf6000InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6000InputLogOnePlusV_eq }

private noncomputable def leaf6000Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi316InputQChi innerPair340Input
    leaf6000InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6000LowerChecked :
    lowerCheck 24 leaf6000Box leaf6000Inputs = true := by
  rfl'

private theorem leaf6000CoversExact : CoversExact 8
    leaf6000Box leaf6000Certificate leaf6000InnerLog leaf6000Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi316RoundedFacts
    innerPair340RoundedFacts leaf6000RoundedFacts (by rfl)

private theorem leaf6000FlatSound : Sound leaf6000Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6000CertificateValid
    leaf6000InnerLogValid leaf6000CoversExact leaf6000LowerChecked

private noncomputable def leaf6001Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (53/128), chiHi := (107/256) }

private noncomputable def leaf6001Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871377/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712573952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1405136681/1073741824) }, upper := { exponent := 1, mantissa := (10837/8192) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi315LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428970493/137425147904) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf6001InnerLog : WideLogData :=
  innerPair340Data

set_option maxRecDepth 1000000 in
private theorem leaf6001LocalValidity :
    LeafFacts leaf6001Box leaf6001Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6001Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712573952) }) = true
      norm_num [leaf6001Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6001CertificateValid :
    WideCertificateValid leaf6001Box leaf6001Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi315ValidityFacts
    leaf6001LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6001CoverageChecked :
    coverageCheck (innerAD leaf6001Box) leaf6001InnerLog = true := by
  rfl'

private theorem leaf6001InnerLogValid :
    leaf6001InnerLog.Valid 8 (innerAD leaf6001Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint92PositiveFacts.valid leaf6001CoverageChecked

private noncomputable def leaf6001InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629547/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6001InputLogOnePlusV_eq :
    leaf6001InputLogOnePlusV = outerEnclosure 24
      (leaf6001Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6001RoundedFacts : LeafRoundedFacts 8
    leaf6001Certificate.logOnePlusV leaf6001InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6001InputLogOnePlusV_eq }

private noncomputable def leaf6001Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi315InputQChi innerPair340Input
    leaf6001InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6001LowerChecked :
    lowerCheck 24 leaf6001Box leaf6001Inputs = true := by
  rfl'

private theorem leaf6001CoversExact : CoversExact 8
    leaf6001Box leaf6001Certificate leaf6001InnerLog leaf6001Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi315RoundedFacts
    innerPair340RoundedFacts leaf6001RoundedFacts (by rfl)

private theorem leaf6001FlatSound : Sound leaf6001Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6001CertificateValid
    leaf6001InnerLogValid leaf6001CoversExact leaf6001LowerChecked

private noncomputable def leaf6002Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (107/256), chiHi := (27/64) }

private noncomputable def leaf6002Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871379/536870912) }, vSqrt := { lower := (8191/8192), upper := (4042140973/4041912320) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1413328179/1073741824) }, upper := { exponent := 1, mantissa := (2725/2048) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi316LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (8084053293/8083824640) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf6002InnerLog : WideLogData :=
  innerPair345Data

set_option maxRecDepth 1000000 in
private theorem leaf6002LocalValidity :
    LeafFacts leaf6002Box leaf6002Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6002Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4042140973/4041912320) }) = true
      norm_num [leaf6002Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6002CertificateValid :
    WideCertificateValid leaf6002Box leaf6002Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi316ValidityFacts
    leaf6002LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6002CoverageChecked :
    coverageCheck (innerAD leaf6002Box) leaf6002InnerLog = true := by
  rfl'

private theorem leaf6002InnerLogValid :
    leaf6002InnerLog.Valid 8 (innerAD leaf6002Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint92PositiveFacts.valid leaf6002CoverageChecked

private noncomputable def leaf6002InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629555/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6002InputLogOnePlusV_eq :
    leaf6002InputLogOnePlusV = outerEnclosure 24
      (leaf6002Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6002RoundedFacts : LeafRoundedFacts 8
    leaf6002Certificate.logOnePlusV leaf6002InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6002InputLogOnePlusV_eq }

private noncomputable def leaf6002Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi316InputQChi innerPair345Input
    leaf6002InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6002LowerChecked :
    lowerCheck 24 leaf6002Box leaf6002Inputs = true := by
  rfl'

private theorem leaf6002CoversExact : CoversExact 8
    leaf6002Box leaf6002Certificate leaf6002InnerLog leaf6002Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi316RoundedFacts
    innerPair345RoundedFacts leaf6002RoundedFacts (by rfl)

private theorem leaf6002FlatSound : Sound leaf6002Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6002CertificateValid
    leaf6002InnerLogValid leaf6002CoversExact leaf6002LowerChecked

private noncomputable def leaf6003Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (13/32), chiHi := (105/256) }

private noncomputable def leaf6003Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871375/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712649216) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1395569011/1073741824) }, upper := { exponent := 1, mantissa := (21527/16384) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi313LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429045757/137425298432) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf6003InnerLog : WideLogData :=
  innerPair688Data

set_option maxRecDepth 1000000 in
private theorem leaf6003LocalValidity :
    LeafFacts leaf6003Box leaf6003Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6003Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712649216) }) = true
      norm_num [leaf6003Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6003CertificateValid :
    WideCertificateValid leaf6003Box leaf6003Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi313ValidityFacts
    leaf6003LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6003CoverageChecked :
    coverageCheck (innerAD leaf6003Box) leaf6003InnerLog = true := by
  rfl'

private theorem leaf6003InnerLogValid :
    leaf6003InnerLog.Valid 8 (innerAD leaf6003Box) :=
  wideLogDataValid_of_cachedCheck endpoint436PositiveFacts
    endpoint95PositiveFacts.valid leaf6003CoverageChecked

private noncomputable def leaf6003InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814769/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6003InputLogOnePlusV_eq :
    leaf6003InputLogOnePlusV = outerEnclosure 24
      (leaf6003Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6003RoundedFacts : LeafRoundedFacts 8
    leaf6003Certificate.logOnePlusV leaf6003InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6003InputLogOnePlusV_eq }

private noncomputable def leaf6003Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi313InputQChi innerPair688Input
    leaf6003InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6003LowerChecked :
    lowerCheck 24 leaf6003Box leaf6003Inputs = true := by
  rfl'

private theorem leaf6003CoversExact : CoversExact 8
    leaf6003Box leaf6003Certificate leaf6003InnerLog leaf6003Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi313RoundedFacts
    innerPair688RoundedFacts leaf6003RoundedFacts (by rfl)

private theorem leaf6003FlatSound : Sound leaf6003Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6003CertificateValid
    leaf6003InnerLogValid leaf6003CoversExact leaf6003LowerChecked

private noncomputable def leaf6004Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (105/256), chiHi := (53/128) }

private noncomputable def leaf6004Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871377/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712584192) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1403826041/1073741824) }, upper := { exponent := 1, mantissa := (10827/8192) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi314LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428980733/137425168384) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf6004InnerLog : WideLogData :=
  innerPair340Data

set_option maxRecDepth 1000000 in
private theorem leaf6004LocalValidity :
    LeafFacts leaf6004Box leaf6004Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6004Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712584192) }) = true
      norm_num [leaf6004Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6004CertificateValid :
    WideCertificateValid leaf6004Box leaf6004Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi314ValidityFacts
    leaf6004LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6004CoverageChecked :
    coverageCheck (innerAD leaf6004Box) leaf6004InnerLog = true := by
  rfl'

private theorem leaf6004InnerLogValid :
    leaf6004InnerLog.Valid 8 (innerAD leaf6004Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint92PositiveFacts.valid leaf6004CoverageChecked

private noncomputable def leaf6004InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814773/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6004InputLogOnePlusV_eq :
    leaf6004InputLogOnePlusV = outerEnclosure 24
      (leaf6004Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6004RoundedFacts : LeafRoundedFacts 8
    leaf6004Certificate.logOnePlusV leaf6004InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6004InputLogOnePlusV_eq }

private noncomputable def leaf6004Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi314InputQChi innerPair340Input
    leaf6004InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6004LowerChecked :
    lowerCheck 24 leaf6004Box leaf6004Inputs = true := by
  rfl'

private theorem leaf6004CoversExact : CoversExact 8
    leaf6004Box leaf6004Certificate leaf6004InnerLog leaf6004Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi314RoundedFacts
    innerPair340RoundedFacts leaf6004RoundedFacts (by rfl)

private theorem leaf6004FlatSound : Sound leaf6004Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6004CertificateValid
    leaf6004InnerLogValid leaf6004CoversExact leaf6004LowerChecked

private noncomputable def leaf6005Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (13/32), chiHi := (105/256) }

private noncomputable def leaf6005Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871377/536870912) }, vSqrt := { lower := (65527/65536), upper := (68716396541/68712595456) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1402384337/1073741824) }, upper := { exponent := 1, mantissa := (169/128) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi313LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (137428991997/137425190912) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf6005InnerLog : WideLogData :=
  innerPair698Data

set_option maxRecDepth 1000000 in
private theorem leaf6005LocalValidity :
    LeafFacts leaf6005Box leaf6005Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6005Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (68716396541/68712595456) }) = true
      norm_num [leaf6005Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6005CertificateValid :
    WideCertificateValid leaf6005Box leaf6005Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi313ValidityFacts
    leaf6005LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6005CoverageChecked :
    coverageCheck (innerAD leaf6005Box) leaf6005InnerLog = true := by
  rfl'

private theorem leaf6005InnerLogValid :
    leaf6005InnerLog.Valid 8 (innerAD leaf6005Box) :=
  wideLogDataValid_of_cachedCheck endpoint444PositiveFacts
    endpoint95PositiveFacts.valid leaf6005CoverageChecked

private noncomputable def leaf6005InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629545/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6005InputLogOnePlusV_eq :
    leaf6005InputLogOnePlusV = outerEnclosure 24
      (leaf6005Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6005RoundedFacts : LeafRoundedFacts 8
    leaf6005Certificate.logOnePlusV leaf6005InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6005InputLogOnePlusV_eq }

private noncomputable def leaf6005Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi313InputQChi innerPair698Input
    leaf6005InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6005LowerChecked :
    lowerCheck 24 leaf6005Box leaf6005Inputs = true := by
  rfl'

private theorem leaf6005CoversExact : CoversExact 8
    leaf6005Box leaf6005Certificate leaf6005InnerLog leaf6005Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi313RoundedFacts
    innerPair698RoundedFacts leaf6005RoundedFacts (by rfl)

private theorem leaf6005FlatSound : Sound leaf6005Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6005CertificateValid
    leaf6005InnerLogValid leaf6005CoversExact leaf6005LowerChecked

private noncomputable def leaf6006Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (105/256), chiHi := (53/128) }

private noncomputable def leaf6006Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871379/536870912) }, vSqrt := { lower := (65527/65536), upper := (68716396541/68712529920) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1410706899/1073741824) }, upper := { exponent := 1, mantissa := (85/64) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi314LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (137428926461/137425059840) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf6006InnerLog : WideLogData :=
  innerPair345Data

set_option maxRecDepth 1000000 in
private theorem leaf6006LocalValidity :
    LeafFacts leaf6006Box leaf6006Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6006Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (68716396541/68712529920) }) = true
      norm_num [leaf6006Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6006CertificateValid :
    WideCertificateValid leaf6006Box leaf6006Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi314ValidityFacts
    leaf6006LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6006CoverageChecked :
    coverageCheck (innerAD leaf6006Box) leaf6006InnerLog = true := by
  rfl'

private theorem leaf6006InnerLogValid :
    leaf6006InnerLog.Valid 8 (innerAD leaf6006Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint92PositiveFacts.valid leaf6006CoverageChecked

private noncomputable def leaf6006InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629553/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6006InputLogOnePlusV_eq :
    leaf6006InputLogOnePlusV = outerEnclosure 24
      (leaf6006Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6006RoundedFacts : LeafRoundedFacts 8
    leaf6006Certificate.logOnePlusV leaf6006InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6006InputLogOnePlusV_eq }

private noncomputable def leaf6006Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi314InputQChi innerPair345Input
    leaf6006InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6006LowerChecked :
    lowerCheck 24 leaf6006Box leaf6006Inputs = true := by
  rfl'

private theorem leaf6006CoversExact : CoversExact 8
    leaf6006Box leaf6006Certificate leaf6006InnerLog leaf6006Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi314RoundedFacts
    innerPair345RoundedFacts leaf6006RoundedFacts (by rfl)

private theorem leaf6006FlatSound : Sound leaf6006Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6006CertificateValid
    leaf6006InnerLogValid leaf6006CoversExact leaf6006LowerChecked

private noncomputable def leaf6007Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (53/128), chiHi := (107/256) }

private noncomputable def leaf6007Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871379/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712519168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1412083071/1073741824) }, upper := { exponent := 1, mantissa := (21781/16384) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi315LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428915709/137425038336) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf6007InnerLog : WideLogData :=
  innerPair345Data

set_option maxRecDepth 1000000 in
private theorem leaf6007LocalValidity :
    LeafFacts leaf6007Box leaf6007Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6007Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712519168) }) = true
      norm_num [leaf6007Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6007CertificateValid :
    WideCertificateValid leaf6007Box leaf6007Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi315ValidityFacts
    leaf6007LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6007CoverageChecked :
    coverageCheck (innerAD leaf6007Box) leaf6007InnerLog = true := by
  rfl'

private theorem leaf6007InnerLogValid :
    leaf6007InnerLog.Valid 8 (innerAD leaf6007Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint92PositiveFacts.valid leaf6007CoverageChecked

private noncomputable def leaf6007InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814777/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6007InputLogOnePlusV_eq :
    leaf6007InputLogOnePlusV = outerEnclosure 24
      (leaf6007Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6007RoundedFacts : LeafRoundedFacts 8
    leaf6007Certificate.logOnePlusV leaf6007InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6007InputLogOnePlusV_eq }

private noncomputable def leaf6007Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi315InputQChi innerPair345Input
    leaf6007InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6007LowerChecked :
    lowerCheck 24 leaf6007Box leaf6007Inputs = true := by
  rfl'

private theorem leaf6007CoversExact : CoversExact 8
    leaf6007Box leaf6007Certificate leaf6007InnerLog leaf6007Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi315RoundedFacts
    innerPair345RoundedFacts leaf6007RoundedFacts (by rfl)

private theorem leaf6007FlatSound : Sound leaf6007Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6007CertificateValid
    leaf6007InnerLogValid leaf6007CoversExact leaf6007LowerChecked

private noncomputable def leaf6008Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (107/256), chiHi := (27/64) }

private noncomputable def leaf6008Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871381/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712454144) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1420340101/1073741824) }, upper := { exponent := 1, mantissa := (5477/4096) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi316LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428850685/137424908288) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf6008InnerLog : WideLogData :=
  innerPair345Data

set_option maxRecDepth 1000000 in
private theorem leaf6008LocalValidity :
    LeafFacts leaf6008Box leaf6008Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6008Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712454144) }) = true
      norm_num [leaf6008Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6008CertificateValid :
    WideCertificateValid leaf6008Box leaf6008Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi316ValidityFacts
    leaf6008LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6008CoverageChecked :
    coverageCheck (innerAD leaf6008Box) leaf6008InnerLog = true := by
  rfl'

private theorem leaf6008InnerLogValid :
    leaf6008InnerLog.Valid 8 (innerAD leaf6008Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint92PositiveFacts.valid leaf6008CoverageChecked

private noncomputable def leaf6008InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814781/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6008InputLogOnePlusV_eq :
    leaf6008InputLogOnePlusV = outerEnclosure 24
      (leaf6008Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6008RoundedFacts : LeafRoundedFacts 8
    leaf6008Certificate.logOnePlusV leaf6008InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6008InputLogOnePlusV_eq }

private noncomputable def leaf6008Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi316InputQChi innerPair345Input
    leaf6008InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6008LowerChecked :
    lowerCheck 24 leaf6008Box leaf6008Inputs = true := by
  rfl'

private theorem leaf6008CoversExact : CoversExact 8
    leaf6008Box leaf6008Certificate leaf6008InnerLog leaf6008Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi316RoundedFacts
    innerPair345RoundedFacts leaf6008RoundedFacts (by rfl)

private theorem leaf6008FlatSound : Sound leaf6008Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6008CertificateValid
    leaf6008InnerLogValid leaf6008CoversExact leaf6008LowerChecked

private noncomputable def leaf6009Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (53/128), chiHi := (107/256) }

private noncomputable def leaf6009Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871381/536870912) }, vSqrt := { lower := (65527/65536), upper := (68716396541/68712464384) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1419029461/1073741824) }, upper := { exponent := 1, mantissa := (171/128) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi315LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (137428860925/137424928768) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf6009InnerLog : WideLogData :=
  innerPair345Data

set_option maxRecDepth 1000000 in
private theorem leaf6009LocalValidity :
    LeafFacts leaf6009Box leaf6009Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6009Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (68716396541/68712464384) }) = true
      norm_num [leaf6009Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6009CertificateValid :
    WideCertificateValid leaf6009Box leaf6009Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi315ValidityFacts
    leaf6009LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6009CoverageChecked :
    coverageCheck (innerAD leaf6009Box) leaf6009InnerLog = true := by
  rfl'

private theorem leaf6009InnerLogValid :
    leaf6009InnerLog.Valid 8 (innerAD leaf6009Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint92PositiveFacts.valid leaf6009CoverageChecked

private noncomputable def leaf6009InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629561/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6009InputLogOnePlusV_eq :
    leaf6009InputLogOnePlusV = outerEnclosure 24
      (leaf6009Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6009RoundedFacts : LeafRoundedFacts 8
    leaf6009Certificate.logOnePlusV leaf6009InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6009InputLogOnePlusV_eq }

private noncomputable def leaf6009Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi315InputQChi innerPair345Input
    leaf6009InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6009LowerChecked :
    lowerCheck 24 leaf6009Box leaf6009Inputs = true := by
  rfl'

private theorem leaf6009CoversExact : CoversExact 8
    leaf6009Box leaf6009Certificate leaf6009InnerLog leaf6009Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi315RoundedFacts
    innerPair345RoundedFacts leaf6009RoundedFacts (by rfl)

private theorem leaf6009FlatSound : Sound leaf6009Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6009CertificateValid
    leaf6009InnerLogValid leaf6009CoversExact leaf6009LowerChecked

private noncomputable def leaf6010Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (107/256), chiHi := (27/64) }

private noncomputable def leaf6010Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871383/536870912) }, vSqrt := { lower := (65527/65536), upper := (68716396541/68712398848) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1427352023/1073741824) }, upper := { exponent := 1, mantissa := (43/32) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi316LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (137428795389/137424797696) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf6010InnerLog : WideLogData :=
  innerPair345Data

set_option maxRecDepth 1000000 in
private theorem leaf6010LocalValidity :
    LeafFacts leaf6010Box leaf6010Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6010Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (68716396541/68712398848) }) = true
      norm_num [leaf6010Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6010CertificateValid :
    WideCertificateValid leaf6010Box leaf6010Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi316ValidityFacts
    leaf6010LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6010CoverageChecked :
    coverageCheck (innerAD leaf6010Box) leaf6010InnerLog = true := by
  rfl'

private theorem leaf6010InnerLogValid :
    leaf6010InnerLog.Valid 8 (innerAD leaf6010Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint92PositiveFacts.valid leaf6010CoverageChecked

private noncomputable def leaf6010InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629569/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6010InputLogOnePlusV_eq :
    leaf6010InputLogOnePlusV = outerEnclosure 24
      (leaf6010Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6010RoundedFacts : LeafRoundedFacts 8
    leaf6010Certificate.logOnePlusV leaf6010InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6010InputLogOnePlusV_eq }

private noncomputable def leaf6010Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi316InputQChi innerPair345Input
    leaf6010InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6010LowerChecked :
    lowerCheck 24 leaf6010Box leaf6010Inputs = true := by
  rfl'

private theorem leaf6010CoversExact : CoversExact 8
    leaf6010Box leaf6010Certificate leaf6010InnerLog leaf6010Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi316RoundedFacts
    innerPair345RoundedFacts leaf6010RoundedFacts (by rfl)

private theorem leaf6010FlatSound : Sound leaf6010Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6010CertificateValid
    leaf6010InnerLogValid leaf6010CoversExact leaf6010LowerChecked

private noncomputable def leaf6011Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (27/64), chiHi := (55/128) }

private noncomputable def leaf6011Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435815/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712436736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (707204603/536870912) }, upper := { exponent := 1, mantissa := (10971/8192) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi265LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428833277/137424873472) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf6011InnerLog : WideLogData :=
  innerPair712Data

set_option maxRecDepth 1000000 in
private theorem leaf6011LocalValidity :
    LeafFacts leaf6011Box leaf6011Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6011Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712436736) }) = true
      norm_num [leaf6011Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6011CertificateValid :
    WideCertificateValid leaf6011Box leaf6011Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi265ValidityFacts
    leaf6011LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6011CoverageChecked :
    coverageCheck (innerAD leaf6011Box) leaf6011InnerLog = true := by
  rfl'

private theorem leaf6011InnerLogValid :
    leaf6011InnerLog.Valid 8 (innerAD leaf6011Box) :=
  wideLogDataValid_of_cachedCheck endpoint452PositiveFacts
    endpoint453PositiveFacts.valid leaf6011CoverageChecked

private noncomputable def leaf6011InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907391/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6011InputLogOnePlusV_eq :
    leaf6011InputLogOnePlusV = outerEnclosure 24
      (leaf6011Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6011RoundedFacts : LeafRoundedFacts 8
    leaf6011Certificate.logOnePlusV leaf6011InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6011InputLogOnePlusV_eq }

private noncomputable def leaf6011Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi265InputQChi innerPair712Input
    leaf6011InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6011LowerChecked :
    lowerCheck 24 leaf6011Box leaf6011Inputs = true := by
  rfl'

private theorem leaf6011CoversExact : CoversExact 8
    leaf6011Box leaf6011Certificate leaf6011InnerLog leaf6011Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi265RoundedFacts
    innerPair712RoundedFacts leaf6011RoundedFacts (by rfl)

private theorem leaf6011FlatSound : Sound leaf6011Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6011CertificateValid
    leaf6011InnerLogValid leaf6011CoversExact leaf6011LowerChecked

private noncomputable def leaf6012Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (27/64), chiHi := (109/256) }

private noncomputable def leaf6012Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871381/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712444928) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1421519677/1073741824) }, upper := { exponent := 1, mantissa := (10963/8192) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi317LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428841469/137424889856) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf6012InnerLog : WideLogData :=
  innerPair345Data

set_option maxRecDepth 1000000 in
private theorem leaf6012LocalValidity :
    LeafFacts leaf6012Box leaf6012Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6012Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712444928) }) = true
      norm_num [leaf6012Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6012CertificateValid :
    WideCertificateValid leaf6012Box leaf6012Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi317ValidityFacts
    leaf6012LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6012CoverageChecked :
    coverageCheck (innerAD leaf6012Box) leaf6012InnerLog = true := by
  rfl'

private theorem leaf6012InnerLogValid :
    leaf6012InnerLog.Valid 8 (innerAD leaf6012Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint92PositiveFacts.valid leaf6012CoverageChecked

private noncomputable def leaf6012InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629563/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6012InputLogOnePlusV_eq :
    leaf6012InputLogOnePlusV = outerEnclosure 24
      (leaf6012Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6012RoundedFacts : LeafRoundedFacts 8
    leaf6012Certificate.logOnePlusV leaf6012InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6012InputLogOnePlusV_eq }

private noncomputable def leaf6012Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi317InputQChi innerPair345Input
    leaf6012InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6012LowerChecked :
    lowerCheck 24 leaf6012Box leaf6012Inputs = true := by
  rfl'

private theorem leaf6012CoversExact : CoversExact 8
    leaf6012Box leaf6012Certificate leaf6012InnerLog leaf6012Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi317RoundedFacts
    innerPair345RoundedFacts leaf6012RoundedFacts (by rfl)

private theorem leaf6012FlatSound : Sound leaf6012Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6012CertificateValid
    leaf6012InnerLogValid leaf6012CoversExact leaf6012LowerChecked

private noncomputable def leaf6013Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (109/256), chiHi := (55/128) }

private noncomputable def leaf6013Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871383/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712380416) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1429711175/1073741824) }, upper := { exponent := 1, mantissa := (5513/4096) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi318LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428776957/137424760832) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf6013InnerLog : WideLogData :=
  innerPair346Data

set_option maxRecDepth 1000000 in
private theorem leaf6013LocalValidity :
    LeafFacts leaf6013Box leaf6013Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6013Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712380416) }) = true
      norm_num [leaf6013Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6013CertificateValid :
    WideCertificateValid leaf6013Box leaf6013Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi318ValidityFacts
    leaf6013LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6013CoverageChecked :
    coverageCheck (innerAD leaf6013Box) leaf6013InnerLog = true := by
  rfl'

private theorem leaf6013InnerLogValid :
    leaf6013InnerLog.Valid 8 (innerAD leaf6013Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint93PositiveFacts.valid leaf6013CoverageChecked

private noncomputable def leaf6013InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629571/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6013InputLogOnePlusV_eq :
    leaf6013InputLogOnePlusV = outerEnclosure 24
      (leaf6013Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6013RoundedFacts : LeafRoundedFacts 8
    leaf6013Certificate.logOnePlusV leaf6013InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6013InputLogOnePlusV_eq }

private noncomputable def leaf6013Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi318InputQChi innerPair346Input
    leaf6013InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6013LowerChecked :
    lowerCheck 24 leaf6013Box leaf6013Inputs = true := by
  rfl'

private theorem leaf6013CoversExact : CoversExact 8
    leaf6013Box leaf6013Certificate leaf6013InnerLog leaf6013Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi318RoundedFacts
    innerPair346RoundedFacts leaf6013RoundedFacts (by rfl)

private theorem leaf6013FlatSound : Sound leaf6013Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6013CertificateValid
    leaf6013InnerLogValid leaf6013CoversExact leaf6013LowerChecked

private noncomputable def leaf6014Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (55/128), chiHi := (7/16) }

private noncomputable def leaf6014Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435817/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712308736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (715330569/536870912) }, upper := { exponent := 1, mantissa := (1387/1024) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi266LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428705277/137424617472) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf6014InnerLog : WideLogData :=
  innerPair713Data

set_option maxRecDepth 1000000 in
private theorem leaf6014LocalValidity :
    LeafFacts leaf6014Box leaf6014Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6014Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712308736) }) = true
      norm_num [leaf6014Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6014CertificateValid :
    WideCertificateValid leaf6014Box leaf6014Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi266ValidityFacts
    leaf6014LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6014CoverageChecked :
    coverageCheck (innerAD leaf6014Box) leaf6014InnerLog = true := by
  rfl'

private theorem leaf6014InnerLogValid :
    leaf6014InnerLog.Valid 8 (innerAD leaf6014Box) :=
  wideLogDataValid_of_cachedCheck endpoint454PositiveFacts
    endpoint455PositiveFacts.valid leaf6014CoverageChecked

private noncomputable def leaf6014InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907395/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6014InputLogOnePlusV_eq :
    leaf6014InputLogOnePlusV = outerEnclosure 24
      (leaf6014Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6014RoundedFacts : LeafRoundedFacts 8
    leaf6014Certificate.logOnePlusV leaf6014InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6014InputLogOnePlusV_eq }

private noncomputable def leaf6014Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi266InputQChi innerPair713Input
    leaf6014InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6014LowerChecked :
    lowerCheck 24 leaf6014Box leaf6014Inputs = true := by
  rfl'

private theorem leaf6014CoversExact : CoversExact 8
    leaf6014Box leaf6014Certificate leaf6014InnerLog leaf6014Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi266RoundedFacts
    innerPair713RoundedFacts leaf6014RoundedFacts (by rfl)

private theorem leaf6014FlatSound : Sound leaf6014Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6014CertificateValid
    leaf6014InnerLogValid leaf6014CoversExact leaf6014LowerChecked

private noncomputable def leaf6015Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (55/128), chiHi := (7/16) }

private noncomputable def leaf6015Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435819/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712251392) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (718934827/536870912) }, upper := { exponent := 1, mantissa := (697/512) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi266LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428647933/137424502784) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf6015InnerLog : WideLogData :=
  innerPair714Data

set_option maxRecDepth 1000000 in
private theorem leaf6015LocalValidity :
    LeafFacts leaf6015Box leaf6015Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6015Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712251392) }) = true
      norm_num [leaf6015Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6015CertificateValid :
    WideCertificateValid leaf6015Box leaf6015Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi266ValidityFacts
    leaf6015LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6015CoverageChecked :
    coverageCheck (innerAD leaf6015Box) leaf6015InnerLog = true := by
  rfl'

private theorem leaf6015InnerLogValid :
    leaf6015InnerLog.Valid 8 (innerAD leaf6015Box) :=
  wideLogDataValid_of_cachedCheck endpoint456PositiveFacts
    endpoint457PositiveFacts.valid leaf6015CoverageChecked

private noncomputable def leaf6015InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629587/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6015InputLogOnePlusV_eq :
    leaf6015InputLogOnePlusV = outerEnclosure 24
      (leaf6015Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6015RoundedFacts : LeafRoundedFacts 8
    leaf6015Certificate.logOnePlusV leaf6015InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6015InputLogOnePlusV_eq }

private noncomputable def leaf6015Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi266InputQChi innerPair714Input
    leaf6015InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6015LowerChecked :
    lowerCheck 24 leaf6015Box leaf6015Inputs = true := by
  rfl'

private theorem leaf6015CoversExact : CoversExact 8
    leaf6015Box leaf6015Certificate leaf6015InnerLog leaf6015Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi266RoundedFacts
    innerPair714RoundedFacts leaf6015RoundedFacts (by rfl)

private theorem leaf6015FlatSound : Sound leaf6015Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6015CertificateValid
    leaf6015InnerLogValid leaf6015CoversExact leaf6015LowerChecked

private noncomputable def leaf6016Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (27/64), chiHi := (109/256) }

private noncomputable def leaf6016Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871383/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712389120) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1428597131/1073741824) }, upper := { exponent := 1, mantissa := (22035/16384) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi317LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428785661/137424778240) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf6016InnerLog : WideLogData :=
  innerPair702Data

set_option maxRecDepth 1000000 in
private theorem leaf6016LocalValidity :
    LeafFacts leaf6016Box leaf6016Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6016Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712389120) }) = true
      norm_num [leaf6016Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6016CertificateValid :
    WideCertificateValid leaf6016Box leaf6016Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi317ValidityFacts
    leaf6016LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6016CoverageChecked :
    coverageCheck (innerAD leaf6016Box) leaf6016InnerLog = true := by
  rfl'

private theorem leaf6016InnerLogValid :
    leaf6016InnerLog.Valid 8 (innerAD leaf6016Box) :=
  wideLogDataValid_of_cachedCheck endpoint447PositiveFacts
    endpoint451PositiveFacts.valid leaf6016CoverageChecked

private noncomputable def leaf6016InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814785/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6016InputLogOnePlusV_eq :
    leaf6016InputLogOnePlusV = outerEnclosure 24
      (leaf6016Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6016RoundedFacts : LeafRoundedFacts 8
    leaf6016Certificate.logOnePlusV leaf6016InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6016InputLogOnePlusV_eq }

private noncomputable def leaf6016Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi317InputQChi innerPair702Input
    leaf6016InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6016LowerChecked :
    lowerCheck 24 leaf6016Box leaf6016Inputs = true := by
  rfl'

private theorem leaf6016CoversExact : CoversExact 8
    leaf6016Box leaf6016Certificate leaf6016InnerLog leaf6016Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi317RoundedFacts
    innerPair702RoundedFacts leaf6016RoundedFacts (by rfl)

private theorem leaf6016FlatSound : Sound leaf6016Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6016CertificateValid
    leaf6016InnerLogValid leaf6016CoversExact leaf6016LowerChecked

private noncomputable def leaf6017Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (109/256), chiHi := (55/128) }

private noncomputable def leaf6017Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871385/536870912) }, vSqrt := { lower := (8191/8192), upper := (5285876657/5285563392) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1436854161/1073741824) }, upper := { exponent := 1, mantissa := (11081/8192) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi318LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (10571440049/10571126784) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf6017InnerLog : WideLogData :=
  innerPair346Data

set_option maxRecDepth 1000000 in
private theorem leaf6017LocalValidity :
    LeafFacts leaf6017Box leaf6017Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6017Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5285876657/5285563392) }) = true
      norm_num [leaf6017Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6017CertificateValid :
    WideCertificateValid leaf6017Box leaf6017Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi318ValidityFacts
    leaf6017LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6017CoverageChecked :
    coverageCheck (innerAD leaf6017Box) leaf6017InnerLog = true := by
  rfl'

private theorem leaf6017InnerLogValid :
    leaf6017InnerLog.Valid 8 (innerAD leaf6017Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint93PositiveFacts.valid leaf6017CoverageChecked

private noncomputable def leaf6017InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814789/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6017InputLogOnePlusV_eq :
    leaf6017InputLogOnePlusV = outerEnclosure 24
      (leaf6017Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6017RoundedFacts : LeafRoundedFacts 8
    leaf6017Certificate.logOnePlusV leaf6017InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6017InputLogOnePlusV_eq }

private noncomputable def leaf6017Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi318InputQChi innerPair346Input
    leaf6017InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6017LowerChecked :
    lowerCheck 24 leaf6017Box leaf6017Inputs = true := by
  rfl'

private theorem leaf6017CoversExact : CoversExact 8
    leaf6017Box leaf6017Certificate leaf6017InnerLog leaf6017Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi318RoundedFacts
    innerPair346RoundedFacts leaf6017RoundedFacts (by rfl)

private theorem leaf6017FlatSound : Sound leaf6017Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6017CertificateValid
    leaf6017InnerLogValid leaf6017CoversExact leaf6017LowerChecked

private noncomputable def leaf6018Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (27/64), chiHi := (109/256) }

private noncomputable def leaf6018Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871385/536870912) }, vSqrt := { lower := (65527/65536), upper := (68716396541/68712333312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1435674585/1073741824) }, upper := { exponent := 1, mantissa := (173/128) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi317LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (137428729853/137424666624) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf6018InnerLog : WideLogData :=
  innerPair346Data

set_option maxRecDepth 1000000 in
private theorem leaf6018LocalValidity :
    LeafFacts leaf6018Box leaf6018Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6018Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (68716396541/68712333312) }) = true
      norm_num [leaf6018Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6018CertificateValid :
    WideCertificateValid leaf6018Box leaf6018Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi317ValidityFacts
    leaf6018LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6018CoverageChecked :
    coverageCheck (innerAD leaf6018Box) leaf6018InnerLog = true := by
  rfl'

private theorem leaf6018InnerLogValid :
    leaf6018InnerLog.Valid 8 (innerAD leaf6018Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint93PositiveFacts.valid leaf6018CoverageChecked

private noncomputable def leaf6018InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629577/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6018InputLogOnePlusV_eq :
    leaf6018InputLogOnePlusV = outerEnclosure 24
      (leaf6018Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6018RoundedFacts : LeafRoundedFacts 8
    leaf6018Certificate.logOnePlusV leaf6018InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6018InputLogOnePlusV_eq }

private noncomputable def leaf6018Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi317InputQChi innerPair346Input
    leaf6018InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6018LowerChecked :
    lowerCheck 24 leaf6018Box leaf6018Inputs = true := by
  rfl'

private theorem leaf6018CoversExact : CoversExact 8
    leaf6018Box leaf6018Certificate leaf6018InnerLog leaf6018Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi317RoundedFacts
    innerPair346RoundedFacts leaf6018RoundedFacts (by rfl)

private theorem leaf6018FlatSound : Sound leaf6018Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6018CertificateValid
    leaf6018InnerLogValid leaf6018CoversExact leaf6018LowerChecked

private noncomputable def leaf6019Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (109/256), chiHi := (55/128) }

private noncomputable def leaf6019Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871387/536870912) }, vSqrt := { lower := (65527/65536), upper := (68716396541/68712267776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1443997147/1073741824) }, upper := { exponent := 1, mantissa := (87/64) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi318LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (137428664317/137424535552) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf6019InnerLog : WideLogData :=
  innerPair352Data

set_option maxRecDepth 1000000 in
private theorem leaf6019LocalValidity :
    LeafFacts leaf6019Box leaf6019Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6019Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (68716396541/68712267776) }) = true
      norm_num [leaf6019Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6019CertificateValid :
    WideCertificateValid leaf6019Box leaf6019Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi318ValidityFacts
    leaf6019LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6019CoverageChecked :
    coverageCheck (innerAD leaf6019Box) leaf6019InnerLog = true := by
  rfl'

private theorem leaf6019InnerLogValid :
    leaf6019InnerLog.Valid 8 (innerAD leaf6019Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint93PositiveFacts.valid leaf6019CoverageChecked

private noncomputable def leaf6019InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629585/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6019InputLogOnePlusV_eq :
    leaf6019InputLogOnePlusV = outerEnclosure 24
      (leaf6019Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6019RoundedFacts : LeafRoundedFacts 8
    leaf6019Certificate.logOnePlusV leaf6019InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6019InputLogOnePlusV_eq }

private noncomputable def leaf6019Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi318InputQChi innerPair352Input
    leaf6019InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6019LowerChecked :
    lowerCheck 24 leaf6019Box leaf6019Inputs = true := by
  rfl'

private theorem leaf6019CoversExact : CoversExact 8
    leaf6019Box leaf6019Certificate leaf6019InnerLog leaf6019Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi318RoundedFacts
    innerPair352RoundedFacts leaf6019RoundedFacts (by rfl)

private theorem leaf6019FlatSound : Sound leaf6019Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6019CertificateValid
    leaf6019InnerLogValid leaf6019CoversExact leaf6019LowerChecked

private noncomputable def leaf6020Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (55/128), chiHi := (7/16) }

private noncomputable def leaf6020Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435821/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712194048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (722539085/536870912) }, upper := { exponent := 1, mantissa := (1401/1024) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi266LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428590589/137424388096) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf6020InnerLog : WideLogData :=
  innerPair716Data

set_option maxRecDepth 1000000 in
private theorem leaf6020LocalValidity :
    LeafFacts leaf6020Box leaf6020Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6020Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712194048) }) = true
      norm_num [leaf6020Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6020CertificateValid :
    WideCertificateValid leaf6020Box leaf6020Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi266ValidityFacts
    leaf6020LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6020CoverageChecked :
    coverageCheck (innerAD leaf6020Box) leaf6020InnerLog = true := by
  rfl'

private theorem leaf6020InnerLogValid :
    leaf6020InnerLog.Valid 8 (innerAD leaf6020Box) :=
  wideLogDataValid_of_cachedCheck endpoint458PositiveFacts
    endpoint459PositiveFacts.valid leaf6020CoverageChecked

private noncomputable def leaf6020InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814797/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6020InputLogOnePlusV_eq :
    leaf6020InputLogOnePlusV = outerEnclosure 24
      (leaf6020Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6020RoundedFacts : LeafRoundedFacts 8
    leaf6020Certificate.logOnePlusV leaf6020InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6020InputLogOnePlusV_eq }

private noncomputable def leaf6020Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi266InputQChi innerPair716Input
    leaf6020InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6020LowerChecked :
    lowerCheck 24 leaf6020Box leaf6020Inputs = true := by
  rfl'

private theorem leaf6020CoversExact : CoversExact 8
    leaf6020Box leaf6020Certificate leaf6020InnerLog leaf6020Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi266RoundedFacts
    innerPair716RoundedFacts leaf6020RoundedFacts (by rfl)

private theorem leaf6020FlatSound : Sound leaf6020Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6020CertificateValid
    leaf6020InnerLogValid leaf6020CoversExact leaf6020LowerChecked

private noncomputable def leaf6021Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (55/128), chiHi := (111/256) }

private noncomputable def leaf6021Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871389/536870912) }, vSqrt := { lower := (65527/65536), upper := (68716396541/68712202240) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1452319709/1073741824) }, upper := { exponent := 1, mantissa := (175/128) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi319LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (137428598781/137424404480) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf6021InnerLog : WideLogData :=
  innerPair352Data

set_option maxRecDepth 1000000 in
private theorem leaf6021LocalValidity :
    LeafFacts leaf6021Box leaf6021Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6021Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (68716396541/68712202240) }) = true
      norm_num [leaf6021Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6021CertificateValid :
    WideCertificateValid leaf6021Box leaf6021Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi319ValidityFacts
    leaf6021LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6021CoverageChecked :
    coverageCheck (innerAD leaf6021Box) leaf6021InnerLog = true := by
  rfl'

private theorem leaf6021InnerLogValid :
    leaf6021InnerLog.Valid 8 (innerAD leaf6021Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint93PositiveFacts.valid leaf6021CoverageChecked

private noncomputable def leaf6021InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629593/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6021InputLogOnePlusV_eq :
    leaf6021InputLogOnePlusV = outerEnclosure 24
      (leaf6021Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6021RoundedFacts : LeafRoundedFacts 8
    leaf6021Certificate.logOnePlusV leaf6021InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6021InputLogOnePlusV_eq }

private noncomputable def leaf6021Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi319InputQChi innerPair352Input
    leaf6021InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6021LowerChecked :
    lowerCheck 24 leaf6021Box leaf6021Inputs = true := by
  rfl'

private theorem leaf6021CoversExact : CoversExact 8
    leaf6021Box leaf6021Certificate leaf6021InnerLog leaf6021Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi319RoundedFacts
    innerPair352RoundedFacts leaf6021RoundedFacts (by rfl)

private theorem leaf6021FlatSound : Sound leaf6021Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6021CertificateValid
    leaf6021InnerLogValid leaf6021CoversExact leaf6021LowerChecked

private noncomputable def leaf6022Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (111/256), chiHi := (7/16) }

private noncomputable def leaf6022Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871391/536870912) }, vSqrt := { lower := (65527/65536), upper := (68716396541/68712136704) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1460642271/1073741824) }, upper := { exponent := 1, mantissa := (11/8) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi320LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (137428533245/137424273408) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf6022InnerLog : WideLogData :=
  innerPair352Data

set_option maxRecDepth 1000000 in
private theorem leaf6022LocalValidity :
    LeafFacts leaf6022Box leaf6022Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6022Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (68716396541/68712136704) }) = true
      norm_num [leaf6022Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6022CertificateValid :
    WideCertificateValid leaf6022Box leaf6022Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi320ValidityFacts
    leaf6022LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6022CoverageChecked :
    coverageCheck (innerAD leaf6022Box) leaf6022InnerLog = true := by
  rfl'

private theorem leaf6022InnerLogValid :
    leaf6022InnerLog.Valid 8 (innerAD leaf6022Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint93PositiveFacts.valid leaf6022CoverageChecked

private noncomputable def leaf6022InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629601/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6022InputLogOnePlusV_eq :
    leaf6022InputLogOnePlusV = outerEnclosure 24
      (leaf6022Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6022RoundedFacts : LeafRoundedFacts 8
    leaf6022Certificate.logOnePlusV leaf6022InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6022InputLogOnePlusV_eq }

private noncomputable def leaf6022Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi320InputQChi innerPair352Input
    leaf6022InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6022LowerChecked :
    lowerCheck 24 leaf6022Box leaf6022Inputs = true := by
  rfl'

private theorem leaf6022CoversExact : CoversExact 8
    leaf6022Box leaf6022Certificate leaf6022InnerLog leaf6022Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi320RoundedFacts
    innerPair352RoundedFacts leaf6022RoundedFacts (by rfl)

private theorem leaf6022FlatSound : Sound leaf6022Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6022CertificateValid
    leaf6022InnerLogValid leaf6022CoversExact leaf6022LowerChecked

private noncomputable def component120Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (13/32), chiHi := (53/128) }

set_option maxRecDepth 1000000 in
private theorem component120Node0_sound : Sound component120Node0Box :=
  sound_of_literal_split component120Node0Box leaf5973Box leaf5974Box
    .chi (105/256) (by rfl) (by rfl)
    leaf5973FlatSound leaf5974FlatSound

private noncomputable def component120Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (13/32), chiHi := (53/128) }

set_option maxRecDepth 1000000 in
private theorem component120Node1_sound : Sound component120Node1Box :=
  sound_of_literal_split component120Node1Box leaf5975Box leaf5976Box
    .chi (105/256) (by rfl) (by rfl)
    leaf5975FlatSound leaf5976FlatSound

private noncomputable def component120Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (13/32), chiHi := (53/128) }

set_option maxRecDepth 1000000 in
private theorem component120Node2_sound : Sound component120Node2Box :=
  sound_of_literal_split component120Node2Box component120Node0Box component120Node1Box
    .k (121/32) (by rfl) (by rfl)
    component120Node0_sound component120Node1_sound

private noncomputable def component120Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (53/128), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component120Node3_sound : Sound component120Node3Box :=
  sound_of_literal_split component120Node3Box leaf5977Box leaf5978Box
    .k (121/32) (by rfl) (by rfl)
    leaf5977FlatSound leaf5978FlatSound

private noncomputable def component120Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (13/32), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component120Node4_sound : Sound component120Node4Box :=
  sound_of_literal_split component120Node4Box component120Node2Box component120Node3Box
    .chi (53/128) (by rfl) (by rfl)
    component120Node2_sound component120Node3_sound

private noncomputable def component120Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (13/32), chiHi := (53/128) }

set_option maxRecDepth 1000000 in
private theorem component120Node5_sound : Sound component120Node5Box :=
  sound_of_literal_split component120Node5Box leaf5979Box leaf5980Box
    .chi (105/256) (by rfl) (by rfl)
    leaf5979FlatSound leaf5980FlatSound

private noncomputable def component120Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (13/32), chiHi := (53/128) }

set_option maxRecDepth 1000000 in
private theorem component120Node6_sound : Sound component120Node6Box :=
  sound_of_literal_split component120Node6Box leaf5981Box leaf5982Box
    .chi (105/256) (by rfl) (by rfl)
    leaf5981FlatSound leaf5982FlatSound

private noncomputable def component120Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (13/32), chiHi := (53/128) }

set_option maxRecDepth 1000000 in
private theorem component120Node7_sound : Sound component120Node7Box :=
  sound_of_literal_split component120Node7Box component120Node5Box component120Node6Box
    .k (123/32) (by rfl) (by rfl)
    component120Node5_sound component120Node6_sound

private noncomputable def component120Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (53/128), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component120Node8_sound : Sound component120Node8Box :=
  sound_of_literal_split component120Node8Box leaf5983Box leaf5984Box
    .chi (107/256) (by rfl) (by rfl)
    leaf5983FlatSound leaf5984FlatSound

private noncomputable def component120Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (53/128), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component120Node9_sound : Sound component120Node9Box :=
  sound_of_literal_split component120Node9Box leaf5985Box leaf5986Box
    .chi (107/256) (by rfl) (by rfl)
    leaf5985FlatSound leaf5986FlatSound

private noncomputable def component120Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (53/128), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component120Node10_sound : Sound component120Node10Box :=
  sound_of_literal_split component120Node10Box component120Node8Box component120Node9Box
    .k (123/32) (by rfl) (by rfl)
    component120Node8_sound component120Node9_sound

private noncomputable def component120Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (13/32), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component120Node11_sound : Sound component120Node11Box :=
  sound_of_literal_split component120Node11Box component120Node7Box component120Node10Box
    .chi (53/128) (by rfl) (by rfl)
    component120Node7_sound component120Node10_sound

private noncomputable def component120Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (13/32), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component120Node12_sound : Sound component120Node12Box :=
  sound_of_literal_split component120Node12Box component120Node4Box component120Node11Box
    .k (61/16) (by rfl) (by rfl)
    component120Node4_sound component120Node11_sound

private noncomputable def component120Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (27/64), chiHi := (55/128) }

set_option maxRecDepth 1000000 in
private theorem component120Node13_sound : Sound component120Node13Box :=
  sound_of_literal_split component120Node13Box leaf5987Box leaf5988Box
    .k (121/32) (by rfl) (by rfl)
    leaf5987FlatSound leaf5988FlatSound

private noncomputable def component120Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (55/128), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component120Node14_sound : Sound component120Node14Box :=
  sound_of_literal_split component120Node14Box leaf5989Box leaf5990Box
    .k (121/32) (by rfl) (by rfl)
    leaf5989FlatSound leaf5990FlatSound

private noncomputable def component120Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (27/64), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component120Node15_sound : Sound component120Node15Box :=
  sound_of_literal_split component120Node15Box component120Node13Box component120Node14Box
    .chi (55/128) (by rfl) (by rfl)
    component120Node13_sound component120Node14_sound

private noncomputable def component120Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (27/64), chiHi := (55/128) }

set_option maxRecDepth 1000000 in
private theorem component120Node16_sound : Sound component120Node16Box :=
  sound_of_literal_split component120Node16Box leaf5991Box leaf5992Box
    .k (123/32) (by rfl) (by rfl)
    leaf5991FlatSound leaf5992FlatSound

private noncomputable def component120Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (55/128), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component120Node17_sound : Sound component120Node17Box :=
  sound_of_literal_split component120Node17Box leaf5993Box leaf5994Box
    .k (123/32) (by rfl) (by rfl)
    leaf5993FlatSound leaf5994FlatSound

private noncomputable def component120Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (27/64), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component120Node18_sound : Sound component120Node18Box :=
  sound_of_literal_split component120Node18Box component120Node16Box component120Node17Box
    .chi (55/128) (by rfl) (by rfl)
    component120Node16_sound component120Node17_sound

private noncomputable def component120Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (27/64), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component120Node19_sound : Sound component120Node19Box :=
  sound_of_literal_split component120Node19Box component120Node15Box component120Node18Box
    .k (61/16) (by rfl) (by rfl)
    component120Node15_sound component120Node18_sound

private noncomputable def component120Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (13/32), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component120Node20_sound : Sound component120Node20Box :=
  sound_of_literal_split component120Node20Box component120Node12Box component120Node19Box
    .chi (27/64) (by rfl) (by rfl)
    component120Node12_sound component120Node19_sound

private noncomputable def component120Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (13/32), chiHi := (53/128) }

set_option maxRecDepth 1000000 in
private theorem component120Node21_sound : Sound component120Node21Box :=
  sound_of_literal_split component120Node21Box leaf5995Box leaf5996Box
    .chi (105/256) (by rfl) (by rfl)
    leaf5995FlatSound leaf5996FlatSound

private noncomputable def component120Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (13/32), chiHi := (53/128) }

set_option maxRecDepth 1000000 in
private theorem component120Node22_sound : Sound component120Node22Box :=
  sound_of_literal_split component120Node22Box leaf5997Box leaf5998Box
    .chi (105/256) (by rfl) (by rfl)
    leaf5997FlatSound leaf5998FlatSound

private noncomputable def component120Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (13/32), chiHi := (53/128) }

set_option maxRecDepth 1000000 in
private theorem component120Node23_sound : Sound component120Node23Box :=
  sound_of_literal_split component120Node23Box component120Node21Box component120Node22Box
    .k (125/32) (by rfl) (by rfl)
    component120Node21_sound component120Node22_sound

private noncomputable def component120Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (53/128), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component120Node24_sound : Sound component120Node24Box :=
  sound_of_literal_split component120Node24Box leaf5999Box leaf6000Box
    .chi (107/256) (by rfl) (by rfl)
    leaf5999FlatSound leaf6000FlatSound

private noncomputable def component120Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (53/128), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component120Node25_sound : Sound component120Node25Box :=
  sound_of_literal_split component120Node25Box leaf6001Box leaf6002Box
    .chi (107/256) (by rfl) (by rfl)
    leaf6001FlatSound leaf6002FlatSound

private noncomputable def component120Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (53/128), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component120Node26_sound : Sound component120Node26Box :=
  sound_of_literal_split component120Node26Box component120Node24Box component120Node25Box
    .k (125/32) (by rfl) (by rfl)
    component120Node24_sound component120Node25_sound

private noncomputable def component120Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (13/32), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component120Node27_sound : Sound component120Node27Box :=
  sound_of_literal_split component120Node27Box component120Node23Box component120Node26Box
    .chi (53/128) (by rfl) (by rfl)
    component120Node23_sound component120Node26_sound

private noncomputable def component120Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (13/32), chiHi := (53/128) }

set_option maxRecDepth 1000000 in
private theorem component120Node28_sound : Sound component120Node28Box :=
  sound_of_literal_split component120Node28Box leaf6003Box leaf6004Box
    .chi (105/256) (by rfl) (by rfl)
    leaf6003FlatSound leaf6004FlatSound

private noncomputable def component120Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (13/32), chiHi := (53/128) }

set_option maxRecDepth 1000000 in
private theorem component120Node29_sound : Sound component120Node29Box :=
  sound_of_literal_split component120Node29Box leaf6005Box leaf6006Box
    .chi (105/256) (by rfl) (by rfl)
    leaf6005FlatSound leaf6006FlatSound

private noncomputable def component120Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (13/32), chiHi := (53/128) }

set_option maxRecDepth 1000000 in
private theorem component120Node30_sound : Sound component120Node30Box :=
  sound_of_literal_split component120Node30Box component120Node28Box component120Node29Box
    .k (127/32) (by rfl) (by rfl)
    component120Node28_sound component120Node29_sound

private noncomputable def component120Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (53/128), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component120Node31_sound : Sound component120Node31Box :=
  sound_of_literal_split component120Node31Box leaf6007Box leaf6008Box
    .chi (107/256) (by rfl) (by rfl)
    leaf6007FlatSound leaf6008FlatSound

private noncomputable def component120Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (53/128), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component120Node32_sound : Sound component120Node32Box :=
  sound_of_literal_split component120Node32Box leaf6009Box leaf6010Box
    .chi (107/256) (by rfl) (by rfl)
    leaf6009FlatSound leaf6010FlatSound

private noncomputable def component120Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (53/128), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component120Node33_sound : Sound component120Node33Box :=
  sound_of_literal_split component120Node33Box component120Node31Box component120Node32Box
    .k (127/32) (by rfl) (by rfl)
    component120Node31_sound component120Node32_sound

private noncomputable def component120Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (13/32), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component120Node34_sound : Sound component120Node34Box :=
  sound_of_literal_split component120Node34Box component120Node30Box component120Node33Box
    .chi (53/128) (by rfl) (by rfl)
    component120Node30_sound component120Node33_sound

private noncomputable def component120Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (13/32), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component120Node35_sound : Sound component120Node35Box :=
  sound_of_literal_split component120Node35Box component120Node27Box component120Node34Box
    .k (63/16) (by rfl) (by rfl)
    component120Node27_sound component120Node34_sound

private noncomputable def component120Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (27/64), chiHi := (55/128) }

set_option maxRecDepth 1000000 in
private theorem component120Node36_sound : Sound component120Node36Box :=
  sound_of_literal_split component120Node36Box leaf6012Box leaf6013Box
    .chi (109/256) (by rfl) (by rfl)
    leaf6012FlatSound leaf6013FlatSound

private noncomputable def component120Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (27/64), chiHi := (55/128) }

set_option maxRecDepth 1000000 in
private theorem component120Node37_sound : Sound component120Node37Box :=
  sound_of_literal_split component120Node37Box leaf6011Box component120Node36Box
    .k (125/32) (by rfl) (by rfl)
    leaf6011FlatSound component120Node36_sound

private noncomputable def component120Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (55/128), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component120Node38_sound : Sound component120Node38Box :=
  sound_of_literal_split component120Node38Box leaf6014Box leaf6015Box
    .k (125/32) (by rfl) (by rfl)
    leaf6014FlatSound leaf6015FlatSound

private noncomputable def component120Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (27/64), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component120Node39_sound : Sound component120Node39Box :=
  sound_of_literal_split component120Node39Box component120Node37Box component120Node38Box
    .chi (55/128) (by rfl) (by rfl)
    component120Node37_sound component120Node38_sound

private noncomputable def component120Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (27/64), chiHi := (55/128) }

set_option maxRecDepth 1000000 in
private theorem component120Node40_sound : Sound component120Node40Box :=
  sound_of_literal_split component120Node40Box leaf6016Box leaf6017Box
    .chi (109/256) (by rfl) (by rfl)
    leaf6016FlatSound leaf6017FlatSound

private noncomputable def component120Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (27/64), chiHi := (55/128) }

set_option maxRecDepth 1000000 in
private theorem component120Node41_sound : Sound component120Node41Box :=
  sound_of_literal_split component120Node41Box leaf6018Box leaf6019Box
    .chi (109/256) (by rfl) (by rfl)
    leaf6018FlatSound leaf6019FlatSound

private noncomputable def component120Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (27/64), chiHi := (55/128) }

set_option maxRecDepth 1000000 in
private theorem component120Node42_sound : Sound component120Node42Box :=
  sound_of_literal_split component120Node42Box component120Node40Box component120Node41Box
    .k (127/32) (by rfl) (by rfl)
    component120Node40_sound component120Node41_sound

private noncomputable def component120Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (55/128), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component120Node43_sound : Sound component120Node43Box :=
  sound_of_literal_split component120Node43Box leaf6021Box leaf6022Box
    .chi (111/256) (by rfl) (by rfl)
    leaf6021FlatSound leaf6022FlatSound

private noncomputable def component120Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (55/128), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component120Node44_sound : Sound component120Node44Box :=
  sound_of_literal_split component120Node44Box leaf6020Box component120Node43Box
    .k (127/32) (by rfl) (by rfl)
    leaf6020FlatSound component120Node43_sound

private noncomputable def component120Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (27/64), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component120Node45_sound : Sound component120Node45Box :=
  sound_of_literal_split component120Node45Box component120Node42Box component120Node44Box
    .chi (55/128) (by rfl) (by rfl)
    component120Node42_sound component120Node44_sound

private noncomputable def component120Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (27/64), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component120Node46_sound : Sound component120Node46Box :=
  sound_of_literal_split component120Node46Box component120Node39Box component120Node45Box
    .k (63/16) (by rfl) (by rfl)
    component120Node39_sound component120Node45_sound

private noncomputable def component120Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (13/32), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component120Node47_sound : Sound component120Node47Box :=
  sound_of_literal_split component120Node47Box component120Node35Box component120Node46Box
    .chi (27/64) (by rfl) (by rfl)
    component120Node35_sound component120Node46_sound

noncomputable def component120Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (4), chiLo := (13/32), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
theorem component120_sound : Sound component120Box :=
  sound_of_literal_split component120Box component120Node20Box component120Node47Box
    .k (31/8) (by rfl) (by rfl)
    component120Node20_sound component120Node47_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
