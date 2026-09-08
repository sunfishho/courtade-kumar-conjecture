import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch2
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

private noncomputable def leaf1974Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (5/32), chiHi := (21/128) }

private noncomputable def leaf1974Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435691/268435456) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717390848) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (394223895/268435456) }, upper := { exponent := 0, mantissa := (6133/4096) } }, logOuter := sk133LogOuterCertificate, logK := sk133LogKCertificate, logChi := chi111LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435884543/137434781696) } }, logDArg := sk133LogDArgCertificate }

private noncomputable def leaf1974InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1974LocalValidity :
    LeafFacts leaf1974Box leaf1974Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1974Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717390848) }) = true
      norm_num [leaf1974Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1974CertificateValid :
    WideCertificateValid leaf1974Box leaf1974Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk133ValidityFacts chi111ValidityFacts
    leaf1974LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1974CoverageChecked :
    coverageCheck (innerAD leaf1974Box) leaf1974InnerLog = true := by
  rfl'

private theorem leaf1974InnerLogValid :
    leaf1974InnerLog.Valid 8 (innerAD leaf1974Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1974CoverageChecked

private noncomputable def leaf1974InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629215/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1974InputLogOnePlusV_eq :
    leaf1974InputLogOnePlusV = outerEnclosure 24
      (leaf1974Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1974RoundedFacts : LeafRoundedFacts 8
    leaf1974Certificate.logOnePlusV leaf1974InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1974InputLogOnePlusV_eq }

private noncomputable def leaf1974Inputs : Inputs :=
  inputsOfCaches globalInput sk133RoundedInputs
    chi111InputQChi innerPair34Input
    leaf1974InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1974LowerChecked :
    lowerCheck 24 leaf1974Box leaf1974Inputs = true := by
  rfl'

private theorem leaf1974CoversExact : CoversExact 8
    leaf1974Box leaf1974Certificate leaf1974InnerLog leaf1974Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk133RoundedFacts chi111RoundedFacts
    innerPair34RoundedFacts leaf1974RoundedFacts (by rfl)

private theorem leaf1974FlatSound : Sound leaf1974Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1974CertificateValid
    leaf1974InnerLogValid leaf1974CoversExact leaf1974LowerChecked

private noncomputable def leaf1975Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (5/32), chiHi := (41/256) }

private noncomputable def leaf1975Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871189/536870912) }, vSqrt := { lower := (65529/65536), upper := (13743698739/13743483904) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (791102029/536870912) }, upper := { exponent := 0, mantissa := (6105/4096) } }, logOuter := sk134LogOuterCertificate, logK := sk134LogKCertificate, logChi := chi183LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (27487182643/27486967808) } }, logDArg := sk134LogDArgCertificate }

private noncomputable def leaf1975InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1975LocalValidity :
    LeafFacts leaf1975Box leaf1975Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1975Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (13743698739/13743483904) }) = true
      norm_num [leaf1975Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1975CertificateValid :
    WideCertificateValid leaf1975Box leaf1975Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk134ValidityFacts chi183ValidityFacts
    leaf1975LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1975CoverageChecked :
    coverageCheck (innerAD leaf1975Box) leaf1975InnerLog = true := by
  rfl'

private theorem leaf1975InnerLogValid :
    leaf1975InnerLog.Valid 8 (innerAD leaf1975Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1975CoverageChecked

private noncomputable def leaf1975InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907303/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1975InputLogOnePlusV_eq :
    leaf1975InputLogOnePlusV = outerEnclosure 24
      (leaf1975Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1975RoundedFacts : LeafRoundedFacts 8
    leaf1975Certificate.logOnePlusV leaf1975InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1975InputLogOnePlusV_eq }

private noncomputable def leaf1975Inputs : Inputs :=
  inputsOfCaches globalInput sk134RoundedInputs
    chi183InputQChi innerPair34Input
    leaf1975InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1975LowerChecked :
    lowerCheck 24 leaf1975Box leaf1975Inputs = true := by
  rfl'

private theorem leaf1975CoversExact : CoversExact 8
    leaf1975Box leaf1975Certificate leaf1975InnerLog leaf1975Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk134RoundedFacts chi183RoundedFacts
    innerPair34RoundedFacts leaf1975RoundedFacts (by rfl)

private theorem leaf1975FlatSound : Sound leaf1975Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1975CertificateValid
    leaf1975InnerLogValid leaf1975CoversExact leaf1975LowerChecked

private noncomputable def leaf1976Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (41/256), chiHi := (21/128) }

private noncomputable def leaf1976Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871191/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717369344) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (797458631/536870912) }, upper := { exponent := 0, mantissa := (3077/2048) } }, logOuter := sk134LogOuterCertificate, logK := sk134LogKCertificate, logChi := chi184LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435863039/137434738688) } }, logDArg := sk134LogDArgCertificate }

private noncomputable def leaf1976InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf1976LocalValidity :
    LeafFacts leaf1976Box leaf1976Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1976Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717369344) }) = true
      norm_num [leaf1976Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1976CertificateValid :
    WideCertificateValid leaf1976Box leaf1976Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk134ValidityFacts chi184ValidityFacts
    leaf1976LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1976CoverageChecked :
    coverageCheck (innerAD leaf1976Box) leaf1976InnerLog = true := by
  rfl'

private theorem leaf1976InnerLogValid :
    leaf1976InnerLog.Valid 8 (innerAD leaf1976Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf1976CoverageChecked

private noncomputable def leaf1976InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814609/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1976InputLogOnePlusV_eq :
    leaf1976InputLogOnePlusV = outerEnclosure 24
      (leaf1976Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1976RoundedFacts : LeafRoundedFacts 8
    leaf1976Certificate.logOnePlusV leaf1976InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1976InputLogOnePlusV_eq }

private noncomputable def leaf1976Inputs : Inputs :=
  inputsOfCaches globalInput sk134RoundedInputs
    chi184InputQChi innerPair35Input
    leaf1976InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1976LowerChecked :
    lowerCheck 24 leaf1976Box leaf1976Inputs = true := by
  rfl'

private theorem leaf1976CoversExact : CoversExact 8
    leaf1976Box leaf1976Certificate leaf1976InnerLog leaf1976Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk134RoundedFacts chi184RoundedFacts
    innerPair35RoundedFacts leaf1976RoundedFacts (by rfl)

private theorem leaf1976FlatSound : Sound leaf1976Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1976CertificateValid
    leaf1976InnerLogValid leaf1976CoversExact leaf1976LowerChecked

private noncomputable def leaf1977Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (21/128), chiHi := (43/256) }

private noncomputable def leaf1977Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871191/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717341184) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (801062891/536870912) }, upper := { exponent := 0, mantissa := (12363/8192) } }, logOuter := sk133LogOuterCertificate, logK := sk133LogKCertificate, logChi := chi185LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435834879/137434682368) } }, logDArg := sk133LogDArgCertificate }

private noncomputable def leaf1977InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf1977LocalValidity :
    LeafFacts leaf1977Box leaf1977Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1977Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717341184) }) = true
      norm_num [leaf1977Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1977CertificateValid :
    WideCertificateValid leaf1977Box leaf1977Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk133ValidityFacts chi185ValidityFacts
    leaf1977LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1977CoverageChecked :
    coverageCheck (innerAD leaf1977Box) leaf1977InnerLog = true := by
  rfl'

private theorem leaf1977InnerLogValid :
    leaf1977InnerLog.Valid 8 (innerAD leaf1977Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf1977CoverageChecked

private noncomputable def leaf1977InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629221/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1977InputLogOnePlusV_eq :
    leaf1977InputLogOnePlusV = outerEnclosure 24
      (leaf1977Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1977RoundedFacts : LeafRoundedFacts 8
    leaf1977Certificate.logOnePlusV leaf1977InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1977InputLogOnePlusV_eq }

private noncomputable def leaf1977Inputs : Inputs :=
  inputsOfCaches globalInput sk133RoundedInputs
    chi185InputQChi innerPair35Input
    leaf1977InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1977LowerChecked :
    lowerCheck 24 leaf1977Box leaf1977Inputs = true := by
  rfl'

private theorem leaf1977CoversExact : CoversExact 8
    leaf1977Box leaf1977Certificate leaf1977InnerLog leaf1977Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk133RoundedFacts chi185RoundedFacts
    innerPair35RoundedFacts leaf1977RoundedFacts (by rfl)

private theorem leaf1977FlatSound : Sound leaf1977Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1977CertificateValid
    leaf1977InnerLogValid leaf1977CoversExact leaf1977LowerChecked

private noncomputable def leaf1978Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (43/256), chiHi := (11/64) }

private noncomputable def leaf1978Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871193/536870912) }, vSqrt := { lower := (65529/65536), upper := (4581232913/4581152768) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (807353961/536870912) }, upper := { exponent := 0, mantissa := (3115/2048) } }, logOuter := sk133LogOuterCertificate, logK := sk133LogKCertificate, logChi := chi186LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9162385681/9162305536) } }, logDArg := sk133LogDArgCertificate }

private noncomputable def leaf1978InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf1978LocalValidity :
    LeafFacts leaf1978Box leaf1978Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1978Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4581232913/4581152768) }) = true
      norm_num [leaf1978Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1978CertificateValid :
    WideCertificateValid leaf1978Box leaf1978Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk133ValidityFacts chi186ValidityFacts
    leaf1978LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1978CoverageChecked :
    coverageCheck (innerAD leaf1978Box) leaf1978InnerLog = true := by
  rfl'

private theorem leaf1978InnerLogValid :
    leaf1978InnerLog.Valid 8 (innerAD leaf1978Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf1978CoverageChecked

private noncomputable def leaf1978InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629227/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1978InputLogOnePlusV_eq :
    leaf1978InputLogOnePlusV = outerEnclosure 24
      (leaf1978Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1978RoundedFacts : LeafRoundedFacts 8
    leaf1978Certificate.logOnePlusV leaf1978InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1978InputLogOnePlusV_eq }

private noncomputable def leaf1978Inputs : Inputs :=
  inputsOfCaches globalInput sk133RoundedInputs
    chi186InputQChi innerPair40Input
    leaf1978InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1978LowerChecked :
    lowerCheck 24 leaf1978Box leaf1978Inputs = true := by
  rfl'

private theorem leaf1978CoversExact : CoversExact 8
    leaf1978Box leaf1978Certificate leaf1978InnerLog leaf1978Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk133RoundedFacts chi186RoundedFacts
    innerPair40RoundedFacts leaf1978RoundedFacts (by rfl)

private theorem leaf1978FlatSound : Sound leaf1978Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1978CertificateValid
    leaf1978InnerLogValid leaf1978CoversExact leaf1978LowerChecked

private noncomputable def leaf1979Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (21/128), chiHi := (43/256) }

private noncomputable def leaf1979Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871193/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905773056) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (803815233/536870912) }, upper := { exponent := 0, mantissa := (6203/4096) } }, logOuter := sk134LogOuterCertificate, logK := sk134LogKCertificate, logChi := chi185LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811937621/45811546112) } }, logDArg := sk134LogDArgCertificate }

private noncomputable def leaf1979InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf1979LocalValidity :
    LeafFacts leaf1979Box leaf1979Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1979Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905773056) }) = true
      norm_num [leaf1979Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1979CertificateValid :
    WideCertificateValid leaf1979Box leaf1979Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk134ValidityFacts chi185ValidityFacts
    leaf1979LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1979CoverageChecked :
    coverageCheck (innerAD leaf1979Box) leaf1979InnerLog = true := by
  rfl'

private theorem leaf1979InnerLogValid :
    leaf1979InnerLog.Valid 8 (innerAD leaf1979Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf1979CoverageChecked

private noncomputable def leaf1979InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453653/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1979InputLogOnePlusV_eq :
    leaf1979InputLogOnePlusV = outerEnclosure 24
      (leaf1979Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1979RoundedFacts : LeafRoundedFacts 8
    leaf1979Certificate.logOnePlusV leaf1979InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1979InputLogOnePlusV_eq }

private noncomputable def leaf1979Inputs : Inputs :=
  inputsOfCaches globalInput sk134RoundedInputs
    chi185InputQChi innerPair35Input
    leaf1979InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1979LowerChecked :
    lowerCheck 24 leaf1979Box leaf1979Inputs = true := by
  rfl'

private theorem leaf1979CoversExact : CoversExact 8
    leaf1979Box leaf1979Certificate leaf1979InnerLog leaf1979Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk134RoundedFacts chi185RoundedFacts
    innerPair35RoundedFacts leaf1979RoundedFacts (by rfl)

private theorem leaf1979FlatSound : Sound leaf1979Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1979CertificateValid
    leaf1979InnerLogValid leaf1979CoversExact leaf1979LowerChecked

private noncomputable def leaf1980Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (43/256), chiHi := (11/64) }

private noncomputable def leaf1980Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871195/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717268992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (810171835/536870912) }, upper := { exponent := 0, mantissa := (1563/1024) } }, logOuter := sk134LogOuterCertificate, logK := sk134LogKCertificate, logChi := chi186LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435762687/137434537984) } }, logDArg := sk134LogDArgCertificate }

private noncomputable def leaf1980InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf1980LocalValidity :
    LeafFacts leaf1980Box leaf1980Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1980Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717268992) }) = true
      norm_num [leaf1980Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1980CertificateValid :
    WideCertificateValid leaf1980Box leaf1980Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk134ValidityFacts chi186ValidityFacts
    leaf1980LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1980CoverageChecked :
    coverageCheck (innerAD leaf1980Box) leaf1980InnerLog = true := by
  rfl'

private theorem leaf1980InnerLogValid :
    leaf1980InnerLog.Valid 8 (innerAD leaf1980Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf1980CoverageChecked

private noncomputable def leaf1980InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814615/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1980InputLogOnePlusV_eq :
    leaf1980InputLogOnePlusV = outerEnclosure 24
      (leaf1980Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1980RoundedFacts : LeafRoundedFacts 8
    leaf1980Certificate.logOnePlusV leaf1980InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1980InputLogOnePlusV_eq }

private noncomputable def leaf1980Inputs : Inputs :=
  inputsOfCaches globalInput sk134RoundedInputs
    chi186InputQChi innerPair40Input
    leaf1980InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1980LowerChecked :
    lowerCheck 24 leaf1980Box leaf1980Inputs = true := by
  rfl'

private theorem leaf1980CoversExact : CoversExact 8
    leaf1980Box leaf1980Certificate leaf1980InnerLog leaf1980Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk134RoundedFacts chi186RoundedFacts
    innerPair40RoundedFacts leaf1980RoundedFacts (by rfl)

private theorem leaf1980FlatSound : Sound leaf1980Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1980CertificateValid
    leaf1980InnerLogValid leaf1980CoversExact leaf1980LowerChecked

private noncomputable def leaf1981Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (5/32), chiHi := (41/256) }

private noncomputable def leaf1981Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871191/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717398528) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (793723307/536870912) }, upper := { exponent := 0, mantissa := (12251/8192) } }, logOuter := sk135LogOuterCertificate, logK := sk135LogKCertificate, logChi := chi183LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435892223/137434797056) } }, logDArg := sk135LogDArgCertificate }

private noncomputable def leaf1981InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1981LocalValidity :
    LeafFacts leaf1981Box leaf1981Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1981Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717398528) }) = true
      norm_num [leaf1981Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1981CertificateValid :
    WideCertificateValid leaf1981Box leaf1981Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk135ValidityFacts chi183ValidityFacts
    leaf1981LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1981CoverageChecked :
    coverageCheck (innerAD leaf1981Box) leaf1981InnerLog = true := by
  rfl'

private theorem leaf1981InnerLogValid :
    leaf1981InnerLog.Valid 8 (innerAD leaf1981Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1981CoverageChecked

private noncomputable def leaf1981InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814607/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1981InputLogOnePlusV_eq :
    leaf1981InputLogOnePlusV = outerEnclosure 24
      (leaf1981Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1981RoundedFacts : LeafRoundedFacts 8
    leaf1981Certificate.logOnePlusV leaf1981InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1981InputLogOnePlusV_eq }

private noncomputable def leaf1981Inputs : Inputs :=
  inputsOfCaches globalInput sk135RoundedInputs
    chi183InputQChi innerPair34Input
    leaf1981InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1981LowerChecked :
    lowerCheck 24 leaf1981Box leaf1981Inputs = true := by
  rfl'

private theorem leaf1981CoversExact : CoversExact 8
    leaf1981Box leaf1981Certificate leaf1981InnerLog leaf1981Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk135RoundedFacts chi183RoundedFacts
    innerPair34RoundedFacts leaf1981RoundedFacts (by rfl)

private theorem leaf1981FlatSound : Sound leaf1981Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1981CertificateValid
    leaf1981InnerLogValid leaf1981CoversExact leaf1981LowerChecked

private noncomputable def leaf1982Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (41/256), chiHi := (21/128) }

private noncomputable def leaf1982Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871193/536870912) }, vSqrt := { lower := (65529/65536), upper := (13743698739/13743469568) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (800145441/536870912) }, upper := { exponent := 0, mantissa := (6175/4096) } }, logOuter := sk135LogOuterCertificate, logK := sk135LogKCertificate, logChi := chi184LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (27487168307/27486939136) } }, logDArg := sk135LogDArgCertificate }

private noncomputable def leaf1982InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf1982LocalValidity :
    LeafFacts leaf1982Box leaf1982Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1982Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (13743698739/13743469568) }) = true
      norm_num [leaf1982Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1982CertificateValid :
    WideCertificateValid leaf1982Box leaf1982Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk135ValidityFacts chi184ValidityFacts
    leaf1982LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1982CoverageChecked :
    coverageCheck (innerAD leaf1982Box) leaf1982InnerLog = true := by
  rfl'

private theorem leaf1982InnerLogValid :
    leaf1982InnerLog.Valid 8 (innerAD leaf1982Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf1982CoverageChecked

private noncomputable def leaf1982InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629221/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1982InputLogOnePlusV_eq :
    leaf1982InputLogOnePlusV = outerEnclosure 24
      (leaf1982Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1982RoundedFacts : LeafRoundedFacts 8
    leaf1982Certificate.logOnePlusV leaf1982InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1982InputLogOnePlusV_eq }

private noncomputable def leaf1982Inputs : Inputs :=
  inputsOfCaches globalInput sk135RoundedInputs
    chi184InputQChi innerPair35Input
    leaf1982InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1982LowerChecked :
    lowerCheck 24 leaf1982Box leaf1982Inputs = true := by
  rfl'

private theorem leaf1982CoversExact : CoversExact 8
    leaf1982Box leaf1982Certificate leaf1982InnerLog leaf1982Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk135RoundedFacts chi184RoundedFacts
    innerPair35RoundedFacts leaf1982RoundedFacts (by rfl)

private theorem leaf1982FlatSound : Sound leaf1982Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1982CertificateValid
    leaf1982InnerLogValid leaf1982CoversExact leaf1982LowerChecked

private noncomputable def leaf1983Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (5/32), chiHi := (41/256) }

private noncomputable def leaf1983Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871193/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905792512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (796344585/536870912) }, upper := { exponent := 0, mantissa := (3073/2048) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi183LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811957077/45811585024) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf1983InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf1983LocalValidity :
    LeafFacts leaf1983Box leaf1983Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1983Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905792512) }) = true
      norm_num [leaf1983Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1983CertificateValid :
    WideCertificateValid leaf1983Box leaf1983Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi183ValidityFacts
    leaf1983LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1983CoverageChecked :
    coverageCheck (innerAD leaf1983Box) leaf1983InnerLog = true := by
  rfl'

private theorem leaf1983InnerLogValid :
    leaf1983InnerLog.Valid 8 (innerAD leaf1983Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf1983CoverageChecked

private noncomputable def leaf1983InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629217/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1983InputLogOnePlusV_eq :
    leaf1983InputLogOnePlusV = outerEnclosure 24
      (leaf1983Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1983RoundedFacts : LeafRoundedFacts 8
    leaf1983Certificate.logOnePlusV leaf1983InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1983InputLogOnePlusV_eq }

private noncomputable def leaf1983Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi183InputQChi innerPair35Input
    leaf1983InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1983LowerChecked :
    lowerCheck 24 leaf1983Box leaf1983Inputs = true := by
  rfl'

private theorem leaf1983CoversExact : CoversExact 8
    leaf1983Box leaf1983Certificate leaf1983InnerLog leaf1983Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi183RoundedFacts
    innerPair35RoundedFacts leaf1983RoundedFacts (by rfl)

private theorem leaf1983FlatSound : Sound leaf1983Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1983CertificateValid
    leaf1983InnerLogValid leaf1983CoversExact leaf1983LowerChecked

private noncomputable def leaf1984Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (41/256), chiHi := (21/128) }

private noncomputable def leaf1984Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871195/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717326336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (802832251/536870912) }, upper := { exponent := 0, mantissa := (1549/1024) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi184LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435820031/137434652672) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf1984InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf1984LocalValidity :
    LeafFacts leaf1984Box leaf1984Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1984Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717326336) }) = true
      norm_num [leaf1984Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1984CertificateValid :
    WideCertificateValid leaf1984Box leaf1984Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi184ValidityFacts
    leaf1984LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1984CoverageChecked :
    coverageCheck (innerAD leaf1984Box) leaf1984InnerLog = true := by
  rfl'

private theorem leaf1984InnerLogValid :
    leaf1984InnerLog.Valid 8 (innerAD leaf1984Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf1984CoverageChecked

private noncomputable def leaf1984InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629223/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1984InputLogOnePlusV_eq :
    leaf1984InputLogOnePlusV = outerEnclosure 24
      (leaf1984Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1984RoundedFacts : LeafRoundedFacts 8
    leaf1984Certificate.logOnePlusV leaf1984InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1984InputLogOnePlusV_eq }

private noncomputable def leaf1984Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi184InputQChi innerPair35Input
    leaf1984InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1984LowerChecked :
    lowerCheck 24 leaf1984Box leaf1984Inputs = true := by
  rfl'

private theorem leaf1984CoversExact : CoversExact 8
    leaf1984Box leaf1984Certificate leaf1984InnerLog leaf1984Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi184RoundedFacts
    innerPair35RoundedFacts leaf1984RoundedFacts (by rfl)

private theorem leaf1984FlatSound : Sound leaf1984Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1984CertificateValid
    leaf1984InnerLogValid leaf1984CoversExact leaf1984LowerChecked

private noncomputable def leaf1985Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (21/128), chiHi := (43/256) }

private noncomputable def leaf1985Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871195/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717297152) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (806567575/536870912) }, upper := { exponent := 0, mantissa := (12449/8192) } }, logOuter := sk135LogOuterCertificate, logK := sk135LogKCertificate, logChi := chi185LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435790847/137434594304) } }, logDArg := sk135LogDArgCertificate }

private noncomputable def leaf1985InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf1985LocalValidity :
    LeafFacts leaf1985Box leaf1985Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1985Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717297152) }) = true
      norm_num [leaf1985Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1985CertificateValid :
    WideCertificateValid leaf1985Box leaf1985Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk135ValidityFacts chi185ValidityFacts
    leaf1985LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1985CoverageChecked :
    coverageCheck (innerAD leaf1985Box) leaf1985InnerLog = true := by
  rfl'

private theorem leaf1985InnerLogValid :
    leaf1985InnerLog.Valid 8 (innerAD leaf1985Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf1985CoverageChecked

private noncomputable def leaf1985InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629227/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1985InputLogOnePlusV_eq :
    leaf1985InputLogOnePlusV = outerEnclosure 24
      (leaf1985Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1985RoundedFacts : LeafRoundedFacts 8
    leaf1985Certificate.logOnePlusV leaf1985InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1985InputLogOnePlusV_eq }

private noncomputable def leaf1985Inputs : Inputs :=
  inputsOfCaches globalInput sk135RoundedInputs
    chi185InputQChi innerPair40Input
    leaf1985InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1985LowerChecked :
    lowerCheck 24 leaf1985Box leaf1985Inputs = true := by
  rfl'

private theorem leaf1985CoversExact : CoversExact 8
    leaf1985Box leaf1985Certificate leaf1985InnerLog leaf1985Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk135RoundedFacts chi185RoundedFacts
    innerPair40RoundedFacts leaf1985RoundedFacts (by rfl)

private theorem leaf1985FlatSound : Sound leaf1985Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1985CertificateValid
    leaf1985InnerLogValid leaf1985CoversExact leaf1985LowerChecked

private noncomputable def leaf1986Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (43/256), chiHi := (11/64) }

private noncomputable def leaf1986Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871197/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717246464) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (812989709/536870912) }, upper := { exponent := 0, mantissa := (3137/2048) } }, logOuter := sk135LogOuterCertificate, logK := sk135LogKCertificate, logChi := chi186LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435740159/137434492928) } }, logDArg := sk135LogDArgCertificate }

private noncomputable def leaf1986InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf1986LocalValidity :
    LeafFacts leaf1986Box leaf1986Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1986Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717246464) }) = true
      norm_num [leaf1986Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1986CertificateValid :
    WideCertificateValid leaf1986Box leaf1986Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk135ValidityFacts chi186ValidityFacts
    leaf1986LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1986CoverageChecked :
    coverageCheck (innerAD leaf1986Box) leaf1986InnerLog = true := by
  rfl'

private theorem leaf1986InnerLogValid :
    leaf1986InnerLog.Valid 8 (innerAD leaf1986Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf1986CoverageChecked

private noncomputable def leaf1986InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629233/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1986InputLogOnePlusV_eq :
    leaf1986InputLogOnePlusV = outerEnclosure 24
      (leaf1986Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1986RoundedFacts : LeafRoundedFacts 8
    leaf1986Certificate.logOnePlusV leaf1986InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1986InputLogOnePlusV_eq }

private noncomputable def leaf1986Inputs : Inputs :=
  inputsOfCaches globalInput sk135RoundedInputs
    chi186InputQChi innerPair40Input
    leaf1986InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1986LowerChecked :
    lowerCheck 24 leaf1986Box leaf1986Inputs = true := by
  rfl'

private theorem leaf1986CoversExact : CoversExact 8
    leaf1986Box leaf1986Certificate leaf1986InnerLog leaf1986Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk135RoundedFacts chi186RoundedFacts
    innerPair40RoundedFacts leaf1986RoundedFacts (by rfl)

private theorem leaf1986FlatSound : Sound leaf1986Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1986CertificateValid
    leaf1986InnerLogValid leaf1986CoversExact leaf1986LowerChecked

private noncomputable def leaf1987Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (21/128), chiHi := (43/256) }

private noncomputable def leaf1987Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871197/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717275136) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (809319917/536870912) }, upper := { exponent := 0, mantissa := (3123/2048) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi185LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435768831/137434550272) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf1987InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf1987LocalValidity :
    LeafFacts leaf1987Box leaf1987Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1987Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717275136) }) = true
      norm_num [leaf1987Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1987CertificateValid :
    WideCertificateValid leaf1987Box leaf1987Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi185ValidityFacts
    leaf1987LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1987CoverageChecked :
    coverageCheck (innerAD leaf1987Box) leaf1987InnerLog = true := by
  rfl'

private theorem leaf1987InnerLogValid :
    leaf1987InnerLog.Valid 8 (innerAD leaf1987Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf1987CoverageChecked

private noncomputable def leaf1987InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629229/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1987InputLogOnePlusV_eq :
    leaf1987InputLogOnePlusV = outerEnclosure 24
      (leaf1987Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1987RoundedFacts : LeafRoundedFacts 8
    leaf1987Certificate.logOnePlusV leaf1987InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1987InputLogOnePlusV_eq }

private noncomputable def leaf1987Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi185InputQChi innerPair40Input
    leaf1987InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1987LowerChecked :
    lowerCheck 24 leaf1987Box leaf1987Inputs = true := by
  rfl'

private theorem leaf1987CoversExact : CoversExact 8
    leaf1987Box leaf1987Certificate leaf1987InnerLog leaf1987Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi185RoundedFacts
    innerPair40RoundedFacts leaf1987RoundedFacts (by rfl)

private theorem leaf1987FlatSound : Sound leaf1987Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1987CertificateValid
    leaf1987InnerLogValid leaf1987CoversExact leaf1987LowerChecked

private noncomputable def leaf1988Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (43/256), chiHi := (11/64) }

private noncomputable def leaf1988Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871199/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905741312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (815807583/536870912) }, upper := { exponent := 0, mantissa := (787/512) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi186LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811905877/45811482624) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf1988InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf1988LocalValidity :
    LeafFacts leaf1988Box leaf1988Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1988Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905741312) }) = true
      norm_num [leaf1988Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1988CertificateValid :
    WideCertificateValid leaf1988Box leaf1988Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi186ValidityFacts
    leaf1988LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1988CoverageChecked :
    coverageCheck (innerAD leaf1988Box) leaf1988InnerLog = true := by
  rfl'

private theorem leaf1988InnerLogValid :
    leaf1988InnerLog.Valid 8 (innerAD leaf1988Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf1988CoverageChecked

private noncomputable def leaf1988InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907309/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1988InputLogOnePlusV_eq :
    leaf1988InputLogOnePlusV = outerEnclosure 24
      (leaf1988Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1988RoundedFacts : LeafRoundedFacts 8
    leaf1988Certificate.logOnePlusV leaf1988InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1988InputLogOnePlusV_eq }

private noncomputable def leaf1988Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi186InputQChi innerPair40Input
    leaf1988InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1988LowerChecked :
    lowerCheck 24 leaf1988Box leaf1988Inputs = true := by
  rfl'

private theorem leaf1988CoversExact : CoversExact 8
    leaf1988Box leaf1988Certificate leaf1988InnerLog leaf1988Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi186RoundedFacts
    innerPair40RoundedFacts leaf1988RoundedFacts (by rfl)

private theorem leaf1988FlatSound : Sound leaf1988Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1988CertificateValid
    leaf1988InnerLogValid leaf1988CoversExact leaf1988LowerChecked

private noncomputable def leaf1989Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (11/64), chiHi := (45/256) }

private noncomputable def leaf1989Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871195/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717241856) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (813645031/536870912) }, upper := { exponent := 0, mantissa := (12557/8192) } }, logOuter := sk133LogOuterCertificate, logK := sk133LogKCertificate, logChi := chi133LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435735551/137434483712) } }, logDArg := sk133LogDArgCertificate }

private noncomputable def leaf1989InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf1989LocalValidity :
    LeafFacts leaf1989Box leaf1989Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1989Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717241856) }) = true
      norm_num [leaf1989Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1989CertificateValid :
    WideCertificateValid leaf1989Box leaf1989Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk133ValidityFacts chi133ValidityFacts
    leaf1989LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1989CoverageChecked :
    coverageCheck (innerAD leaf1989Box) leaf1989InnerLog = true := by
  rfl'

private theorem leaf1989InnerLogValid :
    leaf1989InnerLog.Valid 8 (innerAD leaf1989Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf1989CoverageChecked

private noncomputable def leaf1989InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814617/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1989InputLogOnePlusV_eq :
    leaf1989InputLogOnePlusV = outerEnclosure 24
      (leaf1989Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1989RoundedFacts : LeafRoundedFacts 8
    leaf1989Certificate.logOnePlusV leaf1989InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1989InputLogOnePlusV_eq }

private noncomputable def leaf1989Inputs : Inputs :=
  inputsOfCaches globalInput sk133RoundedInputs
    chi133InputQChi innerPair40Input
    leaf1989InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1989LowerChecked :
    lowerCheck 24 leaf1989Box leaf1989Inputs = true := by
  rfl'

private theorem leaf1989CoversExact : CoversExact 8
    leaf1989Box leaf1989Certificate leaf1989InnerLog leaf1989Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk133RoundedFacts chi133RoundedFacts
    innerPair40RoundedFacts leaf1989RoundedFacts (by rfl)

private theorem leaf1989FlatSound : Sound leaf1989Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1989CertificateValid
    leaf1989InnerLogValid leaf1989CoversExact leaf1989LowerChecked

private noncomputable def leaf1990Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (45/256), chiHi := (23/128) }

private noncomputable def leaf1990Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871197/536870912) }, vSqrt := { lower := (65529/65536), upper := (4042264335/4042187776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (819936101/536870912) }, upper := { exponent := 0, mantissa := (6327/4096) } }, logOuter := sk133LogOuterCertificate, logK := sk133LogKCertificate, logChi := chi134LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (8084452111/8084375552) } }, logDArg := sk133LogDArgCertificate }

private noncomputable def leaf1990InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf1990LocalValidity :
    LeafFacts leaf1990Box leaf1990Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1990Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4042264335/4042187776) }) = true
      norm_num [leaf1990Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1990CertificateValid :
    WideCertificateValid leaf1990Box leaf1990Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk133ValidityFacts chi134ValidityFacts
    leaf1990LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1990CoverageChecked :
    coverageCheck (innerAD leaf1990Box) leaf1990InnerLog = true := by
  rfl'

private theorem leaf1990InnerLogValid :
    leaf1990InnerLog.Valid 8 (innerAD leaf1990Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf1990CoverageChecked

private noncomputable def leaf1990InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453655/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1990InputLogOnePlusV_eq :
    leaf1990InputLogOnePlusV = outerEnclosure 24
      (leaf1990Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1990RoundedFacts : LeafRoundedFacts 8
    leaf1990Certificate.logOnePlusV leaf1990InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1990InputLogOnePlusV_eq }

private noncomputable def leaf1990Inputs : Inputs :=
  inputsOfCaches globalInput sk133RoundedInputs
    chi134InputQChi innerPair40Input
    leaf1990InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1990LowerChecked :
    lowerCheck 24 leaf1990Box leaf1990Inputs = true := by
  rfl'

private theorem leaf1990CoversExact : CoversExact 8
    leaf1990Box leaf1990Certificate leaf1990InnerLog leaf1990Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk133RoundedFacts chi134RoundedFacts
    innerPair40RoundedFacts leaf1990RoundedFacts (by rfl)

private theorem leaf1990FlatSound : Sound leaf1990Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1990CertificateValid
    leaf1990InnerLogValid leaf1990CoversExact leaf1990LowerChecked

private noncomputable def leaf1991Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (11/64), chiHi := (45/256) }

private noncomputable def leaf1991Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871197/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717218816) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (816528437/536870912) }, upper := { exponent := 0, mantissa := (6301/4096) } }, logOuter := sk134LogOuterCertificate, logK := sk134LogKCertificate, logChi := chi133LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435712511/137434437632) } }, logDArg := sk134LogDArgCertificate }

private noncomputable def leaf1991InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf1991LocalValidity :
    LeafFacts leaf1991Box leaf1991Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1991Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717218816) }) = true
      norm_num [leaf1991Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1991CertificateValid :
    WideCertificateValid leaf1991Box leaf1991Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk134ValidityFacts chi133ValidityFacts
    leaf1991LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1991CoverageChecked :
    coverageCheck (innerAD leaf1991Box) leaf1991InnerLog = true := by
  rfl'

private theorem leaf1991InnerLogValid :
    leaf1991InnerLog.Valid 8 (innerAD leaf1991Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf1991CoverageChecked

private noncomputable def leaf1991InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907309/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1991InputLogOnePlusV_eq :
    leaf1991InputLogOnePlusV = outerEnclosure 24
      (leaf1991Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1991RoundedFacts : LeafRoundedFacts 8
    leaf1991Certificate.logOnePlusV leaf1991InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1991InputLogOnePlusV_eq }

private noncomputable def leaf1991Inputs : Inputs :=
  inputsOfCaches globalInput sk134RoundedInputs
    chi133InputQChi innerPair40Input
    leaf1991InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1991LowerChecked :
    lowerCheck 24 leaf1991Box leaf1991Inputs = true := by
  rfl'

private theorem leaf1991CoversExact : CoversExact 8
    leaf1991Box leaf1991Certificate leaf1991InnerLog leaf1991Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk134RoundedFacts chi133RoundedFacts
    innerPair40RoundedFacts leaf1991RoundedFacts (by rfl)

private theorem leaf1991FlatSound : Sound leaf1991Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1991CertificateValid
    leaf1991InnerLogValid leaf1991CoversExact leaf1991LowerChecked

private noncomputable def leaf1992Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (45/256), chiHi := (23/128) }

private noncomputable def leaf1992Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871199/536870912) }, vSqrt := { lower := (65529/65536), upper := (4581232913/4581144576) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (822885039/536870912) }, upper := { exponent := 0, mantissa := (3175/2048) } }, logOuter := sk134LogOuterCertificate, logK := sk134LogKCertificate, logChi := chi134LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9162377489/9162289152) } }, logDArg := sk134LogDArgCertificate }

private noncomputable def leaf1992InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf1992LocalValidity :
    LeafFacts leaf1992Box leaf1992Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1992Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4581232913/4581144576) }) = true
      norm_num [leaf1992Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1992CertificateValid :
    WideCertificateValid leaf1992Box leaf1992Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk134ValidityFacts chi134ValidityFacts
    leaf1992LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1992CoverageChecked :
    coverageCheck (innerAD leaf1992Box) leaf1992InnerLog = true := by
  rfl'

private theorem leaf1992InnerLogValid :
    leaf1992InnerLog.Valid 8 (innerAD leaf1992Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf1992CoverageChecked

private noncomputable def leaf1992InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814621/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1992InputLogOnePlusV_eq :
    leaf1992InputLogOnePlusV = outerEnclosure 24
      (leaf1992Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1992RoundedFacts : LeafRoundedFacts 8
    leaf1992Certificate.logOnePlusV leaf1992InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1992InputLogOnePlusV_eq }

private noncomputable def leaf1992Inputs : Inputs :=
  inputsOfCaches globalInput sk134RoundedInputs
    chi134InputQChi innerPair40Input
    leaf1992InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1992LowerChecked :
    lowerCheck 24 leaf1992Box leaf1992Inputs = true := by
  rfl'

private theorem leaf1992CoversExact : CoversExact 8
    leaf1992Box leaf1992Certificate leaf1992InnerLog leaf1992Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk134RoundedFacts chi134RoundedFacts
    innerPair40RoundedFacts leaf1992RoundedFacts (by rfl)

private theorem leaf1992FlatSound : Sound leaf1992Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1992CertificateValid
    leaf1992InnerLogValid leaf1992CoversExact leaf1992LowerChecked

private noncomputable def leaf1993Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (23/128), chiHi := (47/256) }

private noncomputable def leaf1993Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871199/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905714176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (826227171/536870912) }, upper := { exponent := 0, mantissa := (12751/8192) } }, logOuter := sk133LogOuterCertificate, logK := sk133LogKCertificate, logChi := chi135LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811878741/45811428352) } }, logDArg := sk133LogDArgCertificate }

private noncomputable def leaf1993InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf1993LocalValidity :
    LeafFacts leaf1993Box leaf1993Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1993Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905714176) }) = true
      norm_num [leaf1993Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1993CertificateValid :
    WideCertificateValid leaf1993Box leaf1993Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk133ValidityFacts chi135ValidityFacts
    leaf1993LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1993CoverageChecked :
    coverageCheck (innerAD leaf1993Box) leaf1993InnerLog = true := by
  rfl'

private theorem leaf1993InnerLogValid :
    leaf1993InnerLog.Valid 8 (innerAD leaf1993Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf1993CoverageChecked

private noncomputable def leaf1993InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814623/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1993InputLogOnePlusV_eq :
    leaf1993InputLogOnePlusV = outerEnclosure 24
      (leaf1993Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1993RoundedFacts : LeafRoundedFacts 8
    leaf1993Certificate.logOnePlusV leaf1993InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1993InputLogOnePlusV_eq }

private noncomputable def leaf1993Inputs : Inputs :=
  inputsOfCaches globalInput sk133RoundedInputs
    chi135InputQChi innerPair40Input
    leaf1993InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1993LowerChecked :
    lowerCheck 24 leaf1993Box leaf1993Inputs = true := by
  rfl'

private theorem leaf1993CoversExact : CoversExact 8
    leaf1993Box leaf1993Certificate leaf1993InnerLog leaf1993Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk133RoundedFacts chi135RoundedFacts
    innerPair40RoundedFacts leaf1993RoundedFacts (by rfl)

private theorem leaf1993FlatSound : Sound leaf1993Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1993CertificateValid
    leaf1993InnerLogValid leaf1993CoversExact leaf1993LowerChecked

private noncomputable def leaf1994Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (47/256), chiHi := (3/16) }

private noncomputable def leaf1994Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871201/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717092864) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (832518241/536870912) }, upper := { exponent := 0, mantissa := (803/512) } }, logOuter := sk133LogOuterCertificate, logK := sk133LogKCertificate, logChi := chi136LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435586559/137434185728) } }, logDArg := sk133LogDArgCertificate }

private noncomputable def leaf1994InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf1994LocalValidity :
    LeafFacts leaf1994Box leaf1994Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1994Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717092864) }) = true
      norm_num [leaf1994Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1994CertificateValid :
    WideCertificateValid leaf1994Box leaf1994Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk133ValidityFacts chi136ValidityFacts
    leaf1994LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1994CoverageChecked :
    coverageCheck (innerAD leaf1994Box) leaf1994InnerLog = true := by
  rfl'

private theorem leaf1994InnerLogValid :
    leaf1994InnerLog.Valid 8 (innerAD leaf1994Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf1994CoverageChecked

private noncomputable def leaf1994InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907313/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1994InputLogOnePlusV_eq :
    leaf1994InputLogOnePlusV = outerEnclosure 24
      (leaf1994Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1994RoundedFacts : LeafRoundedFacts 8
    leaf1994Certificate.logOnePlusV leaf1994InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1994InputLogOnePlusV_eq }

private noncomputable def leaf1994Inputs : Inputs :=
  inputsOfCaches globalInput sk133RoundedInputs
    chi136InputQChi innerPair41Input
    leaf1994InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1994LowerChecked :
    lowerCheck 24 leaf1994Box leaf1994Inputs = true := by
  rfl'

private theorem leaf1994CoversExact : CoversExact 8
    leaf1994Box leaf1994Certificate leaf1994InnerLog leaf1994Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk133RoundedFacts chi136RoundedFacts
    innerPair41RoundedFacts leaf1994RoundedFacts (by rfl)

private theorem leaf1994FlatSound : Sound leaf1994Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1994CertificateValid
    leaf1994InnerLogValid leaf1994CoversExact leaf1994LowerChecked

private noncomputable def leaf1995Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (23/128), chiHi := (47/256) }

private noncomputable def leaf1995Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871201/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717118464) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (829241641/536870912) }, upper := { exponent := 0, mantissa := (6399/4096) } }, logOuter := sk134LogOuterCertificate, logK := sk134LogKCertificate, logChi := chi135LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435612159/137434236928) } }, logDArg := sk134LogDArgCertificate }

private noncomputable def leaf1995InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf1995LocalValidity :
    LeafFacts leaf1995Box leaf1995Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1995Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717118464) }) = true
      norm_num [leaf1995Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1995CertificateValid :
    WideCertificateValid leaf1995Box leaf1995Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk134ValidityFacts chi135ValidityFacts
    leaf1995LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1995CoverageChecked :
    coverageCheck (innerAD leaf1995Box) leaf1995InnerLog = true := by
  rfl'

private theorem leaf1995InnerLogValid :
    leaf1995InnerLog.Valid 8 (innerAD leaf1995Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf1995CoverageChecked

private noncomputable def leaf1995InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629249/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1995InputLogOnePlusV_eq :
    leaf1995InputLogOnePlusV = outerEnclosure 24
      (leaf1995Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1995RoundedFacts : LeafRoundedFacts 8
    leaf1995Certificate.logOnePlusV leaf1995InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1995InputLogOnePlusV_eq }

private noncomputable def leaf1995Inputs : Inputs :=
  inputsOfCaches globalInput sk134RoundedInputs
    chi135InputQChi innerPair40Input
    leaf1995InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1995LowerChecked :
    lowerCheck 24 leaf1995Box leaf1995Inputs = true := by
  rfl'

private theorem leaf1995CoversExact : CoversExact 8
    leaf1995Box leaf1995Certificate leaf1995InnerLog leaf1995Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk134RoundedFacts chi135RoundedFacts
    innerPair40RoundedFacts leaf1995RoundedFacts (by rfl)

private theorem leaf1995FlatSound : Sound leaf1995Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1995CertificateValid
    leaf1995InnerLogValid leaf1995CoversExact leaf1995LowerChecked

private noncomputable def leaf1996Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (47/256), chiHi := (3/16) }

private noncomputable def leaf1996Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871203/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717068288) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (835598243/536870912) }, upper := { exponent := 0, mantissa := (403/256) } }, logOuter := sk134LogOuterCertificate, logK := sk134LogKCertificate, logChi := chi136LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435561983/137434136576) } }, logDArg := sk134LogDArgCertificate }

private noncomputable def leaf1996InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf1996LocalValidity :
    LeafFacts leaf1996Box leaf1996Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1996Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717068288) }) = true
      norm_num [leaf1996Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1996CertificateValid :
    WideCertificateValid leaf1996Box leaf1996Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk134ValidityFacts chi136ValidityFacts
    leaf1996LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1996CoverageChecked :
    coverageCheck (innerAD leaf1996Box) leaf1996InnerLog = true := by
  rfl'

private theorem leaf1996InnerLogValid :
    leaf1996InnerLog.Valid 8 (innerAD leaf1996Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf1996CoverageChecked

private noncomputable def leaf1996InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629255/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1996InputLogOnePlusV_eq :
    leaf1996InputLogOnePlusV = outerEnclosure 24
      (leaf1996Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1996RoundedFacts : LeafRoundedFacts 8
    leaf1996Certificate.logOnePlusV leaf1996InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1996InputLogOnePlusV_eq }

private noncomputable def leaf1996Inputs : Inputs :=
  inputsOfCaches globalInput sk134RoundedInputs
    chi136InputQChi innerPair41Input
    leaf1996InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1996LowerChecked :
    lowerCheck 24 leaf1996Box leaf1996Inputs = true := by
  rfl'

private theorem leaf1996CoversExact : CoversExact 8
    leaf1996Box leaf1996Certificate leaf1996InnerLog leaf1996Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk134RoundedFacts chi136RoundedFacts
    innerPair41RoundedFacts leaf1996RoundedFacts (by rfl)

private theorem leaf1996FlatSound : Sound leaf1996Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1996CertificateValid
    leaf1996InnerLogValid leaf1996CoversExact leaf1996LowerChecked

private noncomputable def leaf1997Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (11/64), chiHi := (45/256) }

private noncomputable def leaf1997Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871199/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717195776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (819411843/536870912) }, upper := { exponent := 0, mantissa := (12647/8192) } }, logOuter := sk135LogOuterCertificate, logK := sk135LogKCertificate, logChi := chi133LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435689471/137434391552) } }, logDArg := sk135LogDArgCertificate }

private noncomputable def leaf1997InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf1997LocalValidity :
    LeafFacts leaf1997Box leaf1997Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1997Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717195776) }) = true
      norm_num [leaf1997Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1997CertificateValid :
    WideCertificateValid leaf1997Box leaf1997Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk135ValidityFacts chi133ValidityFacts
    leaf1997LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1997CoverageChecked :
    coverageCheck (innerAD leaf1997Box) leaf1997InnerLog = true := by
  rfl'

private theorem leaf1997InnerLogValid :
    leaf1997InnerLog.Valid 8 (innerAD leaf1997Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf1997CoverageChecked

private noncomputable def leaf1997InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629239/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1997InputLogOnePlusV_eq :
    leaf1997InputLogOnePlusV = outerEnclosure 24
      (leaf1997Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1997RoundedFacts : LeafRoundedFacts 8
    leaf1997Certificate.logOnePlusV leaf1997InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1997InputLogOnePlusV_eq }

private noncomputable def leaf1997Inputs : Inputs :=
  inputsOfCaches globalInput sk135RoundedInputs
    chi133InputQChi innerPair40Input
    leaf1997InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1997LowerChecked :
    lowerCheck 24 leaf1997Box leaf1997Inputs = true := by
  rfl'

private theorem leaf1997CoversExact : CoversExact 8
    leaf1997Box leaf1997Certificate leaf1997InnerLog leaf1997Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk135RoundedFacts chi133RoundedFacts
    innerPair40RoundedFacts leaf1997RoundedFacts (by rfl)

private theorem leaf1997FlatSound : Sound leaf1997Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1997CertificateValid
    leaf1997InnerLogValid leaf1997CoversExact leaf1997LowerChecked

private noncomputable def leaf1998Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (45/256), chiHi := (23/128) }

private noncomputable def leaf1998Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871201/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717145088) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (825833977/536870912) }, upper := { exponent := 0, mantissa := (6373/4096) } }, logOuter := sk135LogOuterCertificate, logK := sk135LogKCertificate, logChi := chi134LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435638783/137434290176) } }, logDArg := sk135LogDArgCertificate }

private noncomputable def leaf1998InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf1998LocalValidity :
    LeafFacts leaf1998Box leaf1998Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1998Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717145088) }) = true
      norm_num [leaf1998Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1998CertificateValid :
    WideCertificateValid leaf1998Box leaf1998Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk135ValidityFacts chi134ValidityFacts
    leaf1998LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1998CoverageChecked :
    coverageCheck (innerAD leaf1998Box) leaf1998InnerLog = true := by
  rfl'

private theorem leaf1998InnerLogValid :
    leaf1998InnerLog.Valid 8 (innerAD leaf1998Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf1998CoverageChecked

private noncomputable def leaf1998InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629245/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1998InputLogOnePlusV_eq :
    leaf1998InputLogOnePlusV = outerEnclosure 24
      (leaf1998Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1998RoundedFacts : LeafRoundedFacts 8
    leaf1998Certificate.logOnePlusV leaf1998InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1998InputLogOnePlusV_eq }

private noncomputable def leaf1998Inputs : Inputs :=
  inputsOfCaches globalInput sk135RoundedInputs
    chi134InputQChi innerPair40Input
    leaf1998InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1998LowerChecked :
    lowerCheck 24 leaf1998Box leaf1998Inputs = true := by
  rfl'

private theorem leaf1998CoversExact : CoversExact 8
    leaf1998Box leaf1998Certificate leaf1998InnerLog leaf1998Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk135RoundedFacts chi134RoundedFacts
    innerPair40RoundedFacts leaf1998RoundedFacts (by rfl)

private theorem leaf1998FlatSound : Sound leaf1998Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1998CertificateValid
    leaf1998InnerLogValid leaf1998CoversExact leaf1998LowerChecked

private noncomputable def leaf1999Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (11/64), chiHi := (45/256) }

private noncomputable def leaf1999Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871201/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717172736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (822295249/536870912) }, upper := { exponent := 0, mantissa := (3173/2048) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi133LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435666431/137434345472) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf1999InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf1999LocalValidity :
    LeafFacts leaf1999Box leaf1999Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1999Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717172736) }) = true
      norm_num [leaf1999Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1999CertificateValid :
    WideCertificateValid leaf1999Box leaf1999Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi133ValidityFacts
    leaf1999LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1999CoverageChecked :
    coverageCheck (innerAD leaf1999Box) leaf1999InnerLog = true := by
  rfl'

private theorem leaf1999InnerLogValid :
    leaf1999InnerLog.Valid 8 (innerAD leaf1999Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf1999CoverageChecked

private noncomputable def leaf1999InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814621/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1999InputLogOnePlusV_eq :
    leaf1999InputLogOnePlusV = outerEnclosure 24
      (leaf1999Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1999RoundedFacts : LeafRoundedFacts 8
    leaf1999Certificate.logOnePlusV leaf1999InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1999InputLogOnePlusV_eq }

private noncomputable def leaf1999Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi133InputQChi innerPair40Input
    leaf1999InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1999LowerChecked :
    lowerCheck 24 leaf1999Box leaf1999Inputs = true := by
  rfl'

private theorem leaf1999CoversExact : CoversExact 8
    leaf1999Box leaf1999Certificate leaf1999InnerLog leaf1999Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi133RoundedFacts
    innerPair40RoundedFacts leaf1999RoundedFacts (by rfl)

private theorem leaf1999FlatSound : Sound leaf1999Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1999CertificateValid
    leaf1999InnerLogValid leaf1999CoversExact leaf1999LowerChecked

private noncomputable def leaf2000Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (45/256), chiHi := (23/128) }

private noncomputable def leaf2000Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871203/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717121536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (828782915/536870912) }, upper := { exponent := 0, mantissa := (1599/1024) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi134LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435615231/137434243072) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf2000InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2000LocalValidity :
    LeafFacts leaf2000Box leaf2000Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2000Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717121536) }) = true
      norm_num [leaf2000Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2000CertificateValid :
    WideCertificateValid leaf2000Box leaf2000Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi134ValidityFacts
    leaf2000LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2000CoverageChecked :
    coverageCheck (innerAD leaf2000Box) leaf2000InnerLog = true := by
  rfl'

private theorem leaf2000InnerLogValid :
    leaf2000InnerLog.Valid 8 (innerAD leaf2000Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2000CoverageChecked

private noncomputable def leaf2000InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (181707/262144) }

set_option maxRecDepth 1000000 in
private theorem leaf2000InputLogOnePlusV_eq :
    leaf2000InputLogOnePlusV = outerEnclosure 24
      (leaf2000Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2000RoundedFacts : LeafRoundedFacts 8
    leaf2000Certificate.logOnePlusV leaf2000InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2000InputLogOnePlusV_eq }

private noncomputable def leaf2000Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi134InputQChi innerPair40Input
    leaf2000InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2000LowerChecked :
    lowerCheck 24 leaf2000Box leaf2000Inputs = true := by
  rfl'

private theorem leaf2000CoversExact : CoversExact 8
    leaf2000Box leaf2000Certificate leaf2000InnerLog leaf2000Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi134RoundedFacts
    innerPair40RoundedFacts leaf2000RoundedFacts (by rfl)

private theorem leaf2000FlatSound : Sound leaf2000Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2000CertificateValid
    leaf2000InnerLogValid leaf2000CoversExact leaf2000LowerChecked

private noncomputable def leaf2001Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (23/128), chiHi := (47/256) }

private noncomputable def leaf2001Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871203/536870912) }, vSqrt := { lower := (65529/65536), upper := (13743698739/13743418880) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (832256111/536870912) }, upper := { exponent := 0, mantissa := (12845/8192) } }, logOuter := sk135LogOuterCertificate, logK := sk135LogKCertificate, logChi := chi135LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (27487117619/27486837760) } }, logDArg := sk135LogDArgCertificate }

private noncomputable def leaf2001InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf2001LocalValidity :
    LeafFacts leaf2001Box leaf2001Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2001Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (13743698739/13743418880) }) = true
      norm_num [leaf2001Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2001CertificateValid :
    WideCertificateValid leaf2001Box leaf2001Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk135ValidityFacts chi135ValidityFacts
    leaf2001LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2001CoverageChecked :
    coverageCheck (innerAD leaf2001Box) leaf2001InnerLog = true := by
  rfl'

private theorem leaf2001InnerLogValid :
    leaf2001InnerLog.Valid 8 (innerAD leaf2001Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf2001CoverageChecked

private noncomputable def leaf2001InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907313/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2001InputLogOnePlusV_eq :
    leaf2001InputLogOnePlusV = outerEnclosure 24
      (leaf2001Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2001RoundedFacts : LeafRoundedFacts 8
    leaf2001Certificate.logOnePlusV leaf2001InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2001InputLogOnePlusV_eq }

private noncomputable def leaf2001Inputs : Inputs :=
  inputsOfCaches globalInput sk135RoundedInputs
    chi135InputQChi innerPair41Input
    leaf2001InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2001LowerChecked :
    lowerCheck 24 leaf2001Box leaf2001Inputs = true := by
  rfl'

private theorem leaf2001CoversExact : CoversExact 8
    leaf2001Box leaf2001Certificate leaf2001InnerLog leaf2001Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk135RoundedFacts chi135RoundedFacts
    innerPair41RoundedFacts leaf2001RoundedFacts (by rfl)

private theorem leaf2001FlatSound : Sound leaf2001Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2001CertificateValid
    leaf2001InnerLogValid leaf2001CoversExact leaf2001LowerChecked

private noncomputable def leaf2002Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (47/256), chiHi := (3/16) }

private noncomputable def leaf2002Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871205/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717043712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (838678245/536870912) }, upper := { exponent := 0, mantissa := (809/512) } }, logOuter := sk135LogOuterCertificate, logK := sk135LogKCertificate, logChi := chi136LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435537407/137434087424) } }, logDArg := sk135LogDArgCertificate }

private noncomputable def leaf2002InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf2002LocalValidity :
    LeafFacts leaf2002Box leaf2002Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2002Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717043712) }) = true
      norm_num [leaf2002Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2002CertificateValid :
    WideCertificateValid leaf2002Box leaf2002Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk135ValidityFacts chi136ValidityFacts
    leaf2002LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2002CoverageChecked :
    coverageCheck (innerAD leaf2002Box) leaf2002InnerLog = true := by
  rfl'

private theorem leaf2002InnerLogValid :
    leaf2002InnerLog.Valid 8 (innerAD leaf2002Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf2002CoverageChecked

private noncomputable def leaf2002InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814629/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2002InputLogOnePlusV_eq :
    leaf2002InputLogOnePlusV = outerEnclosure 24
      (leaf2002Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2002RoundedFacts : LeafRoundedFacts 8
    leaf2002Certificate.logOnePlusV leaf2002InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2002InputLogOnePlusV_eq }

private noncomputable def leaf2002Inputs : Inputs :=
  inputsOfCaches globalInput sk135RoundedInputs
    chi136InputQChi innerPair41Input
    leaf2002InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2002LowerChecked :
    lowerCheck 24 leaf2002Box leaf2002Inputs = true := by
  rfl'

private theorem leaf2002CoversExact : CoversExact 8
    leaf2002Box leaf2002Certificate leaf2002InnerLog leaf2002Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk135RoundedFacts chi136RoundedFacts
    innerPair41RoundedFacts leaf2002RoundedFacts (by rfl)

private theorem leaf2002FlatSound : Sound leaf2002Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2002CertificateValid
    leaf2002InnerLogValid leaf2002CoversExact leaf2002LowerChecked

private noncomputable def leaf2003Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (23/128), chiHi := (47/256) }

private noncomputable def leaf2003Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871205/536870912) }, vSqrt := { lower := (65529/65536), upper := (1347421445/1347393536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (835270581/536870912) }, upper := { exponent := 0, mantissa := (3223/2048) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi135LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (2694814981/2694787072) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf2003InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf2003LocalValidity :
    LeafFacts leaf2003Box leaf2003Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2003Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (1347421445/1347393536) }) = true
      norm_num [leaf2003Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2003CertificateValid :
    WideCertificateValid leaf2003Box leaf2003Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi135ValidityFacts
    leaf2003LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2003CoverageChecked :
    coverageCheck (innerAD leaf2003Box) leaf2003InnerLog = true := by
  rfl'

private theorem leaf2003InnerLogValid :
    leaf2003InnerLog.Valid 8 (innerAD leaf2003Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf2003CoverageChecked

private noncomputable def leaf2003InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814627/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2003InputLogOnePlusV_eq :
    leaf2003InputLogOnePlusV = outerEnclosure 24
      (leaf2003Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2003RoundedFacts : LeafRoundedFacts 8
    leaf2003Certificate.logOnePlusV leaf2003InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2003InputLogOnePlusV_eq }

private noncomputable def leaf2003Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi135InputQChi innerPair41Input
    leaf2003InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2003LowerChecked :
    lowerCheck 24 leaf2003Box leaf2003Inputs = true := by
  rfl'

private theorem leaf2003CoversExact : CoversExact 8
    leaf2003Box leaf2003Certificate leaf2003InnerLog leaf2003Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi135RoundedFacts
    innerPair41RoundedFacts leaf2003RoundedFacts (by rfl)

private theorem leaf2003FlatSound : Sound leaf2003Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2003CertificateValid
    leaf2003InnerLogValid leaf2003CoversExact leaf2003LowerChecked

private noncomputable def leaf2004Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (47/256), chiHi := (3/16) }

private noncomputable def leaf2004Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871207/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717019136) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (841758247/536870912) }, upper := { exponent := 0, mantissa := (203/128) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi136LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435512831/137434038272) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf2004InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2004LocalValidity :
    LeafFacts leaf2004Box leaf2004Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2004Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717019136) }) = true
      norm_num [leaf2004Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2004CertificateValid :
    WideCertificateValid leaf2004Box leaf2004Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi136ValidityFacts
    leaf2004LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2004CoverageChecked :
    coverageCheck (innerAD leaf2004Box) leaf2004InnerLog = true := by
  rfl'

private theorem leaf2004InnerLogValid :
    leaf2004InnerLog.Valid 8 (innerAD leaf2004Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2004CoverageChecked

private noncomputable def leaf2004InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629261/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2004InputLogOnePlusV_eq :
    leaf2004InputLogOnePlusV = outerEnclosure 24
      (leaf2004Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2004RoundedFacts : LeafRoundedFacts 8
    leaf2004Certificate.logOnePlusV leaf2004InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2004InputLogOnePlusV_eq }

private noncomputable def leaf2004Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi136InputQChi innerPair50Input
    leaf2004InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2004LowerChecked :
    lowerCheck 24 leaf2004Box leaf2004Inputs = true := by
  rfl'

private theorem leaf2004CoversExact : CoversExact 8
    leaf2004Box leaf2004Certificate leaf2004InnerLog leaf2004Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi136RoundedFacts
    innerPair50RoundedFacts leaf2004RoundedFacts (by rfl)

private theorem leaf2004FlatSound : Sound leaf2004Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2004CertificateValid
    leaf2004InnerLogValid leaf2004CoversExact leaf2004LowerChecked

private noncomputable def leaf2005Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (5/32), chiHi := (41/256) }

private noncomputable def leaf2005Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871195/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717356544) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (798965863/536870912) }, upper := { exponent := 0, mantissa := (12333/8192) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi183LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435850239/137434713088) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf2005InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf2005LocalValidity :
    LeafFacts leaf2005Box leaf2005Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2005Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717356544) }) = true
      norm_num [leaf2005Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2005CertificateValid :
    WideCertificateValid leaf2005Box leaf2005Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi183ValidityFacts
    leaf2005LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2005CoverageChecked :
    coverageCheck (innerAD leaf2005Box) leaf2005InnerLog = true := by
  rfl'

private theorem leaf2005InnerLogValid :
    leaf2005InnerLog.Valid 8 (innerAD leaf2005Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf2005CoverageChecked

private noncomputable def leaf2005InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907305/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2005InputLogOnePlusV_eq :
    leaf2005InputLogOnePlusV = outerEnclosure 24
      (leaf2005Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2005RoundedFacts : LeafRoundedFacts 8
    leaf2005Certificate.logOnePlusV leaf2005InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2005InputLogOnePlusV_eq }

private noncomputable def leaf2005Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi183InputQChi innerPair35Input
    leaf2005InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2005LowerChecked :
    lowerCheck 24 leaf2005Box leaf2005Inputs = true := by
  rfl'

private theorem leaf2005CoversExact : CoversExact 8
    leaf2005Box leaf2005Certificate leaf2005InnerLog leaf2005Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi183RoundedFacts
    innerPair35RoundedFacts leaf2005RoundedFacts (by rfl)

private theorem leaf2005FlatSound : Sound leaf2005Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2005CertificateValid
    leaf2005InnerLogValid leaf2005CoversExact leaf2005LowerChecked

private noncomputable def leaf2006Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (41/256), chiHi := (21/128) }

private noncomputable def leaf2006Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871197/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717304832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (805519061/536870912) }, upper := { exponent := 0, mantissa := (6217/4096) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi184LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435798527/137434609664) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf2006InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2006LocalValidity :
    LeafFacts leaf2006Box leaf2006Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2006Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717304832) }) = true
      norm_num [leaf2006Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2006CertificateValid :
    WideCertificateValid leaf2006Box leaf2006Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi184ValidityFacts
    leaf2006LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2006CoverageChecked :
    coverageCheck (innerAD leaf2006Box) leaf2006InnerLog = true := by
  rfl'

private theorem leaf2006InnerLogValid :
    leaf2006InnerLog.Valid 8 (innerAD leaf2006Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2006CoverageChecked

private noncomputable def leaf2006InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814613/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2006InputLogOnePlusV_eq :
    leaf2006InputLogOnePlusV = outerEnclosure 24
      (leaf2006Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2006RoundedFacts : LeafRoundedFacts 8
    leaf2006Certificate.logOnePlusV leaf2006InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2006InputLogOnePlusV_eq }

private noncomputable def leaf2006Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi184InputQChi innerPair40Input
    leaf2006InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2006LowerChecked :
    lowerCheck 24 leaf2006Box leaf2006Inputs = true := by
  rfl'

private theorem leaf2006CoversExact : CoversExact 8
    leaf2006Box leaf2006Certificate leaf2006InnerLog leaf2006Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi184RoundedFacts
    innerPair40RoundedFacts leaf2006RoundedFacts (by rfl)

private theorem leaf2006FlatSound : Sound leaf2006Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2006CertificateValid
    leaf2006InnerLogValid leaf2006CoversExact leaf2006LowerChecked

private noncomputable def leaf2007Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (5/32), chiHi := (41/256) }

private noncomputable def leaf2007Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871197/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717335552) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (801587141/536870912) }, upper := { exponent := 0, mantissa := (6187/4096) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi183LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435829247/137434671104) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf2007InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf2007LocalValidity :
    LeafFacts leaf2007Box leaf2007Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2007Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717335552) }) = true
      norm_num [leaf2007Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2007CertificateValid :
    WideCertificateValid leaf2007Box leaf2007Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi183ValidityFacts
    leaf2007LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2007CoverageChecked :
    coverageCheck (innerAD leaf2007Box) leaf2007InnerLog = true := by
  rfl'

private theorem leaf2007InnerLogValid :
    leaf2007InnerLog.Valid 8 (innerAD leaf2007Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf2007CoverageChecked

private noncomputable def leaf2007InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814611/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2007InputLogOnePlusV_eq :
    leaf2007InputLogOnePlusV = outerEnclosure 24
      (leaf2007Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2007RoundedFacts : LeafRoundedFacts 8
    leaf2007Certificate.logOnePlusV leaf2007InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2007InputLogOnePlusV_eq }

private noncomputable def leaf2007Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi183InputQChi innerPair35Input
    leaf2007InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2007LowerChecked :
    lowerCheck 24 leaf2007Box leaf2007Inputs = true := by
  rfl'

private theorem leaf2007CoversExact : CoversExact 8
    leaf2007Box leaf2007Certificate leaf2007InnerLog leaf2007Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi183RoundedFacts
    innerPair35RoundedFacts leaf2007RoundedFacts (by rfl)

private theorem leaf2007FlatSound : Sound leaf2007Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2007CertificateValid
    leaf2007InnerLogValid leaf2007CoversExact leaf2007LowerChecked

private noncomputable def leaf2008Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (41/256), chiHi := (21/128) }

private noncomputable def leaf2008Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871199/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717283328) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (808205871/536870912) }, upper := { exponent := 0, mantissa := (3119/2048) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi184LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435777023/137434566656) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf2008InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2008LocalValidity :
    LeafFacts leaf2008Box leaf2008Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2008Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717283328) }) = true
      norm_num [leaf2008Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2008CertificateValid :
    WideCertificateValid leaf2008Box leaf2008Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi184ValidityFacts
    leaf2008LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2008CoverageChecked :
    coverageCheck (innerAD leaf2008Box) leaf2008InnerLog = true := by
  rfl'

private theorem leaf2008InnerLogValid :
    leaf2008InnerLog.Valid 8 (innerAD leaf2008Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2008CoverageChecked

private noncomputable def leaf2008InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907307/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2008InputLogOnePlusV_eq :
    leaf2008InputLogOnePlusV = outerEnclosure 24
      (leaf2008Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2008RoundedFacts : LeafRoundedFacts 8
    leaf2008Certificate.logOnePlusV leaf2008InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2008InputLogOnePlusV_eq }

private noncomputable def leaf2008Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi184InputQChi innerPair40Input
    leaf2008InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2008LowerChecked :
    lowerCheck 24 leaf2008Box leaf2008Inputs = true := by
  rfl'

private theorem leaf2008CoversExact : CoversExact 8
    leaf2008Box leaf2008Certificate leaf2008InnerLog leaf2008Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi184RoundedFacts
    innerPair40RoundedFacts leaf2008RoundedFacts (by rfl)

private theorem leaf2008FlatSound : Sound leaf2008Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2008CertificateValid
    leaf2008InnerLogValid leaf2008CoversExact leaf2008LowerChecked

private noncomputable def leaf2009Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (21/128), chiHi := (43/256) }

private noncomputable def leaf2009Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871199/536870912) }, vSqrt := { lower := (65529/65536), upper := (269484289/269479424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (812072259/536870912) }, upper := { exponent := 0, mantissa := (12535/8192) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi185LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (538963713/538958848) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf2009InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2009LocalValidity :
    LeafFacts leaf2009Box leaf2009Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2009Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (269484289/269479424) }) = true
      norm_num [leaf2009Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2009CertificateValid :
    WideCertificateValid leaf2009Box leaf2009Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi185ValidityFacts
    leaf2009LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2009CoverageChecked :
    coverageCheck (innerAD leaf2009Box) leaf2009InnerLog = true := by
  rfl'

private theorem leaf2009InnerLogValid :
    leaf2009InnerLog.Valid 8 (innerAD leaf2009Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2009CoverageChecked

private noncomputable def leaf2009InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (726827/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf2009InputLogOnePlusV_eq :
    leaf2009InputLogOnePlusV = outerEnclosure 24
      (leaf2009Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2009RoundedFacts : LeafRoundedFacts 8
    leaf2009Certificate.logOnePlusV leaf2009InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2009InputLogOnePlusV_eq }

private noncomputable def leaf2009Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi185InputQChi innerPair40Input
    leaf2009InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2009LowerChecked :
    lowerCheck 24 leaf2009Box leaf2009Inputs = true := by
  rfl'

private theorem leaf2009CoversExact : CoversExact 8
    leaf2009Box leaf2009Certificate leaf2009InnerLog leaf2009Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi185RoundedFacts
    innerPair40RoundedFacts leaf2009RoundedFacts (by rfl)

private theorem leaf2009FlatSound : Sound leaf2009Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2009CertificateValid
    leaf2009InnerLogValid leaf2009CoversExact leaf2009LowerChecked

private noncomputable def leaf2010Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (43/256), chiHi := (11/64) }

private noncomputable def leaf2010Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871201/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717201408) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (818625457/536870912) }, upper := { exponent := 0, mantissa := (3159/2048) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi186LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435695103/137434402816) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf2010InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2010LocalValidity :
    LeafFacts leaf2010Box leaf2010Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2010Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717201408) }) = true
      norm_num [leaf2010Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2010CertificateValid :
    WideCertificateValid leaf2010Box leaf2010Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi186ValidityFacts
    leaf2010LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2010CoverageChecked :
    coverageCheck (innerAD leaf2010Box) leaf2010InnerLog = true := by
  rfl'

private theorem leaf2010InnerLogValid :
    leaf2010InnerLog.Valid 8 (innerAD leaf2010Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2010CoverageChecked

private noncomputable def leaf2010InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814619/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2010InputLogOnePlusV_eq :
    leaf2010InputLogOnePlusV = outerEnclosure 24
      (leaf2010Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2010RoundedFacts : LeafRoundedFacts 8
    leaf2010Certificate.logOnePlusV leaf2010InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2010InputLogOnePlusV_eq }

private noncomputable def leaf2010Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi186InputQChi innerPair40Input
    leaf2010InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2010LowerChecked :
    lowerCheck 24 leaf2010Box leaf2010Inputs = true := by
  rfl'

private theorem leaf2010CoversExact : CoversExact 8
    leaf2010Box leaf2010Certificate leaf2010InnerLog leaf2010Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi186RoundedFacts
    innerPair40RoundedFacts leaf2010RoundedFacts (by rfl)

private theorem leaf2010FlatSound : Sound leaf2010Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2010CertificateValid
    leaf2010InnerLogValid leaf2010CoversExact leaf2010LowerChecked

private noncomputable def leaf2011Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (21/128), chiHi := (43/256) }

private noncomputable def leaf2011Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871201/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717231104) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (814824601/536870912) }, upper := { exponent := 0, mantissa := (6289/4096) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi185LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435724799/137434462208) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf2011InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2011LocalValidity :
    LeafFacts leaf2011Box leaf2011Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2011Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717231104) }) = true
      norm_num [leaf2011Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2011CertificateValid :
    WideCertificateValid leaf2011Box leaf2011Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi185ValidityFacts
    leaf2011LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2011CoverageChecked :
    coverageCheck (innerAD leaf2011Box) leaf2011InnerLog = true := by
  rfl'

private theorem leaf2011InnerLogValid :
    leaf2011InnerLog.Valid 8 (innerAD leaf2011Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2011CoverageChecked

private noncomputable def leaf2011InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629235/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2011InputLogOnePlusV_eq :
    leaf2011InputLogOnePlusV = outerEnclosure 24
      (leaf2011Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2011RoundedFacts : LeafRoundedFacts 8
    leaf2011Certificate.logOnePlusV leaf2011InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2011InputLogOnePlusV_eq }

private noncomputable def leaf2011Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi185InputQChi innerPair40Input
    leaf2011InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2011LowerChecked :
    lowerCheck 24 leaf2011Box leaf2011Inputs = true := by
  rfl'

private theorem leaf2011CoversExact : CoversExact 8
    leaf2011Box leaf2011Certificate leaf2011InnerLog leaf2011Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi185RoundedFacts
    innerPair40RoundedFacts leaf2011RoundedFacts (by rfl)

private theorem leaf2011FlatSound : Sound leaf2011Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2011CertificateValid
    leaf2011InnerLogValid leaf2011CoversExact leaf2011LowerChecked

private noncomputable def leaf2012Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (43/256), chiHi := (11/64) }

private noncomputable def leaf2012Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871203/536870912) }, vSqrt := { lower := (65529/65536), upper := (13743698739/13743435776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (821443331/536870912) }, upper := { exponent := 0, mantissa := (1585/1024) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi186LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (27487134515/27486871552) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf2012InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2012LocalValidity :
    LeafFacts leaf2012Box leaf2012Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2012Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (13743698739/13743435776) }) = true
      norm_num [leaf2012Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2012CertificateValid :
    WideCertificateValid leaf2012Box leaf2012Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi186ValidityFacts
    leaf2012LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2012CoverageChecked :
    coverageCheck (innerAD leaf2012Box) leaf2012InnerLog = true := by
  rfl'

private theorem leaf2012InnerLogValid :
    leaf2012InnerLog.Valid 8 (innerAD leaf2012Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2012CoverageChecked

private noncomputable def leaf2012InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629241/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2012InputLogOnePlusV_eq :
    leaf2012InputLogOnePlusV = outerEnclosure 24
      (leaf2012Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2012RoundedFacts : LeafRoundedFacts 8
    leaf2012Certificate.logOnePlusV leaf2012InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2012InputLogOnePlusV_eq }

private noncomputable def leaf2012Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi186InputQChi innerPair40Input
    leaf2012InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2012LowerChecked :
    lowerCheck 24 leaf2012Box leaf2012Inputs = true := by
  rfl'

private theorem leaf2012CoversExact : CoversExact 8
    leaf2012Box leaf2012Certificate leaf2012InnerLog leaf2012Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi186RoundedFacts
    innerPair40RoundedFacts leaf2012RoundedFacts (by rfl)

private theorem leaf2012FlatSound : Sound leaf2012Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2012CertificateValid
    leaf2012InnerLogValid leaf2012CoversExact leaf2012LowerChecked

private noncomputable def leaf2013Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (5/32), chiHi := (41/256) }

private noncomputable def leaf2013Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871199/536870912) }, vSqrt := { lower := (65529/65536), upper := (4581232913/4581154304) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (804208419/536870912) }, upper := { exponent := 0, mantissa := (12415/8192) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi183LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9162387217/9162308608) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf2013InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf2013LocalValidity :
    LeafFacts leaf2013Box leaf2013Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2013Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4581232913/4581154304) }) = true
      norm_num [leaf2013Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2013CertificateValid :
    WideCertificateValid leaf2013Box leaf2013Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi183ValidityFacts
    leaf2013LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2013CoverageChecked :
    coverageCheck (innerAD leaf2013Box) leaf2013InnerLog = true := by
  rfl'

private theorem leaf2013InnerLogValid :
    leaf2013InnerLog.Valid 8 (innerAD leaf2013Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf2013CoverageChecked

private noncomputable def leaf2013InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629225/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2013InputLogOnePlusV_eq :
    leaf2013InputLogOnePlusV = outerEnclosure 24
      (leaf2013Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2013RoundedFacts : LeafRoundedFacts 8
    leaf2013Certificate.logOnePlusV leaf2013InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2013InputLogOnePlusV_eq }

private noncomputable def leaf2013Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi183InputQChi innerPair35Input
    leaf2013InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2013LowerChecked :
    lowerCheck 24 leaf2013Box leaf2013Inputs = true := by
  rfl'

private theorem leaf2013CoversExact : CoversExact 8
    leaf2013Box leaf2013Certificate leaf2013InnerLog leaf2013Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi183RoundedFacts
    innerPair35RoundedFacts leaf2013RoundedFacts (by rfl)

private theorem leaf2013FlatSound : Sound leaf2013Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2013CertificateValid
    leaf2013InnerLogValid leaf2013CoversExact leaf2013LowerChecked

private noncomputable def leaf2014Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (41/256), chiHi := (21/128) }

private noncomputable def leaf2014Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871201/536870912) }, vSqrt := { lower := (65529/65536), upper := (4042264335/4042191872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (810892681/536870912) }, upper := { exponent := 0, mantissa := (6259/4096) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi184LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (8084456207/8084383744) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf2014InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2014LocalValidity :
    LeafFacts leaf2014Box leaf2014Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2014Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4042264335/4042191872) }) = true
      norm_num [leaf2014Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2014CertificateValid :
    WideCertificateValid leaf2014Box leaf2014Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi184ValidityFacts
    leaf2014LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2014CoverageChecked :
    coverageCheck (innerAD leaf2014Box) leaf2014InnerLog = true := by
  rfl'

private theorem leaf2014InnerLogValid :
    leaf2014InnerLog.Valid 8 (innerAD leaf2014Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2014CoverageChecked

private noncomputable def leaf2014InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629231/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2014InputLogOnePlusV_eq :
    leaf2014InputLogOnePlusV = outerEnclosure 24
      (leaf2014Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2014RoundedFacts : LeafRoundedFacts 8
    leaf2014Certificate.logOnePlusV leaf2014InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2014InputLogOnePlusV_eq }

private noncomputable def leaf2014Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi184InputQChi innerPair40Input
    leaf2014InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2014LowerChecked :
    lowerCheck 24 leaf2014Box leaf2014Inputs = true := by
  rfl'

private theorem leaf2014CoversExact : CoversExact 8
    leaf2014Box leaf2014Certificate leaf2014InnerLog leaf2014Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi184RoundedFacts
    innerPair40RoundedFacts leaf2014RoundedFacts (by rfl)

private theorem leaf2014FlatSound : Sound leaf2014Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2014CertificateValid
    leaf2014InnerLogValid leaf2014CoversExact leaf2014LowerChecked

private noncomputable def leaf2015Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (5/32), chiHi := (41/256) }

private noncomputable def leaf2015Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871201/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717293568) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (806829697/536870912) }, upper := { exponent := 0, mantissa := (1557/1024) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi183LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435787263/137434587136) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf2015InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2015LocalValidity :
    LeafFacts leaf2015Box leaf2015Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2015Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717293568) }) = true
      norm_num [leaf2015Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2015CertificateValid :
    WideCertificateValid leaf2015Box leaf2015Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi183ValidityFacts
    leaf2015LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2015CoverageChecked :
    coverageCheck (innerAD leaf2015Box) leaf2015InnerLog = true := by
  rfl'

private theorem leaf2015InnerLogValid :
    leaf2015InnerLog.Valid 8 (innerAD leaf2015Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2015CoverageChecked

private noncomputable def leaf2015InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629227/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2015InputLogOnePlusV_eq :
    leaf2015InputLogOnePlusV = outerEnclosure 24
      (leaf2015Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2015RoundedFacts : LeafRoundedFacts 8
    leaf2015Certificate.logOnePlusV leaf2015InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2015InputLogOnePlusV_eq }

private noncomputable def leaf2015Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi183InputQChi innerPair40Input
    leaf2015InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2015LowerChecked :
    lowerCheck 24 leaf2015Box leaf2015Inputs = true := by
  rfl'

private theorem leaf2015CoversExact : CoversExact 8
    leaf2015Box leaf2015Certificate leaf2015InnerLog leaf2015Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi183RoundedFacts
    innerPair40RoundedFacts leaf2015RoundedFacts (by rfl)

private theorem leaf2015FlatSound : Sound leaf2015Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2015CertificateValid
    leaf2015InnerLogValid leaf2015CoversExact leaf2015LowerChecked

private noncomputable def leaf2016Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (41/256), chiHi := (21/128) }

private noncomputable def leaf2016Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871203/536870912) }, vSqrt := { lower := (65529/65536), upper := (13743698739/13743448064) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (813579491/536870912) }, upper := { exponent := 0, mantissa := (785/512) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi184LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (27487146803/27486896128) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf2016InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2016LocalValidity :
    LeafFacts leaf2016Box leaf2016Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2016Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (13743698739/13743448064) }) = true
      norm_num [leaf2016Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2016CertificateValid :
    WideCertificateValid leaf2016Box leaf2016Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi184ValidityFacts
    leaf2016LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2016CoverageChecked :
    coverageCheck (innerAD leaf2016Box) leaf2016InnerLog = true := by
  rfl'

private theorem leaf2016InnerLogValid :
    leaf2016InnerLog.Valid 8 (innerAD leaf2016Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2016CoverageChecked

private noncomputable def leaf2016InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814617/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2016InputLogOnePlusV_eq :
    leaf2016InputLogOnePlusV = outerEnclosure 24
      (leaf2016Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2016RoundedFacts : LeafRoundedFacts 8
    leaf2016Certificate.logOnePlusV leaf2016InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2016InputLogOnePlusV_eq }

private noncomputable def leaf2016Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi184InputQChi innerPair40Input
    leaf2016InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2016LowerChecked :
    lowerCheck 24 leaf2016Box leaf2016Inputs = true := by
  rfl'

private theorem leaf2016CoversExact : CoversExact 8
    leaf2016Box leaf2016Certificate leaf2016InnerLog leaf2016Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi184RoundedFacts
    innerPair40RoundedFacts leaf2016RoundedFacts (by rfl)

private theorem leaf2016FlatSound : Sound leaf2016Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2016CertificateValid
    leaf2016InnerLogValid leaf2016CoversExact leaf2016LowerChecked

private noncomputable def leaf2017Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (21/128), chiHi := (43/256) }

private noncomputable def leaf2017Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871203/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717209088) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (817576943/536870912) }, upper := { exponent := 0, mantissa := (12621/8192) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi185LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435702783/137434418176) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf2017InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2017LocalValidity :
    LeafFacts leaf2017Box leaf2017Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2017Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717209088) }) = true
      norm_num [leaf2017Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2017CertificateValid :
    WideCertificateValid leaf2017Box leaf2017Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi185ValidityFacts
    leaf2017LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2017CoverageChecked :
    coverageCheck (innerAD leaf2017Box) leaf2017InnerLog = true := by
  rfl'

private theorem leaf2017InnerLogValid :
    leaf2017InnerLog.Valid 8 (innerAD leaf2017Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2017CoverageChecked

private noncomputable def leaf2017InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814619/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2017InputLogOnePlusV_eq :
    leaf2017InputLogOnePlusV = outerEnclosure 24
      (leaf2017Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2017RoundedFacts : LeafRoundedFacts 8
    leaf2017Certificate.logOnePlusV leaf2017InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2017InputLogOnePlusV_eq }

private noncomputable def leaf2017Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi185InputQChi innerPair40Input
    leaf2017InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2017LowerChecked :
    lowerCheck 24 leaf2017Box leaf2017Inputs = true := by
  rfl'

private theorem leaf2017CoversExact : CoversExact 8
    leaf2017Box leaf2017Certificate leaf2017InnerLog leaf2017Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi185RoundedFacts
    innerPair40RoundedFacts leaf2017RoundedFacts (by rfl)

private theorem leaf2017FlatSound : Sound leaf2017Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2017CertificateValid
    leaf2017InnerLogValid leaf2017CoversExact leaf2017LowerChecked

private noncomputable def leaf2018Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (43/256), chiHi := (11/64) }

private noncomputable def leaf2018Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871205/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905718784) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (824261205/536870912) }, upper := { exponent := 0, mantissa := (3181/2048) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi186LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811883349/45811437568) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf2018InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2018LocalValidity :
    LeafFacts leaf2018Box leaf2018Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2018Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905718784) }) = true
      norm_num [leaf2018Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2018CertificateValid :
    WideCertificateValid leaf2018Box leaf2018Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi186ValidityFacts
    leaf2018LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2018CoverageChecked :
    coverageCheck (innerAD leaf2018Box) leaf2018InnerLog = true := by
  rfl'

private theorem leaf2018InnerLogValid :
    leaf2018InnerLog.Valid 8 (innerAD leaf2018Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2018CoverageChecked

private noncomputable def leaf2018InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907311/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2018InputLogOnePlusV_eq :
    leaf2018InputLogOnePlusV = outerEnclosure 24
      (leaf2018Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2018RoundedFacts : LeafRoundedFacts 8
    leaf2018Certificate.logOnePlusV leaf2018InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2018InputLogOnePlusV_eq }

private noncomputable def leaf2018Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi186InputQChi innerPair40Input
    leaf2018InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2018LowerChecked :
    lowerCheck 24 leaf2018Box leaf2018Inputs = true := by
  rfl'

private theorem leaf2018CoversExact : CoversExact 8
    leaf2018Box leaf2018Certificate leaf2018InnerLog leaf2018Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi186RoundedFacts
    innerPair40RoundedFacts leaf2018RoundedFacts (by rfl)

private theorem leaf2018FlatSound : Sound leaf2018Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2018CertificateValid
    leaf2018InnerLogValid leaf2018CoversExact leaf2018LowerChecked

private noncomputable def leaf2019Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (21/128), chiHi := (43/256) }

private noncomputable def leaf2019Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871205/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905729024) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (820329285/536870912) }, upper := { exponent := 0, mantissa := (1583/1024) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi185LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811893589/45811458048) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf2019InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2019LocalValidity :
    LeafFacts leaf2019Box leaf2019Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2019Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905729024) }) = true
      norm_num [leaf2019Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2019CertificateValid :
    WideCertificateValid leaf2019Box leaf2019Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi185ValidityFacts
    leaf2019LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2019CoverageChecked :
    coverageCheck (innerAD leaf2019Box) leaf2019InnerLog = true := by
  rfl'

private theorem leaf2019InnerLogValid :
    leaf2019InnerLog.Valid 8 (innerAD leaf2019Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2019CoverageChecked

private noncomputable def leaf2019InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453655/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf2019InputLogOnePlusV_eq :
    leaf2019InputLogOnePlusV = outerEnclosure 24
      (leaf2019Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2019RoundedFacts : LeafRoundedFacts 8
    leaf2019Certificate.logOnePlusV leaf2019InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2019InputLogOnePlusV_eq }

private noncomputable def leaf2019Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi185InputQChi innerPair40Input
    leaf2019InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2019LowerChecked :
    lowerCheck 24 leaf2019Box leaf2019Inputs = true := by
  rfl'

private theorem leaf2019CoversExact : CoversExact 8
    leaf2019Box leaf2019Certificate leaf2019InnerLog leaf2019Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi185RoundedFacts
    innerPair40RoundedFacts leaf2019RoundedFacts (by rfl)

private theorem leaf2019FlatSound : Sound leaf2019Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2019CertificateValid
    leaf2019InnerLogValid leaf2019CoversExact leaf2019LowerChecked

private noncomputable def leaf2020Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (43/256), chiHi := (11/64) }

private noncomputable def leaf2020Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871207/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717133824) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (827079079/536870912) }, upper := { exponent := 0, mantissa := (399/256) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi186LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435627519/137434267648) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf2020InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2020LocalValidity :
    LeafFacts leaf2020Box leaf2020Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2020Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717133824) }) = true
      norm_num [leaf2020Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2020CertificateValid :
    WideCertificateValid leaf2020Box leaf2020Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi186ValidityFacts
    leaf2020LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2020CoverageChecked :
    coverageCheck (innerAD leaf2020Box) leaf2020InnerLog = true := by
  rfl'

private theorem leaf2020InnerLogValid :
    leaf2020InnerLog.Valid 8 (innerAD leaf2020Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2020CoverageChecked

private noncomputable def leaf2020InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629247/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2020InputLogOnePlusV_eq :
    leaf2020InputLogOnePlusV = outerEnclosure 24
      (leaf2020Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2020RoundedFacts : LeafRoundedFacts 8
    leaf2020Certificate.logOnePlusV leaf2020InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2020InputLogOnePlusV_eq }

private noncomputable def leaf2020Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi186InputQChi innerPair40Input
    leaf2020InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2020LowerChecked :
    lowerCheck 24 leaf2020Box leaf2020Inputs = true := by
  rfl'

private theorem leaf2020CoversExact : CoversExact 8
    leaf2020Box leaf2020Certificate leaf2020InnerLog leaf2020Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi186RoundedFacts
    innerPair40RoundedFacts leaf2020RoundedFacts (by rfl)

private theorem leaf2020FlatSound : Sound leaf2020Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2020CertificateValid
    leaf2020InnerLogValid leaf2020CoversExact leaf2020LowerChecked

private noncomputable def leaf2021Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (11/64), chiHi := (45/256) }

private noncomputable def leaf2021Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871203/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717149696) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (825178655/536870912) }, upper := { exponent := 0, mantissa := (12737/8192) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi133LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435643391/137434299392) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf2021InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2021LocalValidity :
    LeafFacts leaf2021Box leaf2021Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2021Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717149696) }) = true
      norm_num [leaf2021Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2021CertificateValid :
    WideCertificateValid leaf2021Box leaf2021Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi133ValidityFacts
    leaf2021LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2021CoverageChecked :
    coverageCheck (innerAD leaf2021Box) leaf2021InnerLog = true := by
  rfl'

private theorem leaf2021InnerLogValid :
    leaf2021InnerLog.Valid 8 (innerAD leaf2021Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2021CoverageChecked

private noncomputable def leaf2021InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629245/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2021InputLogOnePlusV_eq :
    leaf2021InputLogOnePlusV = outerEnclosure 24
      (leaf2021Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2021RoundedFacts : LeafRoundedFacts 8
    leaf2021Certificate.logOnePlusV leaf2021InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2021InputLogOnePlusV_eq }

private noncomputable def leaf2021Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi133InputQChi innerPair40Input
    leaf2021InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2021LowerChecked :
    lowerCheck 24 leaf2021Box leaf2021Inputs = true := by
  rfl'

private theorem leaf2021CoversExact : CoversExact 8
    leaf2021Box leaf2021Certificate leaf2021InnerLog leaf2021Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi133RoundedFacts
    innerPair40RoundedFacts leaf2021RoundedFacts (by rfl)

private theorem leaf2021FlatSound : Sound leaf2021Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2021CertificateValid
    leaf2021InnerLogValid leaf2021CoversExact leaf2021LowerChecked

private noncomputable def leaf2022Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (45/256), chiHi := (23/128) }

private noncomputable def leaf2022Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871205/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905699328) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (831731853/536870912) }, upper := { exponent := 0, mantissa := (6419/4096) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi134LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811863893/45811398656) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf2022InnerLog : WideLogData :=
  innerPair156Data

set_option maxRecDepth 1000000 in
private theorem leaf2022LocalValidity :
    LeafFacts leaf2022Box leaf2022Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2022Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905699328) }) = true
      norm_num [leaf2022Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2022CertificateValid :
    WideCertificateValid leaf2022Box leaf2022Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi134ValidityFacts
    leaf2022LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2022CoverageChecked :
    coverageCheck (innerAD leaf2022Box) leaf2022InnerLog = true := by
  rfl'

private theorem leaf2022InnerLogValid :
    leaf2022InnerLog.Valid 8 (innerAD leaf2022Box) :=
  wideLogDataValid_of_cachedCheck endpoint43PositiveFacts
    endpoint47PositiveFacts.valid leaf2022CoverageChecked

private noncomputable def leaf2022InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629251/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2022InputLogOnePlusV_eq :
    leaf2022InputLogOnePlusV = outerEnclosure 24
      (leaf2022Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2022RoundedFacts : LeafRoundedFacts 8
    leaf2022Certificate.logOnePlusV leaf2022InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2022InputLogOnePlusV_eq }

private noncomputable def leaf2022Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi134InputQChi innerPair156Input
    leaf2022InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2022LowerChecked :
    lowerCheck 24 leaf2022Box leaf2022Inputs = true := by
  rfl'

private theorem leaf2022CoversExact : CoversExact 8
    leaf2022Box leaf2022Certificate leaf2022InnerLog leaf2022Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi134RoundedFacts
    innerPair156RoundedFacts leaf2022RoundedFacts (by rfl)

private theorem leaf2022FlatSound : Sound leaf2022Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2022CertificateValid
    leaf2022InnerLogValid leaf2022CoversExact leaf2022LowerChecked

private noncomputable def leaf2023Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (11/64), chiHi := (45/256) }

private noncomputable def leaf2023Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871205/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717126656) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (828062061/536870912) }, upper := { exponent := 0, mantissa := (6391/4096) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi133LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435620351/137434253312) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf2023InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2023LocalValidity :
    LeafFacts leaf2023Box leaf2023Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2023Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717126656) }) = true
      norm_num [leaf2023Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2023CertificateValid :
    WideCertificateValid leaf2023Box leaf2023Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi133ValidityFacts
    leaf2023LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2023CoverageChecked :
    coverageCheck (innerAD leaf2023Box) leaf2023InnerLog = true := by
  rfl'

private theorem leaf2023InnerLogValid :
    leaf2023InnerLog.Valid 8 (innerAD leaf2023Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2023CoverageChecked

private noncomputable def leaf2023InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (181707/262144) }

set_option maxRecDepth 1000000 in
private theorem leaf2023InputLogOnePlusV_eq :
    leaf2023InputLogOnePlusV = outerEnclosure 24
      (leaf2023Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2023RoundedFacts : LeafRoundedFacts 8
    leaf2023Certificate.logOnePlusV leaf2023InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2023InputLogOnePlusV_eq }

private noncomputable def leaf2023Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi133InputQChi innerPair40Input
    leaf2023InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2023LowerChecked :
    lowerCheck 24 leaf2023Box leaf2023Inputs = true := by
  rfl'

private theorem leaf2023CoversExact : CoversExact 8
    leaf2023Box leaf2023Certificate leaf2023InnerLog leaf2023Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi133RoundedFacts
    innerPair40RoundedFacts leaf2023RoundedFacts (by rfl)

private theorem leaf2023FlatSound : Sound leaf2023Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2023CertificateValid
    leaf2023InnerLogValid leaf2023CoversExact leaf2023LowerChecked

private noncomputable def leaf2024Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (45/256), chiHi := (23/128) }

private noncomputable def leaf2024Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871207/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717074432) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (834680791/536870912) }, upper := { exponent := 0, mantissa := (3221/2048) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi134LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435568127/137434148864) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf2024InnerLog : WideLogData :=
  innerPair156Data

set_option maxRecDepth 1000000 in
private theorem leaf2024LocalValidity :
    LeafFacts leaf2024Box leaf2024Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2024Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717074432) }) = true
      norm_num [leaf2024Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2024CertificateValid :
    WideCertificateValid leaf2024Box leaf2024Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi134ValidityFacts
    leaf2024LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2024CoverageChecked :
    coverageCheck (innerAD leaf2024Box) leaf2024InnerLog = true := by
  rfl'

private theorem leaf2024InnerLogValid :
    leaf2024InnerLog.Valid 8 (innerAD leaf2024Box) :=
  wideLogDataValid_of_cachedCheck endpoint43PositiveFacts
    endpoint47PositiveFacts.valid leaf2024CoverageChecked

private noncomputable def leaf2024InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814627/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2024InputLogOnePlusV_eq :
    leaf2024InputLogOnePlusV = outerEnclosure 24
      (leaf2024Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2024RoundedFacts : LeafRoundedFacts 8
    leaf2024Certificate.logOnePlusV leaf2024InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2024InputLogOnePlusV_eq }

private noncomputable def leaf2024Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi134InputQChi innerPair156Input
    leaf2024InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2024LowerChecked :
    lowerCheck 24 leaf2024Box leaf2024Inputs = true := by
  rfl'

private theorem leaf2024CoversExact : CoversExact 8
    leaf2024Box leaf2024Certificate leaf2024InnerLog leaf2024Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi134RoundedFacts
    innerPair156RoundedFacts leaf2024RoundedFacts (by rfl)

private theorem leaf2024FlatSound : Sound leaf2024Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2024CertificateValid
    leaf2024InnerLogValid leaf2024CoversExact leaf2024LowerChecked

private noncomputable def leaf2025Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (23/128), chiHi := (47/256) }

private noncomputable def leaf2025Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871207/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717046272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (838285051/536870912) }, upper := { exponent := 0, mantissa := (12939/8192) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi135LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435539967/137434092544) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf2025InnerLog : WideLogData :=
  innerPair154Data

set_option maxRecDepth 1000000 in
private theorem leaf2025LocalValidity :
    LeafFacts leaf2025Box leaf2025Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2025Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717046272) }) = true
      norm_num [leaf2025Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2025CertificateValid :
    WideCertificateValid leaf2025Box leaf2025Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi135ValidityFacts
    leaf2025LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2025CoverageChecked :
    coverageCheck (innerAD leaf2025Box) leaf2025InnerLog = true := by
  rfl'

private theorem leaf2025InnerLogValid :
    leaf2025InnerLog.Valid 8 (innerAD leaf2025Box) :=
  wideLogDataValid_of_cachedCheck endpoint43PositiveFacts
    endpoint44PositiveFacts.valid leaf2025CoverageChecked

private noncomputable def leaf2025InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629257/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2025InputLogOnePlusV_eq :
    leaf2025InputLogOnePlusV = outerEnclosure 24
      (leaf2025Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2025RoundedFacts : LeafRoundedFacts 8
    leaf2025Certificate.logOnePlusV leaf2025InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2025InputLogOnePlusV_eq }

private noncomputable def leaf2025Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi135InputQChi innerPair154Input
    leaf2025InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2025LowerChecked :
    lowerCheck 24 leaf2025Box leaf2025Inputs = true := by
  rfl'

private theorem leaf2025CoversExact : CoversExact 8
    leaf2025Box leaf2025Certificate leaf2025InnerLog leaf2025Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi135RoundedFacts
    innerPair154RoundedFacts leaf2025RoundedFacts (by rfl)

private theorem leaf2025FlatSound : Sound leaf2025Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2025CertificateValid
    leaf2025InnerLogValid leaf2025CoversExact leaf2025LowerChecked

private noncomputable def leaf2026Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (47/256), chiHi := (3/16) }

private noncomputable def leaf2026Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871209/536870912) }, vSqrt := { lower := (65529/65536), upper := (13743698739/13743398912) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (844838249/536870912) }, upper := { exponent := 0, mantissa := (815/512) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi136LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (27487097651/27486797824) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf2026InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2026LocalValidity :
    LeafFacts leaf2026Box leaf2026Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2026Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (13743698739/13743398912) }) = true
      norm_num [leaf2026Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2026CertificateValid :
    WideCertificateValid leaf2026Box leaf2026Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi136ValidityFacts
    leaf2026LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2026CoverageChecked :
    coverageCheck (innerAD leaf2026Box) leaf2026InnerLog = true := by
  rfl'

private theorem leaf2026InnerLogValid :
    leaf2026InnerLog.Valid 8 (innerAD leaf2026Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2026CoverageChecked

private noncomputable def leaf2026InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (726829/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf2026InputLogOnePlusV_eq :
    leaf2026InputLogOnePlusV = outerEnclosure 24
      (leaf2026Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2026RoundedFacts : LeafRoundedFacts 8
    leaf2026Certificate.logOnePlusV leaf2026InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2026InputLogOnePlusV_eq }

private noncomputable def leaf2026Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi136InputQChi innerPair50Input
    leaf2026InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2026LowerChecked :
    lowerCheck 24 leaf2026Box leaf2026Inputs = true := by
  rfl'

private theorem leaf2026CoversExact : CoversExact 8
    leaf2026Box leaf2026Certificate leaf2026InnerLog leaf2026Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi136RoundedFacts
    innerPair50RoundedFacts leaf2026RoundedFacts (by rfl)

private theorem leaf2026FlatSound : Sound leaf2026Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2026CertificateValid
    leaf2026InnerLogValid leaf2026CoversExact leaf2026LowerChecked

private noncomputable def leaf2027Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (23/128), chiHi := (47/256) }

private noncomputable def leaf2027Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871209/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717022208) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (841299521/536870912) }, upper := { exponent := 0, mantissa := (6493/4096) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi135LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435515903/137434044416) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf2027InnerLog : WideLogData :=
  innerPair54Data

set_option maxRecDepth 1000000 in
private theorem leaf2027LocalValidity :
    LeafFacts leaf2027Box leaf2027Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2027Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717022208) }) = true
      norm_num [leaf2027Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2027CertificateValid :
    WideCertificateValid leaf2027Box leaf2027Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi135ValidityFacts
    leaf2027LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2027CoverageChecked :
    coverageCheck (innerAD leaf2027Box) leaf2027InnerLog = true := by
  rfl'

private theorem leaf2027InnerLogValid :
    leaf2027InnerLog.Valid 8 (innerAD leaf2027Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint44PositiveFacts.valid leaf2027CoverageChecked

private noncomputable def leaf2027InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907315/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2027InputLogOnePlusV_eq :
    leaf2027InputLogOnePlusV = outerEnclosure 24
      (leaf2027Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2027RoundedFacts : LeafRoundedFacts 8
    leaf2027Certificate.logOnePlusV leaf2027InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2027InputLogOnePlusV_eq }

private noncomputable def leaf2027Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi135InputQChi innerPair54Input
    leaf2027InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2027LowerChecked :
    lowerCheck 24 leaf2027Box leaf2027Inputs = true := by
  rfl'

private theorem leaf2027CoversExact : CoversExact 8
    leaf2027Box leaf2027Certificate leaf2027InnerLog leaf2027Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi135RoundedFacts
    innerPair54RoundedFacts leaf2027RoundedFacts (by rfl)

private theorem leaf2027FlatSound : Sound leaf2027Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2027CertificateValid
    leaf2027InnerLogValid leaf2027CoversExact leaf2027LowerChecked

private noncomputable def leaf2028Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (47/256), chiHi := (3/16) }

private noncomputable def leaf2028Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871211/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68716969984) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (847918251/536870912) }, upper := { exponent := 0, mantissa := (409/256) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi136LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435463679/137433939968) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf2028InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2028LocalValidity :
    LeafFacts leaf2028Box leaf2028Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2028Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68716969984) }) = true
      norm_num [leaf2028Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2028CertificateValid :
    WideCertificateValid leaf2028Box leaf2028Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi136ValidityFacts
    leaf2028LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2028CoverageChecked :
    coverageCheck (innerAD leaf2028Box) leaf2028InnerLog = true := by
  rfl'

private theorem leaf2028InnerLogValid :
    leaf2028InnerLog.Valid 8 (innerAD leaf2028Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2028CoverageChecked

private noncomputable def leaf2028InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629267/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2028InputLogOnePlusV_eq :
    leaf2028InputLogOnePlusV = outerEnclosure 24
      (leaf2028Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2028RoundedFacts : LeafRoundedFacts 8
    leaf2028Certificate.logOnePlusV leaf2028InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2028InputLogOnePlusV_eq }

private noncomputable def leaf2028Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi136InputQChi innerPair50Input
    leaf2028InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2028LowerChecked :
    lowerCheck 24 leaf2028Box leaf2028Inputs = true := by
  rfl'

private theorem leaf2028CoversExact : CoversExact 8
    leaf2028Box leaf2028Certificate leaf2028InnerLog leaf2028Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi136RoundedFacts
    innerPair50RoundedFacts leaf2028RoundedFacts (by rfl)

private theorem leaf2028FlatSound : Sound leaf2028Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2028CertificateValid
    leaf2028InnerLogValid leaf2028CoversExact leaf2028LowerChecked

private noncomputable def leaf2029Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (11/64), chiHi := (45/256) }

private noncomputable def leaf2029Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871207/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717103616) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (830945467/536870912) }, upper := { exponent := 0, mantissa := (12827/8192) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi133LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435597311/137434207232) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf2029InnerLog : WideLogData :=
  innerPair156Data

set_option maxRecDepth 1000000 in
private theorem leaf2029LocalValidity :
    LeafFacts leaf2029Box leaf2029Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2029Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717103616) }) = true
      norm_num [leaf2029Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2029CertificateValid :
    WideCertificateValid leaf2029Box leaf2029Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi133ValidityFacts
    leaf2029LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2029CoverageChecked :
    coverageCheck (innerAD leaf2029Box) leaf2029InnerLog = true := by
  rfl'

private theorem leaf2029InnerLogValid :
    leaf2029InnerLog.Valid 8 (innerAD leaf2029Box) :=
  wideLogDataValid_of_cachedCheck endpoint43PositiveFacts
    endpoint47PositiveFacts.valid leaf2029CoverageChecked

private noncomputable def leaf2029InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814625/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2029InputLogOnePlusV_eq :
    leaf2029InputLogOnePlusV = outerEnclosure 24
      (leaf2029Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2029RoundedFacts : LeafRoundedFacts 8
    leaf2029Certificate.logOnePlusV leaf2029InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2029InputLogOnePlusV_eq }

private noncomputable def leaf2029Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi133InputQChi innerPair156Input
    leaf2029InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2029LowerChecked :
    lowerCheck 24 leaf2029Box leaf2029Inputs = true := by
  rfl'

private theorem leaf2029CoversExact : CoversExact 8
    leaf2029Box leaf2029Certificate leaf2029InnerLog leaf2029Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi133RoundedFacts
    innerPair156RoundedFacts leaf2029RoundedFacts (by rfl)

private theorem leaf2029FlatSound : Sound leaf2029Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2029CertificateValid
    leaf2029InnerLogValid leaf2029CoversExact leaf2029LowerChecked

private noncomputable def leaf2030Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (45/256), chiHi := (23/128) }

private noncomputable def leaf2030Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871209/536870912) }, vSqrt := { lower := (65529/65536), upper := (13743698739/13743410176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (837629729/536870912) }, upper := { exponent := 0, mantissa := (6465/4096) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi134LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (27487108915/27486820352) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf2030InnerLog : WideLogData :=
  innerPair154Data

set_option maxRecDepth 1000000 in
private theorem leaf2030LocalValidity :
    LeafFacts leaf2030Box leaf2030Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2030Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (13743698739/13743410176) }) = true
      norm_num [leaf2030Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2030CertificateValid :
    WideCertificateValid leaf2030Box leaf2030Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi134ValidityFacts
    leaf2030LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2030CoverageChecked :
    coverageCheck (innerAD leaf2030Box) leaf2030InnerLog = true := by
  rfl'

private theorem leaf2030InnerLogValid :
    leaf2030InnerLog.Valid 8 (innerAD leaf2030Box) :=
  wideLogDataValid_of_cachedCheck endpoint43PositiveFacts
    endpoint44PositiveFacts.valid leaf2030CoverageChecked

private noncomputable def leaf2030InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629257/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2030InputLogOnePlusV_eq :
    leaf2030InputLogOnePlusV = outerEnclosure 24
      (leaf2030Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2030RoundedFacts : LeafRoundedFacts 8
    leaf2030Certificate.logOnePlusV leaf2030InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2030InputLogOnePlusV_eq }

private noncomputable def leaf2030Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi134InputQChi innerPair154Input
    leaf2030InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2030LowerChecked :
    lowerCheck 24 leaf2030Box leaf2030Inputs = true := by
  rfl'

private theorem leaf2030CoversExact : CoversExact 8
    leaf2030Box leaf2030Certificate leaf2030InnerLog leaf2030Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi134RoundedFacts
    innerPair154RoundedFacts leaf2030RoundedFacts (by rfl)

private theorem leaf2030FlatSound : Sound leaf2030Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2030CertificateValid
    leaf2030InnerLogValid leaf2030CoversExact leaf2030LowerChecked

private noncomputable def leaf2031Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (11/64), chiHi := (45/256) }

private noncomputable def leaf2031Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871209/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717080576) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (833828873/536870912) }, upper := { exponent := 0, mantissa := (1609/1024) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi133LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435574271/137434161152) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf2031InnerLog : WideLogData :=
  innerPair156Data

set_option maxRecDepth 1000000 in
private theorem leaf2031LocalValidity :
    LeafFacts leaf2031Box leaf2031Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2031Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717080576) }) = true
      norm_num [leaf2031Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2031CertificateValid :
    WideCertificateValid leaf2031Box leaf2031Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi133ValidityFacts
    leaf2031LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2031CoverageChecked :
    coverageCheck (innerAD leaf2031Box) leaf2031InnerLog = true := by
  rfl'

private theorem leaf2031InnerLogValid :
    leaf2031InnerLog.Valid 8 (innerAD leaf2031Box) :=
  wideLogDataValid_of_cachedCheck endpoint43PositiveFacts
    endpoint47PositiveFacts.valid leaf2031CoverageChecked

private noncomputable def leaf2031InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629253/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2031InputLogOnePlusV_eq :
    leaf2031InputLogOnePlusV = outerEnclosure 24
      (leaf2031Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2031RoundedFacts : LeafRoundedFacts 8
    leaf2031Certificate.logOnePlusV leaf2031InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2031InputLogOnePlusV_eq }

private noncomputable def leaf2031Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi133InputQChi innerPair156Input
    leaf2031InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2031LowerChecked :
    lowerCheck 24 leaf2031Box leaf2031Inputs = true := by
  rfl'

private theorem leaf2031CoversExact : CoversExact 8
    leaf2031Box leaf2031Certificate leaf2031InnerLog leaf2031Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi133RoundedFacts
    innerPair156RoundedFacts leaf2031RoundedFacts (by rfl)

private theorem leaf2031FlatSound : Sound leaf2031Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2031CertificateValid
    leaf2031InnerLogValid leaf2031CoversExact leaf2031LowerChecked

private noncomputable def leaf2032Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (45/256), chiHi := (23/128) }

private noncomputable def leaf2032Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871211/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905675776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (840578667/536870912) }, upper := { exponent := 0, mantissa := (811/512) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi134LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811840341/45811351552) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf2032InnerLog : WideLogData :=
  innerPair54Data

set_option maxRecDepth 1000000 in
private theorem leaf2032LocalValidity :
    LeafFacts leaf2032Box leaf2032Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2032Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905675776) }) = true
      norm_num [leaf2032Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2032CertificateValid :
    WideCertificateValid leaf2032Box leaf2032Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi134ValidityFacts
    leaf2032LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2032CoverageChecked :
    coverageCheck (innerAD leaf2032Box) leaf2032InnerLog = true := by
  rfl'

private theorem leaf2032InnerLogValid :
    leaf2032InnerLog.Valid 8 (innerAD leaf2032Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint44PositiveFacts.valid leaf2032CoverageChecked

private noncomputable def leaf2032InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907315/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2032InputLogOnePlusV_eq :
    leaf2032InputLogOnePlusV = outerEnclosure 24
      (leaf2032Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2032RoundedFacts : LeafRoundedFacts 8
    leaf2032Certificate.logOnePlusV leaf2032InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2032InputLogOnePlusV_eq }

private noncomputable def leaf2032Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi134InputQChi innerPair54Input
    leaf2032InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2032LowerChecked :
    lowerCheck 24 leaf2032Box leaf2032Inputs = true := by
  rfl'

private theorem leaf2032CoversExact : CoversExact 8
    leaf2032Box leaf2032Certificate leaf2032InnerLog leaf2032Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi134RoundedFacts
    innerPair54RoundedFacts leaf2032RoundedFacts (by rfl)

private theorem leaf2032FlatSound : Sound leaf2032Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2032CertificateValid
    leaf2032InnerLogValid leaf2032CoversExact leaf2032LowerChecked

private noncomputable def leaf2033Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (23/128), chiHi := (47/256) }

private noncomputable def leaf2033Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871211/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905666048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (844313991/536870912) }, upper := { exponent := 0, mantissa := (13033/8192) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi135LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811830613/45811332096) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf2033InnerLog : WideLogData :=
  innerPair54Data

set_option maxRecDepth 1000000 in
private theorem leaf2033LocalValidity :
    LeafFacts leaf2033Box leaf2033Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2033Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905666048) }) = true
      norm_num [leaf2033Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2033CertificateValid :
    WideCertificateValid leaf2033Box leaf2033Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi135ValidityFacts
    leaf2033LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2033CoverageChecked :
    coverageCheck (innerAD leaf2033Box) leaf2033InnerLog = true := by
  rfl'

private theorem leaf2033InnerLogValid :
    leaf2033InnerLog.Valid 8 (innerAD leaf2033Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint44PositiveFacts.valid leaf2033CoverageChecked

private noncomputable def leaf2033InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629263/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2033InputLogOnePlusV_eq :
    leaf2033InputLogOnePlusV = outerEnclosure 24
      (leaf2033Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2033RoundedFacts : LeafRoundedFacts 8
    leaf2033Certificate.logOnePlusV leaf2033InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2033InputLogOnePlusV_eq }

private noncomputable def leaf2033Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi135InputQChi innerPair54Input
    leaf2033InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2033LowerChecked :
    lowerCheck 24 leaf2033Box leaf2033Inputs = true := by
  rfl'

private theorem leaf2033CoversExact : CoversExact 8
    leaf2033Box leaf2033Certificate leaf2033InnerLog leaf2033Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi135RoundedFacts
    innerPair54RoundedFacts leaf2033RoundedFacts (by rfl)

private theorem leaf2033FlatSound : Sound leaf2033Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2033CertificateValid
    leaf2033InnerLogValid leaf2033CoversExact leaf2033LowerChecked

private noncomputable def leaf2034Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (47/256), chiHi := (3/16) }

private noncomputable def leaf2034Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871213/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68716945408) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (850998253/536870912) }, upper := { exponent := 0, mantissa := (821/512) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi136LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435439103/137433890816) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf2034InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2034LocalValidity :
    LeafFacts leaf2034Box leaf2034Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2034Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68716945408) }) = true
      norm_num [leaf2034Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2034CertificateValid :
    WideCertificateValid leaf2034Box leaf2034Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi136ValidityFacts
    leaf2034LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2034CoverageChecked :
    coverageCheck (innerAD leaf2034Box) leaf2034InnerLog = true := by
  rfl'

private theorem leaf2034InnerLogValid :
    leaf2034InnerLog.Valid 8 (innerAD leaf2034Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2034CoverageChecked

private noncomputable def leaf2034InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814635/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2034InputLogOnePlusV_eq :
    leaf2034InputLogOnePlusV = outerEnclosure 24
      (leaf2034Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2034RoundedFacts : LeafRoundedFacts 8
    leaf2034Certificate.logOnePlusV leaf2034InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2034InputLogOnePlusV_eq }

private noncomputable def leaf2034Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi136InputQChi innerPair50Input
    leaf2034InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2034LowerChecked :
    lowerCheck 24 leaf2034Box leaf2034Inputs = true := by
  rfl'

private theorem leaf2034CoversExact : CoversExact 8
    leaf2034Box leaf2034Certificate leaf2034InnerLog leaf2034Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi136RoundedFacts
    innerPair50RoundedFacts leaf2034RoundedFacts (by rfl)

private theorem leaf2034FlatSound : Sound leaf2034Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2034CertificateValid
    leaf2034InnerLogValid leaf2034CoversExact leaf2034LowerChecked

private noncomputable def leaf2035Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (23/128), chiHi := (47/256) }

private noncomputable def leaf2035Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871213/536870912) }, vSqrt := { lower := (65529/65536), upper := (13743698739/13743394816) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (847328461/536870912) }, upper := { exponent := 0, mantissa := (1635/1024) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi135LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (27487093555/27486789632) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf2035InnerLog : WideLogData :=
  innerPair171Data

set_option maxRecDepth 1000000 in
private theorem leaf2035LocalValidity :
    LeafFacts leaf2035Box leaf2035Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2035Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (13743698739/13743394816) }) = true
      norm_num [leaf2035Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2035CertificateValid :
    WideCertificateValid leaf2035Box leaf2035Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi135ValidityFacts
    leaf2035LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2035CoverageChecked :
    coverageCheck (innerAD leaf2035Box) leaf2035InnerLog = true := by
  rfl'

private theorem leaf2035InnerLogValid :
    leaf2035InnerLog.Valid 8 (innerAD leaf2035Box) :=
  wideLogDataValid_of_cachedCheck endpoint47PositiveFacts
    endpoint46PositiveFacts.valid leaf2035CoverageChecked

private noncomputable def leaf2035InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814633/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2035InputLogOnePlusV_eq :
    leaf2035InputLogOnePlusV = outerEnclosure 24
      (leaf2035Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2035RoundedFacts : LeafRoundedFacts 8
    leaf2035Certificate.logOnePlusV leaf2035InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2035InputLogOnePlusV_eq }

private noncomputable def leaf2035Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi135InputQChi innerPair171Input
    leaf2035InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2035LowerChecked :
    lowerCheck 24 leaf2035Box leaf2035Inputs = true := by
  rfl'

private theorem leaf2035CoversExact : CoversExact 8
    leaf2035Box leaf2035Certificate leaf2035InnerLog leaf2035Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi135RoundedFacts
    innerPair171RoundedFacts leaf2035RoundedFacts (by rfl)

private theorem leaf2035FlatSound : Sound leaf2035Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2035CertificateValid
    leaf2035InnerLogValid leaf2035CoversExact leaf2035LowerChecked

private noncomputable def leaf2036Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (47/256), chiHi := (3/16) }

private noncomputable def leaf2036Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871215/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68716920832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (854078255/536870912) }, upper := { exponent := 0, mantissa := (103/64) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi136LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435414527/137433841664) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf2036InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2036LocalValidity :
    LeafFacts leaf2036Box leaf2036Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2036Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68716920832) }) = true
      norm_num [leaf2036Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2036CertificateValid :
    WideCertificateValid leaf2036Box leaf2036Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi136ValidityFacts
    leaf2036LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2036CoverageChecked :
    coverageCheck (innerAD leaf2036Box) leaf2036InnerLog = true := by
  rfl'

private theorem leaf2036InnerLogValid :
    leaf2036InnerLog.Valid 8 (innerAD leaf2036Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2036CoverageChecked

private noncomputable def leaf2036InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629273/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2036InputLogOnePlusV_eq :
    leaf2036InputLogOnePlusV = outerEnclosure 24
      (leaf2036Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2036RoundedFacts : LeafRoundedFacts 8
    leaf2036Certificate.logOnePlusV leaf2036InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2036InputLogOnePlusV_eq }

private noncomputable def leaf2036Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi136InputQChi innerPair50Input
    leaf2036InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2036LowerChecked :
    lowerCheck 24 leaf2036Box leaf2036Inputs = true := by
  rfl'

private theorem leaf2036CoversExact : CoversExact 8
    leaf2036Box leaf2036Certificate leaf2036InnerLog leaf2036Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi136RoundedFacts
    innerPair50RoundedFacts leaf2036RoundedFacts (by rfl)

private theorem leaf2036FlatSound : Sound leaf2036Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2036CertificateValid
    leaf2036InnerLogValid leaf2036CoversExact leaf2036LowerChecked

private noncomputable def component44Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component44Node0_sound : Sound component44Node0Box :=
  sound_of_literal_split component44Node0Box leaf1975Box leaf1976Box
    .chi (41/256) (by rfl) (by rfl)
    leaf1975FlatSound leaf1976FlatSound

private noncomputable def component44Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component44Node1_sound : Sound component44Node1Box :=
  sound_of_literal_split component44Node1Box leaf1974Box component44Node0Box
    .k (97/32) (by rfl) (by rfl)
    leaf1974FlatSound component44Node0_sound

private noncomputable def component44Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component44Node2_sound : Sound component44Node2Box :=
  sound_of_literal_split component44Node2Box leaf1977Box leaf1978Box
    .chi (43/256) (by rfl) (by rfl)
    leaf1977FlatSound leaf1978FlatSound

private noncomputable def component44Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component44Node3_sound : Sound component44Node3Box :=
  sound_of_literal_split component44Node3Box leaf1979Box leaf1980Box
    .chi (43/256) (by rfl) (by rfl)
    leaf1979FlatSound leaf1980FlatSound

private noncomputable def component44Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component44Node4_sound : Sound component44Node4Box :=
  sound_of_literal_split component44Node4Box component44Node2Box component44Node3Box
    .k (97/32) (by rfl) (by rfl)
    component44Node2_sound component44Node3_sound

private noncomputable def component44Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (5/32), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component44Node5_sound : Sound component44Node5Box :=
  sound_of_literal_split component44Node5Box component44Node1Box component44Node4Box
    .chi (21/128) (by rfl) (by rfl)
    component44Node1_sound component44Node4_sound

private noncomputable def component44Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component44Node6_sound : Sound component44Node6Box :=
  sound_of_literal_split component44Node6Box leaf1981Box leaf1982Box
    .chi (41/256) (by rfl) (by rfl)
    leaf1981FlatSound leaf1982FlatSound

private noncomputable def component44Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component44Node7_sound : Sound component44Node7Box :=
  sound_of_literal_split component44Node7Box leaf1983Box leaf1984Box
    .chi (41/256) (by rfl) (by rfl)
    leaf1983FlatSound leaf1984FlatSound

private noncomputable def component44Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component44Node8_sound : Sound component44Node8Box :=
  sound_of_literal_split component44Node8Box component44Node6Box component44Node7Box
    .k (99/32) (by rfl) (by rfl)
    component44Node6_sound component44Node7_sound

private noncomputable def component44Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component44Node9_sound : Sound component44Node9Box :=
  sound_of_literal_split component44Node9Box leaf1985Box leaf1986Box
    .chi (43/256) (by rfl) (by rfl)
    leaf1985FlatSound leaf1986FlatSound

private noncomputable def component44Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component44Node10_sound : Sound component44Node10Box :=
  sound_of_literal_split component44Node10Box leaf1987Box leaf1988Box
    .chi (43/256) (by rfl) (by rfl)
    leaf1987FlatSound leaf1988FlatSound

private noncomputable def component44Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component44Node11_sound : Sound component44Node11Box :=
  sound_of_literal_split component44Node11Box component44Node9Box component44Node10Box
    .k (99/32) (by rfl) (by rfl)
    component44Node9_sound component44Node10_sound

private noncomputable def component44Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (5/32), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component44Node12_sound : Sound component44Node12Box :=
  sound_of_literal_split component44Node12Box component44Node8Box component44Node11Box
    .chi (21/128) (by rfl) (by rfl)
    component44Node8_sound component44Node11_sound

private noncomputable def component44Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (5/32), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component44Node13_sound : Sound component44Node13Box :=
  sound_of_literal_split component44Node13Box component44Node5Box component44Node12Box
    .k (49/16) (by rfl) (by rfl)
    component44Node5_sound component44Node12_sound

private noncomputable def component44Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (11/64), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component44Node14_sound : Sound component44Node14Box :=
  sound_of_literal_split component44Node14Box leaf1989Box leaf1990Box
    .chi (45/256) (by rfl) (by rfl)
    leaf1989FlatSound leaf1990FlatSound

private noncomputable def component44Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (11/64), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component44Node15_sound : Sound component44Node15Box :=
  sound_of_literal_split component44Node15Box leaf1991Box leaf1992Box
    .chi (45/256) (by rfl) (by rfl)
    leaf1991FlatSound leaf1992FlatSound

private noncomputable def component44Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (11/64), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component44Node16_sound : Sound component44Node16Box :=
  sound_of_literal_split component44Node16Box component44Node14Box component44Node15Box
    .k (97/32) (by rfl) (by rfl)
    component44Node14_sound component44Node15_sound

private noncomputable def component44Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (23/128), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component44Node17_sound : Sound component44Node17Box :=
  sound_of_literal_split component44Node17Box leaf1993Box leaf1994Box
    .chi (47/256) (by rfl) (by rfl)
    leaf1993FlatSound leaf1994FlatSound

private noncomputable def component44Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (23/128), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component44Node18_sound : Sound component44Node18Box :=
  sound_of_literal_split component44Node18Box leaf1995Box leaf1996Box
    .chi (47/256) (by rfl) (by rfl)
    leaf1995FlatSound leaf1996FlatSound

private noncomputable def component44Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (23/128), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component44Node19_sound : Sound component44Node19Box :=
  sound_of_literal_split component44Node19Box component44Node17Box component44Node18Box
    .k (97/32) (by rfl) (by rfl)
    component44Node17_sound component44Node18_sound

private noncomputable def component44Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (11/64), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component44Node20_sound : Sound component44Node20Box :=
  sound_of_literal_split component44Node20Box component44Node16Box component44Node19Box
    .chi (23/128) (by rfl) (by rfl)
    component44Node16_sound component44Node19_sound

private noncomputable def component44Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (11/64), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component44Node21_sound : Sound component44Node21Box :=
  sound_of_literal_split component44Node21Box leaf1997Box leaf1998Box
    .chi (45/256) (by rfl) (by rfl)
    leaf1997FlatSound leaf1998FlatSound

private noncomputable def component44Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (11/64), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component44Node22_sound : Sound component44Node22Box :=
  sound_of_literal_split component44Node22Box leaf1999Box leaf2000Box
    .chi (45/256) (by rfl) (by rfl)
    leaf1999FlatSound leaf2000FlatSound

private noncomputable def component44Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (11/64), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component44Node23_sound : Sound component44Node23Box :=
  sound_of_literal_split component44Node23Box component44Node21Box component44Node22Box
    .k (99/32) (by rfl) (by rfl)
    component44Node21_sound component44Node22_sound

private noncomputable def component44Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (23/128), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component44Node24_sound : Sound component44Node24Box :=
  sound_of_literal_split component44Node24Box leaf2001Box leaf2002Box
    .chi (47/256) (by rfl) (by rfl)
    leaf2001FlatSound leaf2002FlatSound

private noncomputable def component44Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (23/128), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component44Node25_sound : Sound component44Node25Box :=
  sound_of_literal_split component44Node25Box leaf2003Box leaf2004Box
    .chi (47/256) (by rfl) (by rfl)
    leaf2003FlatSound leaf2004FlatSound

private noncomputable def component44Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (23/128), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component44Node26_sound : Sound component44Node26Box :=
  sound_of_literal_split component44Node26Box component44Node24Box component44Node25Box
    .k (99/32) (by rfl) (by rfl)
    component44Node24_sound component44Node25_sound

private noncomputable def component44Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (11/64), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component44Node27_sound : Sound component44Node27Box :=
  sound_of_literal_split component44Node27Box component44Node23Box component44Node26Box
    .chi (23/128) (by rfl) (by rfl)
    component44Node23_sound component44Node26_sound

private noncomputable def component44Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (11/64), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component44Node28_sound : Sound component44Node28Box :=
  sound_of_literal_split component44Node28Box component44Node20Box component44Node27Box
    .k (49/16) (by rfl) (by rfl)
    component44Node20_sound component44Node27_sound

private noncomputable def component44Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (5/32), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component44Node29_sound : Sound component44Node29Box :=
  sound_of_literal_split component44Node29Box component44Node13Box component44Node28Box
    .chi (11/64) (by rfl) (by rfl)
    component44Node13_sound component44Node28_sound

private noncomputable def component44Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component44Node30_sound : Sound component44Node30Box :=
  sound_of_literal_split component44Node30Box leaf2005Box leaf2006Box
    .chi (41/256) (by rfl) (by rfl)
    leaf2005FlatSound leaf2006FlatSound

private noncomputable def component44Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component44Node31_sound : Sound component44Node31Box :=
  sound_of_literal_split component44Node31Box leaf2007Box leaf2008Box
    .chi (41/256) (by rfl) (by rfl)
    leaf2007FlatSound leaf2008FlatSound

private noncomputable def component44Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component44Node32_sound : Sound component44Node32Box :=
  sound_of_literal_split component44Node32Box component44Node30Box component44Node31Box
    .k (101/32) (by rfl) (by rfl)
    component44Node30_sound component44Node31_sound

private noncomputable def component44Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component44Node33_sound : Sound component44Node33Box :=
  sound_of_literal_split component44Node33Box leaf2009Box leaf2010Box
    .chi (43/256) (by rfl) (by rfl)
    leaf2009FlatSound leaf2010FlatSound

private noncomputable def component44Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component44Node34_sound : Sound component44Node34Box :=
  sound_of_literal_split component44Node34Box leaf2011Box leaf2012Box
    .chi (43/256) (by rfl) (by rfl)
    leaf2011FlatSound leaf2012FlatSound

private noncomputable def component44Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component44Node35_sound : Sound component44Node35Box :=
  sound_of_literal_split component44Node35Box component44Node33Box component44Node34Box
    .k (101/32) (by rfl) (by rfl)
    component44Node33_sound component44Node34_sound

private noncomputable def component44Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (5/32), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component44Node36_sound : Sound component44Node36Box :=
  sound_of_literal_split component44Node36Box component44Node32Box component44Node35Box
    .chi (21/128) (by rfl) (by rfl)
    component44Node32_sound component44Node35_sound

private noncomputable def component44Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component44Node37_sound : Sound component44Node37Box :=
  sound_of_literal_split component44Node37Box leaf2013Box leaf2014Box
    .chi (41/256) (by rfl) (by rfl)
    leaf2013FlatSound leaf2014FlatSound

private noncomputable def component44Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component44Node38_sound : Sound component44Node38Box :=
  sound_of_literal_split component44Node38Box leaf2015Box leaf2016Box
    .chi (41/256) (by rfl) (by rfl)
    leaf2015FlatSound leaf2016FlatSound

private noncomputable def component44Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component44Node39_sound : Sound component44Node39Box :=
  sound_of_literal_split component44Node39Box component44Node37Box component44Node38Box
    .k (103/32) (by rfl) (by rfl)
    component44Node37_sound component44Node38_sound

private noncomputable def component44Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component44Node40_sound : Sound component44Node40Box :=
  sound_of_literal_split component44Node40Box leaf2017Box leaf2018Box
    .chi (43/256) (by rfl) (by rfl)
    leaf2017FlatSound leaf2018FlatSound

private noncomputable def component44Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component44Node41_sound : Sound component44Node41Box :=
  sound_of_literal_split component44Node41Box leaf2019Box leaf2020Box
    .chi (43/256) (by rfl) (by rfl)
    leaf2019FlatSound leaf2020FlatSound

private noncomputable def component44Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component44Node42_sound : Sound component44Node42Box :=
  sound_of_literal_split component44Node42Box component44Node40Box component44Node41Box
    .k (103/32) (by rfl) (by rfl)
    component44Node40_sound component44Node41_sound

private noncomputable def component44Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (5/32), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component44Node43_sound : Sound component44Node43Box :=
  sound_of_literal_split component44Node43Box component44Node39Box component44Node42Box
    .chi (21/128) (by rfl) (by rfl)
    component44Node39_sound component44Node42_sound

private noncomputable def component44Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (5/32), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component44Node44_sound : Sound component44Node44Box :=
  sound_of_literal_split component44Node44Box component44Node36Box component44Node43Box
    .k (51/16) (by rfl) (by rfl)
    component44Node36_sound component44Node43_sound

private noncomputable def component44Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (11/64), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component44Node45_sound : Sound component44Node45Box :=
  sound_of_literal_split component44Node45Box leaf2021Box leaf2022Box
    .chi (45/256) (by rfl) (by rfl)
    leaf2021FlatSound leaf2022FlatSound

private noncomputable def component44Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (11/64), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component44Node46_sound : Sound component44Node46Box :=
  sound_of_literal_split component44Node46Box leaf2023Box leaf2024Box
    .chi (45/256) (by rfl) (by rfl)
    leaf2023FlatSound leaf2024FlatSound

private noncomputable def component44Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (11/64), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component44Node47_sound : Sound component44Node47Box :=
  sound_of_literal_split component44Node47Box component44Node45Box component44Node46Box
    .k (101/32) (by rfl) (by rfl)
    component44Node45_sound component44Node46_sound

private noncomputable def component44Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (23/128), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component44Node48_sound : Sound component44Node48Box :=
  sound_of_literal_split component44Node48Box leaf2025Box leaf2026Box
    .chi (47/256) (by rfl) (by rfl)
    leaf2025FlatSound leaf2026FlatSound

private noncomputable def component44Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (23/128), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component44Node49_sound : Sound component44Node49Box :=
  sound_of_literal_split component44Node49Box leaf2027Box leaf2028Box
    .chi (47/256) (by rfl) (by rfl)
    leaf2027FlatSound leaf2028FlatSound

private noncomputable def component44Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (23/128), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component44Node50_sound : Sound component44Node50Box :=
  sound_of_literal_split component44Node50Box component44Node48Box component44Node49Box
    .k (101/32) (by rfl) (by rfl)
    component44Node48_sound component44Node49_sound

private noncomputable def component44Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (11/64), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component44Node51_sound : Sound component44Node51Box :=
  sound_of_literal_split component44Node51Box component44Node47Box component44Node50Box
    .chi (23/128) (by rfl) (by rfl)
    component44Node47_sound component44Node50_sound

private noncomputable def component44Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (11/64), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component44Node52_sound : Sound component44Node52Box :=
  sound_of_literal_split component44Node52Box leaf2029Box leaf2030Box
    .chi (45/256) (by rfl) (by rfl)
    leaf2029FlatSound leaf2030FlatSound

private noncomputable def component44Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (11/64), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component44Node53_sound : Sound component44Node53Box :=
  sound_of_literal_split component44Node53Box leaf2031Box leaf2032Box
    .chi (45/256) (by rfl) (by rfl)
    leaf2031FlatSound leaf2032FlatSound

private noncomputable def component44Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (11/64), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component44Node54_sound : Sound component44Node54Box :=
  sound_of_literal_split component44Node54Box component44Node52Box component44Node53Box
    .k (103/32) (by rfl) (by rfl)
    component44Node52_sound component44Node53_sound

private noncomputable def component44Node55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (23/128), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component44Node55_sound : Sound component44Node55Box :=
  sound_of_literal_split component44Node55Box leaf2033Box leaf2034Box
    .chi (47/256) (by rfl) (by rfl)
    leaf2033FlatSound leaf2034FlatSound

private noncomputable def component44Node56Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (23/128), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component44Node56_sound : Sound component44Node56Box :=
  sound_of_literal_split component44Node56Box leaf2035Box leaf2036Box
    .chi (47/256) (by rfl) (by rfl)
    leaf2035FlatSound leaf2036FlatSound

private noncomputable def component44Node57Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (23/128), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component44Node57_sound : Sound component44Node57Box :=
  sound_of_literal_split component44Node57Box component44Node55Box component44Node56Box
    .k (103/32) (by rfl) (by rfl)
    component44Node55_sound component44Node56_sound

private noncomputable def component44Node58Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (11/64), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component44Node58_sound : Sound component44Node58Box :=
  sound_of_literal_split component44Node58Box component44Node54Box component44Node57Box
    .chi (23/128) (by rfl) (by rfl)
    component44Node54_sound component44Node57_sound

private noncomputable def component44Node59Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (11/64), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component44Node59_sound : Sound component44Node59Box :=
  sound_of_literal_split component44Node59Box component44Node51Box component44Node58Box
    .k (51/16) (by rfl) (by rfl)
    component44Node51_sound component44Node58_sound

private noncomputable def component44Node60Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (5/32), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component44Node60_sound : Sound component44Node60Box :=
  sound_of_literal_split component44Node60Box component44Node44Box component44Node59Box
    .chi (11/64) (by rfl) (by rfl)
    component44Node44_sound component44Node59_sound

noncomputable def component44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (13/4), chiLo := (5/32), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
theorem component44_sound : Sound component44Box :=
  sound_of_literal_split component44Box component44Node29Box component44Node60Box
    .k (25/8) (by rfl) (by rfl)
    component44Node29_sound component44Node60_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
