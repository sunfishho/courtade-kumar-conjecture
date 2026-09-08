import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch3
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

private noncomputable def leaf443Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (25/16), chiLo := (3/8), chiHi := (25/64) }

private noncomputable def leaf443Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108963/67108864) }, vSqrt := { lower := (16383/16384), upper := (11453093205/11452819456) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (104822431/67108864) }, upper := { exponent := 0, mantissa := (1649/1024) } }, logOuter := sk35LogOuterCertificate, logK := sk35LogKCertificate, logChi := chi62LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (22905912661/22905638912) } }, logDArg := sk35LogDArgCertificate }

private noncomputable def leaf443InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf443LocalValidity :
    LeafFacts leaf443Box leaf443Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf443Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (11453093205/11452819456) }) = true
      norm_num [leaf443Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf443CertificateValid :
    WideCertificateValid leaf443Box leaf443Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk35ValidityFacts chi62ValidityFacts
    leaf443LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf443CoverageChecked :
    coverageCheck (innerAD leaf443Box) leaf443InnerLog = true := by
  rfl'

private theorem leaf443InnerLogValid :
    leaf443InnerLog.Valid 8 (innerAD leaf443Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf443CoverageChecked

private noncomputable def leaf443InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629281/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf443InputLogOnePlusV_eq :
    leaf443InputLogOnePlusV = outerEnclosure 24
      (leaf443Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf443RoundedFacts : LeafRoundedFacts 8
    leaf443Certificate.logOnePlusV leaf443InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf443InputLogOnePlusV_eq }

private noncomputable def leaf443Inputs : Inputs :=
  inputsOfCaches globalInput sk35RoundedInputs
    chi62InputQChi innerPair41Input
    leaf443InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf443LowerChecked :
    lowerCheck 24 leaf443Box leaf443Inputs = true := by
  rfl'

private theorem leaf443CoversExact : CoversExact 8
    leaf443Box leaf443Certificate leaf443InnerLog leaf443Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk35RoundedFacts chi62RoundedFacts
    innerPair41RoundedFacts leaf443RoundedFacts (by rfl)

private theorem leaf443FlatSound : Sound leaf443Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf443CertificateValid
    leaf443InnerLogValid leaf443CoversExact leaf443LowerChecked

private noncomputable def leaf444Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (25/16), chiLo := (25/64), chiHi := (13/32) }

private noncomputable def leaf444Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108965/67108864) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34358407168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (106395197/67108864) }, upper := { exponent := 0, mantissa := (837/512) } }, logOuter := sk35LogOuterCertificate, logK := sk35LogKCertificate, logChi := chi63LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717686783/68716814336) } }, logDArg := sk35LogDArgCertificate }

private noncomputable def leaf444InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf444LocalValidity :
    LeafFacts leaf444Box leaf444Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf444Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34358407168) }) = true
      norm_num [leaf444Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf444CertificateValid :
    WideCertificateValid leaf444Box leaf444Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk35ValidityFacts chi63ValidityFacts
    leaf444LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf444CoverageChecked :
    coverageCheck (innerAD leaf444Box) leaf444InnerLog = true := by
  rfl'

private theorem leaf444InnerLogValid :
    leaf444InnerLog.Valid 8 (innerAD leaf444Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf444CoverageChecked

private noncomputable def leaf444InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814647/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf444InputLogOnePlusV_eq :
    leaf444InputLogOnePlusV = outerEnclosure 24
      (leaf444Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf444RoundedFacts : LeafRoundedFacts 8
    leaf444Certificate.logOnePlusV leaf444InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf444InputLogOnePlusV_eq }

private noncomputable def leaf444Inputs : Inputs :=
  inputsOfCaches globalInput sk35RoundedInputs
    chi63InputQChi innerPair51Input
    leaf444InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf444LowerChecked :
    lowerCheck 24 leaf444Box leaf444Inputs = true := by
  rfl'

private theorem leaf444CoversExact : CoversExact 8
    leaf444Box leaf444Certificate leaf444InnerLog leaf444Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk35RoundedFacts chi63RoundedFacts
    innerPair51RoundedFacts leaf444RoundedFacts (by rfl)

private theorem leaf444FlatSound : Sound leaf444Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf444CertificateValid
    leaf444InnerLogValid leaf444CoversExact leaf444LowerChecked

private noncomputable def leaf445Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (25/16), chiLo := (13/32), chiHi := (7/16) }

private noncomputable def leaf445Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554509/33554432) }, vSqrt := { lower := (16383/16384), upper := (11453093205/11452768256) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (53967573/33554432) }, upper := { exponent := 0, mantissa := (431/256) } }, logOuter := sk35LogOuterCertificate, logK := sk35LogKCertificate, logChi := chi51LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (22905861461/22905536512) } }, logDArg := sk35LogDArgCertificate }

private noncomputable def leaf445InnerLog : WideLogData :=
  innerPair193Data

set_option maxRecDepth 1000000 in
private theorem leaf445LocalValidity :
    LeafFacts leaf445Box leaf445Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf445Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (11453093205/11452768256) }) = true
      norm_num [leaf445Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf445CertificateValid :
    WideCertificateValid leaf445Box leaf445Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk35ValidityFacts chi51ValidityFacts
    leaf445LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf445CoverageChecked :
    coverageCheck (innerAD leaf445Box) leaf445InnerLog = true := by
  rfl'

private theorem leaf445InnerLogValid :
    leaf445InnerLog.Valid 8 (innerAD leaf445Box) :=
  wideLogDataValid_of_cachedCheck endpoint57PositiveFacts
    endpoint58PositiveFacts.valid leaf445CoverageChecked

private noncomputable def leaf445InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629319/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf445InputLogOnePlusV_eq :
    leaf445InputLogOnePlusV = outerEnclosure 24
      (leaf445Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf445RoundedFacts : LeafRoundedFacts 8
    leaf445Certificate.logOnePlusV leaf445InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf445InputLogOnePlusV_eq }

private noncomputable def leaf445Inputs : Inputs :=
  inputsOfCaches globalInput sk35RoundedInputs
    chi51InputQChi innerPair193Input
    leaf445InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf445LowerChecked :
    lowerCheck 24 leaf445Box leaf445Inputs = true := by
  rfl'

private theorem leaf445CoversExact : CoversExact 8
    leaf445Box leaf445Certificate leaf445InnerLog leaf445Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk35RoundedFacts chi51RoundedFacts
    innerPair193RoundedFacts leaf445RoundedFacts (by rfl)

private theorem leaf445FlatSound : Sound leaf445Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf445CertificateValid
    leaf445InnerLogValid leaf445CoversExact leaf445LowerChecked

private noncomputable def leaf446Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/16), kHi := (13/8), chiLo := (3/8), chiHi := (25/64) }

private noncomputable def leaf446Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108965/67108864) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34358407168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (106395197/67108864) }, upper := { exponent := 0, mantissa := (837/512) } }, logOuter := sk36LogOuterCertificate, logK := sk36LogKCertificate, logChi := chi62LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717686783/68716814336) } }, logDArg := sk36LogDArgCertificate }

private noncomputable def leaf446InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf446LocalValidity :
    LeafFacts leaf446Box leaf446Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf446Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34358407168) }) = true
      norm_num [leaf446Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf446CertificateValid :
    WideCertificateValid leaf446Box leaf446Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk36ValidityFacts chi62ValidityFacts
    leaf446LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf446CoverageChecked :
    coverageCheck (innerAD leaf446Box) leaf446InnerLog = true := by
  rfl'

private theorem leaf446InnerLogValid :
    leaf446InnerLog.Valid 8 (innerAD leaf446Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf446CoverageChecked

private noncomputable def leaf446InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814647/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf446InputLogOnePlusV_eq :
    leaf446InputLogOnePlusV = outerEnclosure 24
      (leaf446Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf446RoundedFacts : LeafRoundedFacts 8
    leaf446Certificate.logOnePlusV leaf446InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf446InputLogOnePlusV_eq }

private noncomputable def leaf446Inputs : Inputs :=
  inputsOfCaches globalInput sk36RoundedInputs
    chi62InputQChi innerPair51Input
    leaf446InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf446LowerChecked :
    lowerCheck 24 leaf446Box leaf446Inputs = true := by
  rfl'

private theorem leaf446CoversExact : CoversExact 8
    leaf446Box leaf446Certificate leaf446InnerLog leaf446Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk36RoundedFacts chi62RoundedFacts
    innerPair51RoundedFacts leaf446RoundedFacts (by rfl)

private theorem leaf446FlatSound : Sound leaf446Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf446CertificateValid
    leaf446InnerLogValid leaf446CoversExact leaf446LowerChecked

private noncomputable def leaf447Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/16), kHi := (13/8), chiLo := (25/64), chiHi := (13/32) }

private noncomputable def leaf447Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108967/67108864) }, vSqrt := { lower := (16383/16384), upper := (763539547/763518976) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (108033495/67108864) }, upper := { exponent := 0, mantissa := (425/256) } }, logOuter := sk36LogOuterCertificate, logK := sk36LogKCertificate, logChi := chi63LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (1527058523/1527037952) } }, logDArg := sk36LogDArgCertificate }

private noncomputable def leaf447InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf447LocalValidity :
    LeafFacts leaf447Box leaf447Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf447Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (763539547/763518976) }) = true
      norm_num [leaf447Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf447CertificateValid :
    WideCertificateValid leaf447Box leaf447Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk36ValidityFacts chi63ValidityFacts
    leaf447LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf447CoverageChecked :
    coverageCheck (innerAD leaf447Box) leaf447InnerLog = true := by
  rfl'

private theorem leaf447InnerLogValid :
    leaf447InnerLog.Valid 8 (innerAD leaf447Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf447CoverageChecked

private noncomputable def leaf447InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629307/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf447InputLogOnePlusV_eq :
    leaf447InputLogOnePlusV = outerEnclosure 24
      (leaf447Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf447RoundedFacts : LeafRoundedFacts 8
    leaf447Certificate.logOnePlusV leaf447InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf447InputLogOnePlusV_eq }

private noncomputable def leaf447Inputs : Inputs :=
  inputsOfCaches globalInput sk36RoundedInputs
    chi63InputQChi innerPair51Input
    leaf447InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf447LowerChecked :
    lowerCheck 24 leaf447Box leaf447Inputs = true := by
  rfl'

private theorem leaf447CoversExact : CoversExact 8
    leaf447Box leaf447Certificate leaf447InnerLog leaf447Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk36RoundedFacts chi63RoundedFacts
    innerPair51RoundedFacts leaf447RoundedFacts (by rfl)

private theorem leaf447FlatSound : Sound leaf447Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf447CertificateValid
    leaf447InnerLogValid leaf447CoversExact leaf447LowerChecked

private noncomputable def leaf448Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/16), kHi := (13/8), chiLo := (13/32), chiHi := (27/64) }

private noncomputable def leaf448Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108969/67108864) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34358300672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (109671793/67108864) }, upper := { exponent := 0, mantissa := (863/512) } }, logOuter := sk36LogOuterCertificate, logK := sk36LogKCertificate, logChi := chi64LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717580287/68716601344) } }, logDArg := sk36LogDArgCertificate }

private noncomputable def leaf448InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf448LocalValidity :
    LeafFacts leaf448Box leaf448Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf448Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34358300672) }) = true
      norm_num [leaf448Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf448CertificateValid :
    WideCertificateValid leaf448Box leaf448Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk36ValidityFacts chi64ValidityFacts
    leaf448LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf448CoverageChecked :
    coverageCheck (innerAD leaf448Box) leaf448InnerLog = true := by
  rfl'

private theorem leaf448InnerLogValid :
    leaf448InnerLog.Valid 8 (innerAD leaf448Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf448CoverageChecked

private noncomputable def leaf448InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (1453665/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf448InputLogOnePlusV_eq :
    leaf448InputLogOnePlusV = outerEnclosure 24
      (leaf448Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf448RoundedFacts : LeafRoundedFacts 8
    leaf448Certificate.logOnePlusV leaf448InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf448InputLogOnePlusV_eq }

private noncomputable def leaf448Inputs : Inputs :=
  inputsOfCaches globalInput sk36RoundedInputs
    chi64InputQChi innerPair56Input
    leaf448InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf448LowerChecked :
    lowerCheck 24 leaf448Box leaf448Inputs = true := by
  rfl'

private theorem leaf448CoversExact : CoversExact 8
    leaf448Box leaf448Certificate leaf448InnerLog leaf448Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk36RoundedFacts chi64RoundedFacts
    innerPair56RoundedFacts leaf448RoundedFacts (by rfl)

private theorem leaf448FlatSound : Sound leaf448Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf448CertificateValid
    leaf448InnerLogValid leaf448CoversExact leaf448LowerChecked

private noncomputable def leaf449Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/16), kHi := (13/8), chiLo := (27/64), chiHi := (7/16) }

private noncomputable def leaf449Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108971/67108864) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34358247424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (111310091/67108864) }, upper := { exponent := 0, mantissa := (219/128) } }, logOuter := sk36LogOuterCertificate, logK := sk36LogKCertificate, logChi := chi65LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717527039/68716494848) } }, logDArg := sk36LogDArgCertificate }

private noncomputable def leaf449InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf449LocalValidity :
    LeafFacts leaf449Box leaf449Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf449Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34358247424) }) = true
      norm_num [leaf449Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf449CertificateValid :
    WideCertificateValid leaf449Box leaf449Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk36ValidityFacts chi65ValidityFacts
    leaf449LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf449CoverageChecked :
    coverageCheck (innerAD leaf449Box) leaf449InnerLog = true := by
  rfl'

private theorem leaf449InnerLogValid :
    leaf449InnerLog.Valid 8 (innerAD leaf449Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf449CoverageChecked

private noncomputable def leaf449InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629333/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf449InputLogOnePlusV_eq :
    leaf449InputLogOnePlusV = outerEnclosure 24
      (leaf449Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf449RoundedFacts : LeafRoundedFacts 8
    leaf449Certificate.logOnePlusV leaf449InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf449InputLogOnePlusV_eq }

private noncomputable def leaf449Inputs : Inputs :=
  inputsOfCaches globalInput sk36RoundedInputs
    chi65InputQChi innerPair57Input
    leaf449InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf449LowerChecked :
    lowerCheck 24 leaf449Box leaf449Inputs = true := by
  rfl'

private theorem leaf449CoversExact : CoversExact 8
    leaf449Box leaf449Certificate leaf449InnerLog leaf449Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk36RoundedFacts chi65RoundedFacts
    innerPair57RoundedFacts leaf449RoundedFacts (by rfl)

private theorem leaf449FlatSound : Sound leaf449Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf449CertificateValid
    leaf449InnerLogValid leaf449CoversExact leaf449LowerChecked

private noncomputable def leaf450Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (25/16), chiLo := (7/16), chiHi := (15/32) }

private noncomputable def leaf450Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554511/33554432) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34358202368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (55540339/33554432) }, upper := { exponent := 0, mantissa := (887/512) } }, logOuter := sk35LogOuterCertificate, logK := sk35LogKCertificate, logChi := chi52LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717481983/68716404736) } }, logDArg := sk35LogDArgCertificate }

private noncomputable def leaf450InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf450LocalValidity :
    LeafFacts leaf450Box leaf450Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf450Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34358202368) }) = true
      norm_num [leaf450Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf450CertificateValid :
    WideCertificateValid leaf450Box leaf450Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk35ValidityFacts chi52ValidityFacts
    leaf450LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf450CoverageChecked :
    coverageCheck (innerAD leaf450Box) leaf450InnerLog = true := by
  rfl'

private theorem leaf450InnerLogValid :
    leaf450InnerLog.Valid 8 (innerAD leaf450Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf450CoverageChecked

private noncomputable def leaf450InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (363417/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf450InputLogOnePlusV_eq :
    leaf450InputLogOnePlusV = outerEnclosure 24
      (leaf450Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf450RoundedFacts : LeafRoundedFacts 8
    leaf450Certificate.logOnePlusV leaf450InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf450InputLogOnePlusV_eq }

private noncomputable def leaf450Inputs : Inputs :=
  inputsOfCaches globalInput sk35RoundedInputs
    chi52InputQChi innerPair57Input
    leaf450InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf450LowerChecked :
    lowerCheck 24 leaf450Box leaf450Inputs = true := by
  rfl'

private theorem leaf450CoversExact : CoversExact 8
    leaf450Box leaf450Certificate leaf450InnerLog leaf450Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk35RoundedFacts chi52RoundedFacts
    innerPair57RoundedFacts leaf450RoundedFacts (by rfl)

private theorem leaf450FlatSound : Sound leaf450Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf450CertificateValid
    leaf450InnerLogValid leaf450CoversExact leaf450LowerChecked

private noncomputable def leaf451Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (25/16), chiLo := (15/32), chiHi := (1/2) }

private noncomputable def leaf451Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554513/33554432) }, vSqrt := { lower := (16383/16384), upper := (2021134095/2021064704) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (57113105/33554432) }, upper := { exponent := 0, mantissa := (57/32) } }, logOuter := sk35LogOuterCertificate, logK := sk35LogKCertificate, logChi := chi53LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (4042198799/4042129408) } }, logDArg := sk35LogDArgCertificate }

private noncomputable def leaf451InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf451LocalValidity :
    LeafFacts leaf451Box leaf451Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf451Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (2021134095/2021064704) }) = true
      norm_num [leaf451Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf451CertificateValid :
    WideCertificateValid leaf451Box leaf451Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk35ValidityFacts chi53ValidityFacts
    leaf451LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf451CoverageChecked :
    coverageCheck (innerAD leaf451Box) leaf451InnerLog = true := by
  rfl'

private theorem leaf451InnerLogValid :
    leaf451InnerLog.Valid 8 (innerAD leaf451Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf451CoverageChecked

private noncomputable def leaf451InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629369/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf451InputLogOnePlusV_eq :
    leaf451InputLogOnePlusV = outerEnclosure 24
      (leaf451Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf451RoundedFacts : LeafRoundedFacts 8
    leaf451Certificate.logOnePlusV leaf451InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf451InputLogOnePlusV_eq }

private noncomputable def leaf451Inputs : Inputs :=
  inputsOfCaches globalInput sk35RoundedInputs
    chi53InputQChi innerPair66Input
    leaf451InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf451LowerChecked :
    lowerCheck 24 leaf451Box leaf451Inputs = true := by
  rfl'

private theorem leaf451CoversExact : CoversExact 8
    leaf451Box leaf451Certificate leaf451InnerLog leaf451Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk35RoundedFacts chi53RoundedFacts
    innerPair66RoundedFacts leaf451RoundedFacts (by rfl)

private theorem leaf451FlatSound : Sound leaf451Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf451CertificateValid
    leaf451InnerLogValid leaf451CoversExact leaf451LowerChecked

private noncomputable def leaf452Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/16), kHi := (13/8), chiLo := (7/16), chiHi := (15/32) }

private noncomputable def leaf452Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554513/33554432) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34358140928) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (56457785/33554432) }, upper := { exponent := 0, mantissa := (451/256) } }, logOuter := sk36LogOuterCertificate, logK := sk36LogKCertificate, logChi := chi52LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717420543/68716281856) } }, logDArg := sk36LogDArgCertificate }

private noncomputable def leaf452InnerLog : WideLogData :=
  innerPair197Data

set_option maxRecDepth 1000000 in
private theorem leaf452LocalValidity :
    LeafFacts leaf452Box leaf452Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf452Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34358140928) }) = true
      norm_num [leaf452Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf452CertificateValid :
    WideCertificateValid leaf452Box leaf452Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk36ValidityFacts chi52ValidityFacts
    leaf452LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf452CoverageChecked :
    coverageCheck (innerAD leaf452Box) leaf452InnerLog = true := by
  rfl'

private theorem leaf452InnerLogValid :
    leaf452InnerLog.Valid 8 (innerAD leaf452Box) :=
  wideLogDataValid_of_cachedCheck endpoint59PositiveFacts
    endpoint60PositiveFacts.valid leaf452CoverageChecked

private noncomputable def leaf452InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629359/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf452InputLogOnePlusV_eq :
    leaf452InputLogOnePlusV = outerEnclosure 24
      (leaf452Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf452RoundedFacts : LeafRoundedFacts 8
    leaf452Certificate.logOnePlusV leaf452InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf452InputLogOnePlusV_eq }

private noncomputable def leaf452Inputs : Inputs :=
  inputsOfCaches globalInput sk36RoundedInputs
    chi52InputQChi innerPair197Input
    leaf452InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf452LowerChecked :
    lowerCheck 24 leaf452Box leaf452Inputs = true := by
  rfl'

private theorem leaf452CoversExact : CoversExact 8
    leaf452Box leaf452Certificate leaf452InnerLog leaf452Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk36RoundedFacts chi52RoundedFacts
    innerPair197RoundedFacts leaf452RoundedFacts (by rfl)

private theorem leaf452FlatSound : Sound leaf452Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf452CertificateValid
    leaf452InnerLogValid leaf452CoversExact leaf452LowerChecked

private noncomputable def leaf453Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/16), kHi := (13/8), chiLo := (15/32), chiHi := (1/2) }

private noncomputable def leaf453Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554515/33554432) }, vSqrt := { lower := (16383/16384), upper := (11453093205/11452678144) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (58096083/33554432) }, upper := { exponent := 0, mantissa := (29/16) } }, logOuter := sk36LogOuterCertificate, logK := sk36LogKCertificate, logChi := chi53LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (22905771349/22905356288) } }, logDArg := sk36LogDArgCertificate }

private noncomputable def leaf453InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf453LocalValidity :
    LeafFacts leaf453Box leaf453Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf453Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (11453093205/11452678144) }) = true
      norm_num [leaf453Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf453CertificateValid :
    WideCertificateValid leaf453Box leaf453Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk36ValidityFacts chi53ValidityFacts
    leaf453LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf453CoverageChecked :
    coverageCheck (innerAD leaf453Box) leaf453InnerLog = true := by
  rfl'

private theorem leaf453InnerLogValid :
    leaf453InnerLog.Valid 8 (innerAD leaf453Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf453CoverageChecked

private noncomputable def leaf453InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629385/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf453InputLogOnePlusV_eq :
    leaf453InputLogOnePlusV = outerEnclosure 24
      (leaf453Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf453RoundedFacts : LeafRoundedFacts 8
    leaf453Certificate.logOnePlusV leaf453InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf453InputLogOnePlusV_eq }

private noncomputable def leaf453Inputs : Inputs :=
  inputsOfCaches globalInput sk36RoundedInputs
    chi53InputQChi innerPair66Input
    leaf453InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf453LowerChecked :
    lowerCheck 24 leaf453Box leaf453Inputs = true := by
  rfl'

private theorem leaf453CoversExact : CoversExact 8
    leaf453Box leaf453Certificate leaf453InnerLog leaf453Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk36RoundedFacts chi53RoundedFacts
    innerPair66RoundedFacts leaf453RoundedFacts (by rfl)

private theorem leaf453FlatSound : Sound leaf453Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf453CertificateValid
    leaf453InnerLogValid leaf453CoversExact leaf453LowerChecked

private noncomputable def leaf454Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (27/16), chiLo := (3/8), chiHi := (25/64) }

private noncomputable def leaf454Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108967/67108864) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34358355968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (107967963/67108864) }, upper := { exponent := 0, mantissa := (1699/1024) } }, logOuter := sk33LogOuterCertificate, logK := sk33LogKCertificate, logChi := chi62LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717635583/68716711936) } }, logDArg := sk33LogDArgCertificate }

private noncomputable def leaf454InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf454LocalValidity :
    LeafFacts leaf454Box leaf454Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf454Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34358355968) }) = true
      norm_num [leaf454Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf454CertificateValid :
    WideCertificateValid leaf454Box leaf454Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk33ValidityFacts chi62ValidityFacts
    leaf454LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf454CoverageChecked :
    coverageCheck (innerAD leaf454Box) leaf454InnerLog = true := by
  rfl'

private theorem leaf454InnerLogValid :
    leaf454InnerLog.Valid 8 (innerAD leaf454Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf454CoverageChecked

private noncomputable def leaf454InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814653/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf454InputLogOnePlusV_eq :
    leaf454InputLogOnePlusV = outerEnclosure 24
      (leaf454Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf454RoundedFacts : LeafRoundedFacts 8
    leaf454Certificate.logOnePlusV leaf454InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf454InputLogOnePlusV_eq }

private noncomputable def leaf454Inputs : Inputs :=
  inputsOfCaches globalInput sk33RoundedInputs
    chi62InputQChi innerPair51Input
    leaf454InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf454LowerChecked :
    lowerCheck 24 leaf454Box leaf454Inputs = true := by
  rfl'

private theorem leaf454CoversExact : CoversExact 8
    leaf454Box leaf454Certificate leaf454InnerLog leaf454Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk33RoundedFacts chi62RoundedFacts
    innerPair51RoundedFacts leaf454RoundedFacts (by rfl)

private theorem leaf454FlatSound : Sound leaf454Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf454CertificateValid
    leaf454InnerLogValid leaf454CoversExact leaf454LowerChecked

private noncomputable def leaf455Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (27/16), chiLo := (25/64), chiHi := (13/32) }

private noncomputable def leaf455Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108969/67108864) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34358300672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (109671793/67108864) }, upper := { exponent := 0, mantissa := (863/512) } }, logOuter := sk33LogOuterCertificate, logK := sk33LogKCertificate, logChi := chi63LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717580287/68716601344) } }, logDArg := sk33LogDArgCertificate }

private noncomputable def leaf455InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf455LocalValidity :
    LeafFacts leaf455Box leaf455Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf455Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34358300672) }) = true
      norm_num [leaf455Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf455CertificateValid :
    WideCertificateValid leaf455Box leaf455Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk33ValidityFacts chi63ValidityFacts
    leaf455LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf455CoverageChecked :
    coverageCheck (innerAD leaf455Box) leaf455InnerLog = true := by
  rfl'

private theorem leaf455InnerLogValid :
    leaf455InnerLog.Valid 8 (innerAD leaf455Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf455CoverageChecked

private noncomputable def leaf455InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (1453665/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf455InputLogOnePlusV_eq :
    leaf455InputLogOnePlusV = outerEnclosure 24
      (leaf455Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf455RoundedFacts : LeafRoundedFacts 8
    leaf455Certificate.logOnePlusV leaf455InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf455InputLogOnePlusV_eq }

private noncomputable def leaf455Inputs : Inputs :=
  inputsOfCaches globalInput sk33RoundedInputs
    chi63InputQChi innerPair56Input
    leaf455InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf455LowerChecked :
    lowerCheck 24 leaf455Box leaf455Inputs = true := by
  rfl'

private theorem leaf455CoversExact : CoversExact 8
    leaf455Box leaf455Certificate leaf455InnerLog leaf455Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk33RoundedFacts chi63RoundedFacts
    innerPair56RoundedFacts leaf455RoundedFacts (by rfl)

private theorem leaf455FlatSound : Sound leaf455Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf455CertificateValid
    leaf455InnerLogValid leaf455CoversExact leaf455LowerChecked

private noncomputable def leaf456Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (3/8), chiHi := (25/64) }

private noncomputable def leaf456Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108969/67108864) }, vSqrt := { lower := (16383/16384), upper := (11453093205/11452768256) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (109540729/67108864) }, upper := { exponent := 0, mantissa := (431/256) } }, logOuter := sk34LogOuterCertificate, logK := sk34LogKCertificate, logChi := chi62LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (22905861461/22905536512) } }, logDArg := sk34LogDArgCertificate }

private noncomputable def leaf456InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf456LocalValidity :
    LeafFacts leaf456Box leaf456Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf456Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (11453093205/11452768256) }) = true
      norm_num [leaf456Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf456CertificateValid :
    WideCertificateValid leaf456Box leaf456Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk34ValidityFacts chi62ValidityFacts
    leaf456LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf456CoverageChecked :
    coverageCheck (innerAD leaf456Box) leaf456InnerLog = true := by
  rfl'

private theorem leaf456InnerLogValid :
    leaf456InnerLog.Valid 8 (innerAD leaf456Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf456CoverageChecked

private noncomputable def leaf456InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629319/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf456InputLogOnePlusV_eq :
    leaf456InputLogOnePlusV = outerEnclosure 24
      (leaf456Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf456RoundedFacts : LeafRoundedFacts 8
    leaf456Certificate.logOnePlusV leaf456InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf456InputLogOnePlusV_eq }

private noncomputable def leaf456Inputs : Inputs :=
  inputsOfCaches globalInput sk34RoundedInputs
    chi62InputQChi innerPair56Input
    leaf456InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf456LowerChecked :
    lowerCheck 24 leaf456Box leaf456Inputs = true := by
  rfl'

private theorem leaf456CoversExact : CoversExact 8
    leaf456Box leaf456Certificate leaf456InnerLog leaf456Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk34RoundedFacts chi62RoundedFacts
    innerPair56RoundedFacts leaf456RoundedFacts (by rfl)

private theorem leaf456FlatSound : Sound leaf456Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf456CertificateValid
    leaf456InnerLogValid leaf456CoversExact leaf456LowerChecked

private noncomputable def leaf457Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (25/64), chiHi := (13/32) }

private noncomputable def leaf457Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108971/67108864) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34358247424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (111310091/67108864) }, upper := { exponent := 0, mantissa := (219/128) } }, logOuter := sk34LogOuterCertificate, logK := sk34LogKCertificate, logChi := chi63LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717527039/68716494848) } }, logDArg := sk34LogDArgCertificate }

private noncomputable def leaf457InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf457LocalValidity :
    LeafFacts leaf457Box leaf457Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf457Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34358247424) }) = true
      norm_num [leaf457Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf457CertificateValid :
    WideCertificateValid leaf457Box leaf457Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk34ValidityFacts chi63ValidityFacts
    leaf457LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf457CoverageChecked :
    coverageCheck (innerAD leaf457Box) leaf457InnerLog = true := by
  rfl'

private theorem leaf457InnerLogValid :
    leaf457InnerLog.Valid 8 (innerAD leaf457Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf457CoverageChecked

private noncomputable def leaf457InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629333/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf457InputLogOnePlusV_eq :
    leaf457InputLogOnePlusV = outerEnclosure 24
      (leaf457Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf457RoundedFacts : LeafRoundedFacts 8
    leaf457Certificate.logOnePlusV leaf457InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf457InputLogOnePlusV_eq }

private noncomputable def leaf457Inputs : Inputs :=
  inputsOfCaches globalInput sk34RoundedInputs
    chi63InputQChi innerPair57Input
    leaf457InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf457LowerChecked :
    lowerCheck 24 leaf457Box leaf457Inputs = true := by
  rfl'

private theorem leaf457CoversExact : CoversExact 8
    leaf457Box leaf457Certificate leaf457InnerLog leaf457Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk34RoundedFacts chi63RoundedFacts
    innerPair57RoundedFacts leaf457RoundedFacts (by rfl)

private theorem leaf457FlatSound : Sound leaf457Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf457CertificateValid
    leaf457InnerLogValid leaf457CoversExact leaf457LowerChecked

private noncomputable def leaf458Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (27/16), chiLo := (13/32), chiHi := (27/64) }

private noncomputable def leaf458Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108971/67108864) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34358245376) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (111375623/67108864) }, upper := { exponent := 0, mantissa := (1753/1024) } }, logOuter := sk33LogOuterCertificate, logK := sk33LogKCertificate, logChi := chi64LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717524991/68716490752) } }, logDArg := sk33LogDArgCertificate }

private noncomputable def leaf458InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf458LocalValidity :
    LeafFacts leaf458Box leaf458Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf458Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34358245376) }) = true
      norm_num [leaf458Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf458CertificateValid :
    WideCertificateValid leaf458Box leaf458Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk33ValidityFacts chi64ValidityFacts
    leaf458LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf458CoverageChecked :
    coverageCheck (innerAD leaf458Box) leaf458InnerLog = true := by
  rfl'

private theorem leaf458InnerLogValid :
    leaf458InnerLog.Valid 8 (innerAD leaf458Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf458CoverageChecked

private noncomputable def leaf458InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629333/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf458InputLogOnePlusV_eq :
    leaf458InputLogOnePlusV = outerEnclosure 24
      (leaf458Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf458RoundedFacts : LeafRoundedFacts 8
    leaf458Certificate.logOnePlusV leaf458InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf458InputLogOnePlusV_eq }

private noncomputable def leaf458Inputs : Inputs :=
  inputsOfCaches globalInput sk33RoundedInputs
    chi64InputQChi innerPair57Input
    leaf458InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf458LowerChecked :
    lowerCheck 24 leaf458Box leaf458Inputs = true := by
  rfl'

private theorem leaf458CoversExact : CoversExact 8
    leaf458Box leaf458Certificate leaf458InnerLog leaf458Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk33RoundedFacts chi64RoundedFacts
    innerPair57RoundedFacts leaf458RoundedFacts (by rfl)

private theorem leaf458FlatSound : Sound leaf458Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf458CertificateValid
    leaf458InnerLogValid leaf458CoversExact leaf458LowerChecked

private noncomputable def leaf459Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (27/16), chiLo := (27/64), chiHi := (7/16) }

private noncomputable def leaf459Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108973/67108864) }, vSqrt := { lower := (16383/16384), upper := (6871855923/6871638016) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (113079453/67108864) }, upper := { exponent := 0, mantissa := (445/256) } }, logOuter := sk33LogOuterCertificate, logK := sk33LogKCertificate, logChi := chi65LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (13743493939/13743276032) } }, logDArg := sk33LogDArgCertificate }

private noncomputable def leaf459InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf459LocalValidity :
    LeafFacts leaf459Box leaf459Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf459Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (6871855923/6871638016) }) = true
      norm_num [leaf459Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf459CertificateValid :
    WideCertificateValid leaf459Box leaf459Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk33ValidityFacts chi65ValidityFacts
    leaf459LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf459CoverageChecked :
    coverageCheck (innerAD leaf459Box) leaf459InnerLog = true := by
  rfl'

private theorem leaf459InnerLogValid :
    leaf459InnerLog.Valid 8 (innerAD leaf459Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf459CoverageChecked

private noncomputable def leaf459InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629347/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf459InputLogOnePlusV_eq :
    leaf459InputLogOnePlusV = outerEnclosure 24
      (leaf459Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf459RoundedFacts : LeafRoundedFacts 8
    leaf459Certificate.logOnePlusV leaf459InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf459InputLogOnePlusV_eq }

private noncomputable def leaf459Inputs : Inputs :=
  inputsOfCaches globalInput sk33RoundedInputs
    chi65InputQChi innerPair57Input
    leaf459InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf459LowerChecked :
    lowerCheck 24 leaf459Box leaf459Inputs = true := by
  rfl'

private theorem leaf459CoversExact : CoversExact 8
    leaf459Box leaf459Certificate leaf459InnerLog leaf459Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk33RoundedFacts chi65RoundedFacts
    innerPair57RoundedFacts leaf459RoundedFacts (by rfl)

private theorem leaf459FlatSound : Sound leaf459Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf459CertificateValid
    leaf459InnerLogValid leaf459CoversExact leaf459LowerChecked

private noncomputable def leaf460Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (13/32), chiHi := (27/64) }

private noncomputable def leaf460Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108973/67108864) }, vSqrt := { lower := (16383/16384), upper := (6871855923/6871638016) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (113079453/67108864) }, upper := { exponent := 0, mantissa := (445/256) } }, logOuter := sk34LogOuterCertificate, logK := sk34LogKCertificate, logChi := chi64LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (13743493939/13743276032) } }, logDArg := sk34LogDArgCertificate }

private noncomputable def leaf460InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf460LocalValidity :
    LeafFacts leaf460Box leaf460Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf460Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (6871855923/6871638016) }) = true
      norm_num [leaf460Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf460CertificateValid :
    WideCertificateValid leaf460Box leaf460Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk34ValidityFacts chi64ValidityFacts
    leaf460LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf460CoverageChecked :
    coverageCheck (innerAD leaf460Box) leaf460InnerLog = true := by
  rfl'

private theorem leaf460InnerLogValid :
    leaf460InnerLog.Valid 8 (innerAD leaf460Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf460CoverageChecked

private noncomputable def leaf460InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629347/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf460InputLogOnePlusV_eq :
    leaf460InputLogOnePlusV = outerEnclosure 24
      (leaf460Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf460RoundedFacts : LeafRoundedFacts 8
    leaf460Certificate.logOnePlusV leaf460InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf460InputLogOnePlusV_eq }

private noncomputable def leaf460Inputs : Inputs :=
  inputsOfCaches globalInput sk34RoundedInputs
    chi64InputQChi innerPair57Input
    leaf460InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf460LowerChecked :
    lowerCheck 24 leaf460Box leaf460Inputs = true := by
  rfl'

private theorem leaf460CoversExact : CoversExact 8
    leaf460Box leaf460Certificate leaf460InnerLog leaf460Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk34RoundedFacts chi64RoundedFacts
    innerPair57RoundedFacts leaf460RoundedFacts (by rfl)

private theorem leaf460FlatSound : Sound leaf460Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf460CertificateValid
    leaf460InnerLogValid leaf460CoversExact leaf460LowerChecked

private noncomputable def leaf461Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (27/64), chiHi := (7/16) }

private noncomputable def leaf461Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108975/67108864) }, vSqrt := { lower := (16383/16384), upper := (3817697735/3817570304) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (114848815/67108864) }, upper := { exponent := 0, mantissa := (113/64) } }, logOuter := sk34LogOuterCertificate, logK := sk34LogKCertificate, logChi := chi65LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (7635268039/7635140608) } }, logDArg := sk34LogDArgCertificate }

private noncomputable def leaf461InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf461LocalValidity :
    LeafFacts leaf461Box leaf461Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf461Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (3817697735/3817570304) }) = true
      norm_num [leaf461Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf461CertificateValid :
    WideCertificateValid leaf461Box leaf461Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk34ValidityFacts chi65ValidityFacts
    leaf461LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf461CoverageChecked :
    coverageCheck (innerAD leaf461Box) leaf461InnerLog = true := by
  rfl'

private theorem leaf461InnerLogValid :
    leaf461InnerLog.Valid 8 (innerAD leaf461Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf461CoverageChecked

private noncomputable def leaf461InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629361/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf461InputLogOnePlusV_eq :
    leaf461InputLogOnePlusV = outerEnclosure 24
      (leaf461Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf461RoundedFacts : LeafRoundedFacts 8
    leaf461Certificate.logOnePlusV leaf461InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf461InputLogOnePlusV_eq }

private noncomputable def leaf461Inputs : Inputs :=
  inputsOfCaches globalInput sk34RoundedInputs
    chi65InputQChi innerPair66Input
    leaf461InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf461LowerChecked :
    lowerCheck 24 leaf461Box leaf461Inputs = true := by
  rfl'

private theorem leaf461CoversExact : CoversExact 8
    leaf461Box leaf461Certificate leaf461InnerLog leaf461Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk34RoundedFacts chi65RoundedFacts
    innerPair66RoundedFacts leaf461RoundedFacts (by rfl)

private theorem leaf461FlatSound : Sound leaf461Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf461CertificateValid
    leaf461InnerLogValid leaf461CoversExact leaf461LowerChecked

private noncomputable def leaf462Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (27/16), chiLo := (7/16), chiHi := (29/64) }

private noncomputable def leaf462Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108975/67108864) }, vSqrt := { lower := (16383/16384), upper := (2021134095/2021066752) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (114783283/67108864) }, upper := { exponent := 0, mantissa := (1807/1024) } }, logOuter := sk33LogOuterCertificate, logK := sk33LogKCertificate, logChi := chi66LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (4042200847/4042133504) } }, logDArg := sk33LogDArgCertificate }

private noncomputable def leaf462InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf462LocalValidity :
    LeafFacts leaf462Box leaf462Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf462Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (2021134095/2021066752) }) = true
      norm_num [leaf462Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf462CertificateValid :
    WideCertificateValid leaf462Box leaf462Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk33ValidityFacts chi66ValidityFacts
    leaf462LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf462CoverageChecked :
    coverageCheck (innerAD leaf462Box) leaf462InnerLog = true := by
  rfl'

private theorem leaf462InnerLogValid :
    leaf462InnerLog.Valid 8 (innerAD leaf462Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf462CoverageChecked

private noncomputable def leaf462InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (726835/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf462InputLogOnePlusV_eq :
    leaf462InputLogOnePlusV = outerEnclosure 24
      (leaf462Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf462RoundedFacts : LeafRoundedFacts 8
    leaf462Certificate.logOnePlusV leaf462InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf462InputLogOnePlusV_eq }

private noncomputable def leaf462Inputs : Inputs :=
  inputsOfCaches globalInput sk33RoundedInputs
    chi66InputQChi innerPair66Input
    leaf462InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf462LowerChecked :
    lowerCheck 24 leaf462Box leaf462Inputs = true := by
  rfl'

private theorem leaf462CoversExact : CoversExact 8
    leaf462Box leaf462Certificate leaf462InnerLog leaf462Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk33RoundedFacts chi66RoundedFacts
    innerPair66RoundedFacts leaf462RoundedFacts (by rfl)

private theorem leaf462FlatSound : Sound leaf462Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf462CertificateValid
    leaf462InnerLogValid leaf462CoversExact leaf462LowerChecked

private noncomputable def leaf463Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (27/16), chiLo := (29/64), chiHi := (15/32) }

private noncomputable def leaf463Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108977/67108864) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34358079488) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (116487113/67108864) }, upper := { exponent := 0, mantissa := (917/512) } }, logOuter := sk33LogOuterCertificate, logK := sk33LogKCertificate, logChi := chi67LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717359103/68716158976) } }, logDArg := sk33LogDArgCertificate }

private noncomputable def leaf463InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf463LocalValidity :
    LeafFacts leaf463Box leaf463Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf463Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34358079488) }) = true
      norm_num [leaf463Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf463CertificateValid :
    WideCertificateValid leaf463Box leaf463Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk33ValidityFacts chi67ValidityFacts
    leaf463LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf463CoverageChecked :
    coverageCheck (innerAD leaf463Box) leaf463InnerLog = true := by
  rfl'

private theorem leaf463InnerLogValid :
    leaf463InnerLog.Valid 8 (innerAD leaf463Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf463CoverageChecked

private noncomputable def leaf463InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814687/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf463InputLogOnePlusV_eq :
    leaf463InputLogOnePlusV = outerEnclosure 24
      (leaf463Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf463RoundedFacts : LeafRoundedFacts 8
    leaf463Certificate.logOnePlusV leaf463InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf463InputLogOnePlusV_eq }

private noncomputable def leaf463Inputs : Inputs :=
  inputsOfCaches globalInput sk33RoundedInputs
    chi67InputQChi innerPair66Input
    leaf463InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf463LowerChecked :
    lowerCheck 24 leaf463Box leaf463Inputs = true := by
  rfl'

private theorem leaf463CoversExact : CoversExact 8
    leaf463Box leaf463Certificate leaf463InnerLog leaf463Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk33RoundedFacts chi67RoundedFacts
    innerPair66RoundedFacts leaf463RoundedFacts (by rfl)

private theorem leaf463FlatSound : Sound leaf463Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf463CertificateValid
    leaf463InnerLogValid leaf463CoversExact leaf463LowerChecked

private noncomputable def leaf464Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (7/16), chiHi := (29/64) }

private noncomputable def leaf464Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108977/67108864) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34358075392) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (116618177/67108864) }, upper := { exponent := 0, mantissa := (459/256) } }, logOuter := sk34LogOuterCertificate, logK := sk34LogKCertificate, logChi := chi66LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717355007/68716150784) } }, logDArg := sk34LogDArgCertificate }

private noncomputable def leaf464InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf464LocalValidity :
    LeafFacts leaf464Box leaf464Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf464Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34358075392) }) = true
      norm_num [leaf464Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf464CertificateValid :
    WideCertificateValid leaf464Box leaf464Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk34ValidityFacts chi66ValidityFacts
    leaf464LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf464CoverageChecked :
    coverageCheck (innerAD leaf464Box) leaf464InnerLog = true := by
  rfl'

private theorem leaf464InnerLogValid :
    leaf464InnerLog.Valid 8 (innerAD leaf464Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf464CoverageChecked

private noncomputable def leaf464InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629375/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf464InputLogOnePlusV_eq :
    leaf464InputLogOnePlusV = outerEnclosure 24
      (leaf464Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf464RoundedFacts : LeafRoundedFacts 8
    leaf464Certificate.logOnePlusV leaf464InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf464InputLogOnePlusV_eq }

private noncomputable def leaf464Inputs : Inputs :=
  inputsOfCaches globalInput sk34RoundedInputs
    chi66InputQChi innerPair66Input
    leaf464InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf464LowerChecked :
    lowerCheck 24 leaf464Box leaf464Inputs = true := by
  rfl'

private theorem leaf464CoversExact : CoversExact 8
    leaf464Box leaf464Certificate leaf464InnerLog leaf464Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk34RoundedFacts chi66RoundedFacts
    innerPair66RoundedFacts leaf464RoundedFacts (by rfl)

private theorem leaf464FlatSound : Sound leaf464Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf464CertificateValid
    leaf464InnerLogValid leaf464CoversExact leaf464LowerChecked

private noncomputable def leaf465Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (29/64), chiHi := (15/32) }

private noncomputable def leaf465Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108979/67108864) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34358018048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (118387539/67108864) }, upper := { exponent := 0, mantissa := (233/128) } }, logOuter := sk34LogOuterCertificate, logK := sk34LogKCertificate, logChi := chi67LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717297663/68716036096) } }, logDArg := sk34LogDArgCertificate }

private noncomputable def leaf465InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf465LocalValidity :
    LeafFacts leaf465Box leaf465Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf465Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34358018048) }) = true
      norm_num [leaf465Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf465CertificateValid :
    WideCertificateValid leaf465Box leaf465Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk34ValidityFacts chi67ValidityFacts
    leaf465LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf465CoverageChecked :
    coverageCheck (innerAD leaf465Box) leaf465InnerLog = true := by
  rfl'

private theorem leaf465InnerLogValid :
    leaf465InnerLog.Valid 8 (innerAD leaf465Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf465CoverageChecked

private noncomputable def leaf465InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629389/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf465InputLogOnePlusV_eq :
    leaf465InputLogOnePlusV = outerEnclosure 24
      (leaf465Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf465RoundedFacts : LeafRoundedFacts 8
    leaf465Certificate.logOnePlusV leaf465InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf465InputLogOnePlusV_eq }

private noncomputable def leaf465Inputs : Inputs :=
  inputsOfCaches globalInput sk34RoundedInputs
    chi67InputQChi innerPair72Input
    leaf465InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf465LowerChecked :
    lowerCheck 24 leaf465Box leaf465Inputs = true := by
  rfl'

private theorem leaf465CoversExact : CoversExact 8
    leaf465Box leaf465Certificate leaf465InnerLog leaf465Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk34RoundedFacts chi67RoundedFacts
    innerPair72RoundedFacts leaf465RoundedFacts (by rfl)

private theorem leaf465FlatSound : Sound leaf465Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf465CertificateValid
    leaf465InnerLogValid leaf465CoversExact leaf465LowerChecked

private noncomputable def leaf466Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (27/16), chiLo := (15/32), chiHi := (1/2) }

private noncomputable def leaf466Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554517/33554432) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34357968896) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (59079061/33554432) }, upper := { exponent := 0, mantissa := (59/32) } }, logOuter := sk33LogOuterCertificate, logK := sk33LogKCertificate, logChi := chi53LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717248511/68715937792) } }, logDArg := sk33LogDArgCertificate }

private noncomputable def leaf466InnerLog : WideLogData :=
  innerPair74Data

set_option maxRecDepth 1000000 in
private theorem leaf466LocalValidity :
    LeafFacts leaf466Box leaf466Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf466Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34357968896) }) = true
      norm_num [leaf466Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf466CertificateValid :
    WideCertificateValid leaf466Box leaf466Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk33ValidityFacts chi53ValidityFacts
    leaf466LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf466CoverageChecked :
    coverageCheck (innerAD leaf466Box) leaf466InnerLog = true := by
  rfl'

private theorem leaf466InnerLogValid :
    leaf466InnerLog.Valid 8 (innerAD leaf466Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint61PositiveFacts.valid leaf466CoverageChecked

private noncomputable def leaf466InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629401/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf466InputLogOnePlusV_eq :
    leaf466InputLogOnePlusV = outerEnclosure 24
      (leaf466Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf466RoundedFacts : LeafRoundedFacts 8
    leaf466Certificate.logOnePlusV leaf466InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf466InputLogOnePlusV_eq }

private noncomputable def leaf466Inputs : Inputs :=
  inputsOfCaches globalInput sk33RoundedInputs
    chi53InputQChi innerPair74Input
    leaf466InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf466LowerChecked :
    lowerCheck 24 leaf466Box leaf466Inputs = true := by
  rfl'

private theorem leaf466CoversExact : CoversExact 8
    leaf466Box leaf466Certificate leaf466InnerLog leaf466Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk33RoundedFacts chi53RoundedFacts
    innerPair74RoundedFacts leaf466RoundedFacts (by rfl)

private theorem leaf466FlatSound : Sound leaf466Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf466CertificateValid
    leaf466InnerLogValid leaf466CoversExact leaf466LowerChecked

private noncomputable def leaf467Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (15/32), chiHi := (31/64) }

private noncomputable def leaf467Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108981/67108864) }, vSqrt := { lower := (16383/16384), upper := (673711365/673685504) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (120156901/67108864) }, upper := { exponent := 0, mantissa := (473/256) } }, logOuter := sk34LogOuterCertificate, logK := sk34LogKCertificate, logChi := chi68LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (1347396869/1347371008) } }, logDArg := sk34LogDArgCertificate }

private noncomputable def leaf467InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf467LocalValidity :
    LeafFacts leaf467Box leaf467Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf467Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (673711365/673685504) }) = true
      norm_num [leaf467Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf467CertificateValid :
    WideCertificateValid leaf467Box leaf467Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk34ValidityFacts chi68ValidityFacts
    leaf467LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf467CoverageChecked :
    coverageCheck (innerAD leaf467Box) leaf467InnerLog = true := by
  rfl'

private theorem leaf467InnerLogValid :
    leaf467InnerLog.Valid 8 (innerAD leaf467Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf467CoverageChecked

private noncomputable def leaf467InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629403/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf467InputLogOnePlusV_eq :
    leaf467InputLogOnePlusV = outerEnclosure 24
      (leaf467Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf467RoundedFacts : LeafRoundedFacts 8
    leaf467Certificate.logOnePlusV leaf467InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf467InputLogOnePlusV_eq }

private noncomputable def leaf467Inputs : Inputs :=
  inputsOfCaches globalInput sk34RoundedInputs
    chi68InputQChi innerPair72Input
    leaf467InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf467LowerChecked :
    lowerCheck 24 leaf467Box leaf467Inputs = true := by
  rfl'

private theorem leaf467CoversExact : CoversExact 8
    leaf467Box leaf467Certificate leaf467InnerLog leaf467Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk34RoundedFacts chi68RoundedFacts
    innerPair72RoundedFacts leaf467RoundedFacts (by rfl)

private theorem leaf467FlatSound : Sound leaf467Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf467CertificateValid
    leaf467InnerLogValid leaf467CoversExact leaf467LowerChecked

private noncomputable def leaf468Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (31/64), chiHi := (1/2) }

private noncomputable def leaf468Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108983/67108864) }, vSqrt := { lower := (16383/16384), upper := (6871855923/6871580672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (121926263/67108864) }, upper := { exponent := 0, mantissa := (15/8) } }, logOuter := sk34LogOuterCertificate, logK := sk34LogKCertificate, logChi := chi69LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (13743436595/13743161344) } }, logDArg := sk34LogDArgCertificate }

private noncomputable def leaf468InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf468LocalValidity :
    LeafFacts leaf468Box leaf468Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf468Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (6871855923/6871580672) }) = true
      norm_num [leaf468Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf468CertificateValid :
    WideCertificateValid leaf468Box leaf468Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk34ValidityFacts chi69ValidityFacts
    leaf468LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf468CoverageChecked :
    coverageCheck (innerAD leaf468Box) leaf468InnerLog = true := by
  rfl'

private theorem leaf468InnerLogValid :
    leaf468InnerLog.Valid 8 (innerAD leaf468Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf468CoverageChecked

private noncomputable def leaf468InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629417/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf468InputLogOnePlusV_eq :
    leaf468InputLogOnePlusV = outerEnclosure 24
      (leaf468Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf468RoundedFacts : LeafRoundedFacts 8
    leaf468Certificate.logOnePlusV leaf468InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf468InputLogOnePlusV_eq }

private noncomputable def leaf468Inputs : Inputs :=
  inputsOfCaches globalInput sk34RoundedInputs
    chi69InputQChi innerPair91Input
    leaf468InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf468LowerChecked :
    lowerCheck 24 leaf468Box leaf468Inputs = true := by
  rfl'

private theorem leaf468CoversExact : CoversExact 8
    leaf468Box leaf468Certificate leaf468InnerLog leaf468Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk34RoundedFacts chi69RoundedFacts
    innerPair91RoundedFacts leaf468RoundedFacts (by rfl)

private theorem leaf468FlatSound : Sound leaf468Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf468CertificateValid
    leaf468InnerLogValid leaf468CoversExact leaf468LowerChecked

private noncomputable def leaf469Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16), chiLo := (3/8), chiHi := (25/64) }

private noncomputable def leaf469Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108971/67108864) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34358253568) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (111113495/67108864) }, upper := { exponent := 0, mantissa := (1749/1024) } }, logOuter := sk39LogOuterCertificate, logK := sk39LogKCertificate, logChi := chi62LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717533183/68716507136) } }, logDArg := sk39LogDArgCertificate }

private noncomputable def leaf469InnerLog : WideLogData :=
  innerPair162Data

set_option maxRecDepth 1000000 in
private theorem leaf469LocalValidity :
    LeafFacts leaf469Box leaf469Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf469Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34358253568) }) = true
      norm_num [leaf469Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf469CertificateValid :
    WideCertificateValid leaf469Box leaf469Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk39ValidityFacts chi62ValidityFacts
    leaf469LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf469CoverageChecked :
    coverageCheck (innerAD leaf469Box) leaf469InnerLog = true := by
  rfl'

private theorem leaf469InnerLogValid :
    leaf469InnerLog.Valid 8 (innerAD leaf469Box) :=
  wideLogDataValid_of_cachedCheck endpoint45PositiveFacts
    endpoint62PositiveFacts.valid leaf469CoverageChecked

private noncomputable def leaf469InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629331/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf469InputLogOnePlusV_eq :
    leaf469InputLogOnePlusV = outerEnclosure 24
      (leaf469Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf469RoundedFacts : LeafRoundedFacts 8
    leaf469Certificate.logOnePlusV leaf469InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf469InputLogOnePlusV_eq }

private noncomputable def leaf469Inputs : Inputs :=
  inputsOfCaches globalInput sk39RoundedInputs
    chi62InputQChi innerPair162Input
    leaf469InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf469LowerChecked :
    lowerCheck 24 leaf469Box leaf469Inputs = true := by
  rfl'

private theorem leaf469CoversExact : CoversExact 8
    leaf469Box leaf469Certificate leaf469InnerLog leaf469Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk39RoundedFacts chi62RoundedFacts
    innerPair162RoundedFacts leaf469RoundedFacts (by rfl)

private theorem leaf469FlatSound : Sound leaf469Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf469CertificateValid
    leaf469InnerLogValid leaf469CoversExact leaf469LowerChecked

private noncomputable def leaf470Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16), chiLo := (25/64), chiHi := (13/32) }

private noncomputable def leaf470Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108973/67108864) }, vSqrt := { lower := (16383/16384), upper := (11453093205/11452731392) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (112948389/67108864) }, upper := { exponent := 0, mantissa := (889/512) } }, logOuter := sk39LogOuterCertificate, logK := sk39LogKCertificate, logChi := chi63LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (22905824597/22905462784) } }, logDArg := sk39LogDArgCertificate }

private noncomputable def leaf470InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf470LocalValidity :
    LeafFacts leaf470Box leaf470Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf470Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (11453093205/11452731392) }) = true
      norm_num [leaf470Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf470CertificateValid :
    WideCertificateValid leaf470Box leaf470Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk39ValidityFacts chi63ValidityFacts
    leaf470LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf470CoverageChecked :
    coverageCheck (innerAD leaf470Box) leaf470InnerLog = true := by
  rfl'

private theorem leaf470InnerLogValid :
    leaf470InnerLog.Valid 8 (innerAD leaf470Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf470CoverageChecked

private noncomputable def leaf470InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814673/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf470InputLogOnePlusV_eq :
    leaf470InputLogOnePlusV = outerEnclosure 24
      (leaf470Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf470RoundedFacts : LeafRoundedFacts 8
    leaf470Certificate.logOnePlusV leaf470InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf470InputLogOnePlusV_eq }

private noncomputable def leaf470Inputs : Inputs :=
  inputsOfCaches globalInput sk39RoundedInputs
    chi63InputQChi innerPair57Input
    leaf470InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf470LowerChecked :
    lowerCheck 24 leaf470Box leaf470Inputs = true := by
  rfl'

private theorem leaf470CoversExact : CoversExact 8
    leaf470Box leaf470Certificate leaf470InnerLog leaf470Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk39RoundedFacts chi63RoundedFacts
    innerPair57RoundedFacts leaf470RoundedFacts (by rfl)

private theorem leaf470FlatSound : Sound leaf470Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf470CertificateValid
    leaf470InnerLogValid leaf470CoversExact leaf470LowerChecked

private noncomputable def leaf471Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8), chiLo := (3/8), chiHi := (25/64) }

private noncomputable def leaf471Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108973/67108864) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34358202368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (112686261/67108864) }, upper := { exponent := 0, mantissa := (887/512) } }, logOuter := sk40LogOuterCertificate, logK := sk40LogKCertificate, logChi := chi62LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717481983/68716404736) } }, logDArg := sk40LogDArgCertificate }

private noncomputable def leaf471InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf471LocalValidity :
    LeafFacts leaf471Box leaf471Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf471Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34358202368) }) = true
      norm_num [leaf471Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf471CertificateValid :
    WideCertificateValid leaf471Box leaf471Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk40ValidityFacts chi62ValidityFacts
    leaf471LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf471CoverageChecked :
    coverageCheck (innerAD leaf471Box) leaf471InnerLog = true := by
  rfl'

private theorem leaf471InnerLogValid :
    leaf471InnerLog.Valid 8 (innerAD leaf471Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf471CoverageChecked

private noncomputable def leaf471InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (363417/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf471InputLogOnePlusV_eq :
    leaf471InputLogOnePlusV = outerEnclosure 24
      (leaf471Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf471RoundedFacts : LeafRoundedFacts 8
    leaf471Certificate.logOnePlusV leaf471InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf471InputLogOnePlusV_eq }

private noncomputable def leaf471Inputs : Inputs :=
  inputsOfCaches globalInput sk40RoundedInputs
    chi62InputQChi innerPair57Input
    leaf471InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf471LowerChecked :
    lowerCheck 24 leaf471Box leaf471Inputs = true := by
  rfl'

private theorem leaf471CoversExact : CoversExact 8
    leaf471Box leaf471Certificate leaf471InnerLog leaf471Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk40RoundedFacts chi62RoundedFacts
    innerPair57RoundedFacts leaf471RoundedFacts (by rfl)

private theorem leaf471FlatSound : Sound leaf471Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf471CertificateValid
    leaf471InnerLogValid leaf471CoversExact leaf471LowerChecked

private noncomputable def leaf472Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8), chiLo := (25/64), chiHi := (13/32) }

private noncomputable def leaf472Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108975/67108864) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34358140928) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (114586687/67108864) }, upper := { exponent := 0, mantissa := (451/256) } }, logOuter := sk40LogOuterCertificate, logK := sk40LogKCertificate, logChi := chi63LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717420543/68716281856) } }, logDArg := sk40LogDArgCertificate }

private noncomputable def leaf472InnerLog : WideLogData :=
  innerPair89Data

set_option maxRecDepth 1000000 in
private theorem leaf472LocalValidity :
    LeafFacts leaf472Box leaf472Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf472Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34358140928) }) = true
      norm_num [leaf472Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf472CertificateValid :
    WideCertificateValid leaf472Box leaf472Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk40ValidityFacts chi63ValidityFacts
    leaf472LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf472CoverageChecked :
    coverageCheck (innerAD leaf472Box) leaf472InnerLog = true := by
  rfl'

private theorem leaf472InnerLogValid :
    leaf472InnerLog.Valid 8 (innerAD leaf472Box) :=
  wideLogDataValid_of_cachedCheck endpoint20PositiveFacts
    endpoint63PositiveFacts.valid leaf472CoverageChecked

private noncomputable def leaf472InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629359/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf472InputLogOnePlusV_eq :
    leaf472InputLogOnePlusV = outerEnclosure 24
      (leaf472Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf472RoundedFacts : LeafRoundedFacts 8
    leaf472Certificate.logOnePlusV leaf472InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf472InputLogOnePlusV_eq }

private noncomputable def leaf472Inputs : Inputs :=
  inputsOfCaches globalInput sk40RoundedInputs
    chi63InputQChi innerPair89Input
    leaf472InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf472LowerChecked :
    lowerCheck 24 leaf472Box leaf472Inputs = true := by
  rfl'

private theorem leaf472CoversExact : CoversExact 8
    leaf472Box leaf472Certificate leaf472InnerLog leaf472Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk40RoundedFacts chi63RoundedFacts
    innerPair89RoundedFacts leaf472RoundedFacts (by rfl)

private theorem leaf472FlatSound : Sound leaf472Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf472CertificateValid
    leaf472InnerLogValid leaf472CoversExact leaf472LowerChecked

private noncomputable def leaf473Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16), chiLo := (13/32), chiHi := (27/64) }

private noncomputable def leaf473Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108975/67108864) }, vSqrt := { lower := (16383/16384), upper := (2021134095/2021066752) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (114783283/67108864) }, upper := { exponent := 0, mantissa := (1807/1024) } }, logOuter := sk39LogOuterCertificate, logK := sk39LogKCertificate, logChi := chi64LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (4042200847/4042133504) } }, logDArg := sk39LogDArgCertificate }

private noncomputable def leaf473InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf473LocalValidity :
    LeafFacts leaf473Box leaf473Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf473Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (2021134095/2021066752) }) = true
      norm_num [leaf473Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf473CertificateValid :
    WideCertificateValid leaf473Box leaf473Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk39ValidityFacts chi64ValidityFacts
    leaf473LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf473CoverageChecked :
    coverageCheck (innerAD leaf473Box) leaf473InnerLog = true := by
  rfl'

private theorem leaf473InnerLogValid :
    leaf473InnerLog.Valid 8 (innerAD leaf473Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf473CoverageChecked

private noncomputable def leaf473InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (726835/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf473InputLogOnePlusV_eq :
    leaf473InputLogOnePlusV = outerEnclosure 24
      (leaf473Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf473RoundedFacts : LeafRoundedFacts 8
    leaf473Certificate.logOnePlusV leaf473InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf473InputLogOnePlusV_eq }

private noncomputable def leaf473Inputs : Inputs :=
  inputsOfCaches globalInput sk39RoundedInputs
    chi64InputQChi innerPair66Input
    leaf473InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf473LowerChecked :
    lowerCheck 24 leaf473Box leaf473Inputs = true := by
  rfl'

private theorem leaf473CoversExact : CoversExact 8
    leaf473Box leaf473Certificate leaf473InnerLog leaf473Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk39RoundedFacts chi64RoundedFacts
    innerPair66RoundedFacts leaf473RoundedFacts (by rfl)

private theorem leaf473FlatSound : Sound leaf473Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf473CertificateValid
    leaf473InnerLogValid leaf473CoversExact leaf473LowerChecked

private noncomputable def leaf474Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16), chiLo := (27/64), chiHi := (7/16) }

private noncomputable def leaf474Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108977/67108864) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34358075392) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (116618177/67108864) }, upper := { exponent := 0, mantissa := (459/256) } }, logOuter := sk39LogOuterCertificate, logK := sk39LogKCertificate, logChi := chi65LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717355007/68716150784) } }, logDArg := sk39LogDArgCertificate }

private noncomputable def leaf474InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf474LocalValidity :
    LeafFacts leaf474Box leaf474Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf474Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34358075392) }) = true
      norm_num [leaf474Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf474CertificateValid :
    WideCertificateValid leaf474Box leaf474Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk39ValidityFacts chi65ValidityFacts
    leaf474LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf474CoverageChecked :
    coverageCheck (innerAD leaf474Box) leaf474InnerLog = true := by
  rfl'

private theorem leaf474InnerLogValid :
    leaf474InnerLog.Valid 8 (innerAD leaf474Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf474CoverageChecked

private noncomputable def leaf474InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629375/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf474InputLogOnePlusV_eq :
    leaf474InputLogOnePlusV = outerEnclosure 24
      (leaf474Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf474RoundedFacts : LeafRoundedFacts 8
    leaf474Certificate.logOnePlusV leaf474InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf474InputLogOnePlusV_eq }

private noncomputable def leaf474Inputs : Inputs :=
  inputsOfCaches globalInput sk39RoundedInputs
    chi65InputQChi innerPair66Input
    leaf474InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf474LowerChecked :
    lowerCheck 24 leaf474Box leaf474Inputs = true := by
  rfl'

private theorem leaf474CoversExact : CoversExact 8
    leaf474Box leaf474Certificate leaf474InnerLog leaf474Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk39RoundedFacts chi65RoundedFacts
    innerPair66RoundedFacts leaf474RoundedFacts (by rfl)

private theorem leaf474FlatSound : Sound leaf474Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf474CertificateValid
    leaf474InnerLogValid leaf474CoversExact leaf474LowerChecked

private noncomputable def leaf475Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8), chiLo := (13/32), chiHi := (27/64) }

private noncomputable def leaf475Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108977/67108864) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34358079488) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (116487113/67108864) }, upper := { exponent := 0, mantissa := (917/512) } }, logOuter := sk40LogOuterCertificate, logK := sk40LogKCertificate, logChi := chi64LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717359103/68716158976) } }, logDArg := sk40LogDArgCertificate }

private noncomputable def leaf475InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf475LocalValidity :
    LeafFacts leaf475Box leaf475Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf475Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34358079488) }) = true
      norm_num [leaf475Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf475CertificateValid :
    WideCertificateValid leaf475Box leaf475Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk40ValidityFacts chi64ValidityFacts
    leaf475LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf475CoverageChecked :
    coverageCheck (innerAD leaf475Box) leaf475InnerLog = true := by
  rfl'

private theorem leaf475InnerLogValid :
    leaf475InnerLog.Valid 8 (innerAD leaf475Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf475CoverageChecked

private noncomputable def leaf475InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814687/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf475InputLogOnePlusV_eq :
    leaf475InputLogOnePlusV = outerEnclosure 24
      (leaf475Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf475RoundedFacts : LeafRoundedFacts 8
    leaf475Certificate.logOnePlusV leaf475InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf475InputLogOnePlusV_eq }

private noncomputable def leaf475Inputs : Inputs :=
  inputsOfCaches globalInput sk40RoundedInputs
    chi64InputQChi innerPair66Input
    leaf475InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf475LowerChecked :
    lowerCheck 24 leaf475Box leaf475Inputs = true := by
  rfl'

private theorem leaf475CoversExact : CoversExact 8
    leaf475Box leaf475Certificate leaf475InnerLog leaf475Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk40RoundedFacts chi64RoundedFacts
    innerPair66RoundedFacts leaf475RoundedFacts (by rfl)

private theorem leaf475FlatSound : Sound leaf475Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf475CertificateValid
    leaf475InnerLogValid leaf475CoversExact leaf475LowerChecked

private noncomputable def leaf476Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8), chiLo := (27/64), chiHi := (7/16) }

private noncomputable def leaf476Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108979/67108864) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34358018048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (118387539/67108864) }, upper := { exponent := 0, mantissa := (233/128) } }, logOuter := sk40LogOuterCertificate, logK := sk40LogKCertificate, logChi := chi65LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717297663/68716036096) } }, logDArg := sk40LogDArgCertificate }

private noncomputable def leaf476InnerLog : WideLogData :=
  innerPair76Data

set_option maxRecDepth 1000000 in
private theorem leaf476LocalValidity :
    LeafFacts leaf476Box leaf476Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf476Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34358018048) }) = true
      norm_num [leaf476Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf476CertificateValid :
    WideCertificateValid leaf476Box leaf476Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk40ValidityFacts chi65ValidityFacts
    leaf476LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf476CoverageChecked :
    coverageCheck (innerAD leaf476Box) leaf476InnerLog = true := by
  rfl'

private theorem leaf476InnerLogValid :
    leaf476InnerLog.Valid 8 (innerAD leaf476Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint64PositiveFacts.valid leaf476CoverageChecked

private noncomputable def leaf476InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629389/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf476InputLogOnePlusV_eq :
    leaf476InputLogOnePlusV = outerEnclosure 24
      (leaf476Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf476RoundedFacts : LeafRoundedFacts 8
    leaf476Certificate.logOnePlusV leaf476InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf476InputLogOnePlusV_eq }

private noncomputable def leaf476Inputs : Inputs :=
  inputsOfCaches globalInput sk40RoundedInputs
    chi65InputQChi innerPair76Input
    leaf476InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf476LowerChecked :
    lowerCheck 24 leaf476Box leaf476Inputs = true := by
  rfl'

private theorem leaf476CoversExact : CoversExact 8
    leaf476Box leaf476Certificate leaf476InnerLog leaf476Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk40RoundedFacts chi65RoundedFacts
    innerPair76RoundedFacts leaf476RoundedFacts (by rfl)

private theorem leaf476FlatSound : Sound leaf476Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf476CertificateValid
    leaf476InnerLogValid leaf476CoversExact leaf476LowerChecked

private noncomputable def leaf477Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (3/8), chiHi := (25/64) }

private noncomputable def leaf477Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108975/67108864) }, vSqrt := { lower := (16383/16384), upper := (3817697735/3817572352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (114259027/67108864) }, upper := { exponent := 0, mantissa := (1799/1024) } }, logOuter := sk41LogOuterCertificate, logK := sk41LogKCertificate, logChi := chi62LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (7635270087/7635144704) } }, logDArg := sk41LogDArgCertificate }

private noncomputable def leaf477InnerLog : WideLogData :=
  innerPair217Data

set_option maxRecDepth 1000000 in
private theorem leaf477LocalValidity :
    LeafFacts leaf477Box leaf477Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf477Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (3817697735/3817572352) }) = true
      norm_num [leaf477Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf477CertificateValid :
    WideCertificateValid leaf477Box leaf477Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk41ValidityFacts chi62ValidityFacts
    leaf477LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf477CoverageChecked :
    coverageCheck (innerAD leaf477Box) leaf477InnerLog = true := by
  rfl'

private theorem leaf477InnerLogValid :
    leaf477InnerLog.Valid 8 (innerAD leaf477Box) :=
  wideLogDataValid_of_cachedCheck endpoint65PositiveFacts
    endpoint66PositiveFacts.valid leaf477CoverageChecked

private noncomputable def leaf477InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (2907339/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf477InputLogOnePlusV_eq :
    leaf477InputLogOnePlusV = outerEnclosure 24
      (leaf477Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf477RoundedFacts : LeafRoundedFacts 8
    leaf477Certificate.logOnePlusV leaf477InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf477InputLogOnePlusV_eq }

private noncomputable def leaf477Inputs : Inputs :=
  inputsOfCaches globalInput sk41RoundedInputs
    chi62InputQChi innerPair217Input
    leaf477InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf477LowerChecked :
    lowerCheck 24 leaf477Box leaf477Inputs = true := by
  rfl'

private theorem leaf477CoversExact : CoversExact 8
    leaf477Box leaf477Certificate leaf477InnerLog leaf477Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk41RoundedFacts chi62RoundedFacts
    innerPair217RoundedFacts leaf477RoundedFacts (by rfl)

private theorem leaf477FlatSound : Sound leaf477Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf477CertificateValid
    leaf477InnerLogValid leaf477CoversExact leaf477LowerChecked

private noncomputable def leaf478Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (25/64), chiHi := (13/32) }

private noncomputable def leaf478Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108977/67108864) }, vSqrt := { lower := (16383/16384), upper := (6871855923/6871617536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (116224985/67108864) }, upper := { exponent := 0, mantissa := (915/512) } }, logOuter := sk41LogOuterCertificate, logK := sk41LogKCertificate, logChi := chi63LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (13743473459/13743235072) } }, logDArg := sk41LogDArgCertificate }

private noncomputable def leaf478InnerLog : WideLogData :=
  innerPair205Data

set_option maxRecDepth 1000000 in
private theorem leaf478LocalValidity :
    LeafFacts leaf478Box leaf478Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf478Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (6871855923/6871617536) }) = true
      norm_num [leaf478Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf478CertificateValid :
    WideCertificateValid leaf478Box leaf478Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk41ValidityFacts chi63ValidityFacts
    leaf478LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf478CoverageChecked :
    coverageCheck (innerAD leaf478Box) leaf478InnerLog = true := by
  rfl'

private theorem leaf478InnerLogValid :
    leaf478InnerLog.Valid 8 (innerAD leaf478Box) :=
  wideLogDataValid_of_cachedCheck endpoint62PositiveFacts
    endpoint67PositiveFacts.valid leaf478CoverageChecked

private noncomputable def leaf478InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (2907343/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf478InputLogOnePlusV_eq :
    leaf478InputLogOnePlusV = outerEnclosure 24
      (leaf478Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf478RoundedFacts : LeafRoundedFacts 8
    leaf478Certificate.logOnePlusV leaf478InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf478InputLogOnePlusV_eq }

private noncomputable def leaf478Inputs : Inputs :=
  inputsOfCaches globalInput sk41RoundedInputs
    chi63InputQChi innerPair205Input
    leaf478InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf478LowerChecked :
    lowerCheck 24 leaf478Box leaf478Inputs = true := by
  rfl'

private theorem leaf478CoversExact : CoversExact 8
    leaf478Box leaf478Certificate leaf478InnerLog leaf478Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk41RoundedFacts chi63RoundedFacts
    innerPair205RoundedFacts leaf478RoundedFacts (by rfl)

private theorem leaf478FlatSound : Sound leaf478Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf478CertificateValid
    leaf478InnerLogValid leaf478CoversExact leaf478LowerChecked

private noncomputable def leaf479Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (63/32), chiLo := (3/8), chiHi := (25/64) }

private noncomputable def leaf479Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217903/134217728) }, vSqrt := { lower := (16383/16384), upper := (68718493695/68716251136) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (231696403/134217728) }, upper := { exponent := 0, mantissa := (3623/2048) } }, logOuter := sk47LogOuterCertificate, logK := sk47LogKCertificate, logChi := chi62LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (137434744831/137432502272) } }, logDArg := sk47LogDArgCertificate }

private noncomputable def leaf479InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf479LocalValidity :
    LeafFacts leaf479Box leaf479Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf479Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (68718493695/68716251136) }) = true
      norm_num [leaf479Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf479CertificateValid :
    WideCertificateValid leaf479Box leaf479Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk47ValidityFacts chi62ValidityFacts
    leaf479LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf479CoverageChecked :
    coverageCheck (innerAD leaf479Box) leaf479InnerLog = true := by
  rfl'

private theorem leaf479InnerLogValid :
    leaf479InnerLog.Valid 8 (innerAD leaf479Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf479CoverageChecked

private noncomputable def leaf479InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629355/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf479InputLogOnePlusV_eq :
    leaf479InputLogOnePlusV = outerEnclosure 24
      (leaf479Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf479RoundedFacts : LeafRoundedFacts 8
    leaf479Certificate.logOnePlusV leaf479InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf479InputLogOnePlusV_eq }

private noncomputable def leaf479Inputs : Inputs :=
  inputsOfCaches globalInput sk47RoundedInputs
    chi62InputQChi innerPair66Input
    leaf479InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf479LowerChecked :
    lowerCheck 24 leaf479Box leaf479Inputs = true := by
  rfl'

private theorem leaf479CoversExact : CoversExact 8
    leaf479Box leaf479Certificate leaf479InnerLog leaf479Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk47RoundedFacts chi62RoundedFacts
    innerPair66RoundedFacts leaf479RoundedFacts (by rfl)

private theorem leaf479FlatSound : Sound leaf479Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf479CertificateValid
    leaf479InnerLogValid leaf479CoversExact leaf479LowerChecked

private noncomputable def leaf480Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/32), kHi := (2), chiLo := (3/8), chiHi := (25/64) }

private noncomputable def leaf480Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217905/134217728) }, vSqrt := { lower := (65531/65536), upper := (4042264335/4042129408) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (233269169/134217728) }, upper := { exponent := 0, mantissa := (57/32) } }, logOuter := sk48LogOuterCertificate, logK := sk48LogKCertificate, logChi := chi62LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (8084393743/8084258816) } }, logDArg := sk48LogDArgCertificate }

private noncomputable def leaf480InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf480LocalValidity :
    LeafFacts leaf480Box leaf480Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf480Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (4042264335/4042129408) }) = true
      norm_num [leaf480Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf480CertificateValid :
    WideCertificateValid leaf480Box leaf480Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk48ValidityFacts chi62ValidityFacts
    leaf480LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf480CoverageChecked :
    coverageCheck (innerAD leaf480Box) leaf480InnerLog = true := by
  rfl'

private theorem leaf480InnerLogValid :
    leaf480InnerLog.Valid 8 (innerAD leaf480Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf480CoverageChecked

private noncomputable def leaf480InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629361/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf480InputLogOnePlusV_eq :
    leaf480InputLogOnePlusV = outerEnclosure 24
      (leaf480Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf480RoundedFacts : LeafRoundedFacts 8
    leaf480Certificate.logOnePlusV leaf480InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf480InputLogOnePlusV_eq }

private noncomputable def leaf480Inputs : Inputs :=
  inputsOfCaches globalInput sk48RoundedInputs
    chi62InputQChi innerPair66Input
    leaf480InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf480LowerChecked :
    lowerCheck 24 leaf480Box leaf480Inputs = true := by
  rfl'

private theorem leaf480CoversExact : CoversExact 8
    leaf480Box leaf480Certificate leaf480InnerLog leaf480Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk48RoundedFacts chi62RoundedFacts
    innerPair66RoundedFacts leaf480RoundedFacts (by rfl)

private theorem leaf480FlatSound : Sound leaf480Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf480CertificateValid
    leaf480InnerLogValid leaf480CoversExact leaf480LowerChecked

private noncomputable def leaf481Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (63/32), chiLo := (25/64), chiHi := (13/32) }

private noncomputable def leaf481Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217905/134217728) }, vSqrt := { lower := (16383/16384), upper := (68718493695/68716122112) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (235759385/134217728) }, upper := { exponent := 0, mantissa := (1843/1024) } }, logOuter := sk47LogOuterCertificate, logK := sk47LogKCertificate, logChi := chi63LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (137434615807/137432244224) } }, logDArg := sk47LogDArgCertificate }

private noncomputable def leaf481InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf481LocalValidity :
    LeafFacts leaf481Box leaf481Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf481Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (68718493695/68716122112) }) = true
      norm_num [leaf481Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf481CertificateValid :
    WideCertificateValid leaf481Box leaf481Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk47ValidityFacts chi63ValidityFacts
    leaf481LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf481CoverageChecked :
    coverageCheck (innerAD leaf481Box) leaf481InnerLog = true := by
  rfl'

private theorem leaf481InnerLogValid :
    leaf481InnerLog.Valid 8 (innerAD leaf481Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf481CoverageChecked

private noncomputable def leaf481InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814685/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf481InputLogOnePlusV_eq :
    leaf481InputLogOnePlusV = outerEnclosure 24
      (leaf481Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf481RoundedFacts : LeafRoundedFacts 8
    leaf481Certificate.logOnePlusV leaf481InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf481InputLogOnePlusV_eq }

private noncomputable def leaf481Inputs : Inputs :=
  inputsOfCaches globalInput sk47RoundedInputs
    chi63InputQChi innerPair71Input
    leaf481InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf481LowerChecked :
    lowerCheck 24 leaf481Box leaf481Inputs = true := by
  rfl'

private theorem leaf481CoversExact : CoversExact 8
    leaf481Box leaf481Certificate leaf481InnerLog leaf481Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk47RoundedFacts chi63RoundedFacts
    innerPair71RoundedFacts leaf481RoundedFacts (by rfl)

private theorem leaf481FlatSound : Sound leaf481Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf481CertificateValid
    leaf481InnerLogValid leaf481CoversExact leaf481LowerChecked

private noncomputable def leaf482Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/32), kHi := (2), chiLo := (25/64), chiHi := (13/32) }

private noncomputable def leaf482Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217907/134217728) }, vSqrt := { lower := (65531/65536), upper := (22906164565/22905356288) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (237397683/134217728) }, upper := { exponent := 0, mantissa := (29/16) } }, logOuter := sk48LogOuterCertificate, logK := sk48LogKCertificate, logChi := chi63LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (45811520853/45810712576) } }, logDArg := sk48LogDArgCertificate }

private noncomputable def leaf482InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf482LocalValidity :
    LeafFacts leaf482Box leaf482Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf482Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (22906164565/22905356288) }) = true
      norm_num [leaf482Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf482CertificateValid :
    WideCertificateValid leaf482Box leaf482Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk48ValidityFacts chi63ValidityFacts
    leaf482LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf482CoverageChecked :
    coverageCheck (innerAD leaf482Box) leaf482InnerLog = true := by
  rfl'

private theorem leaf482InnerLogValid :
    leaf482InnerLog.Valid 8 (innerAD leaf482Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf482CoverageChecked

private noncomputable def leaf482InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629377/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf482InputLogOnePlusV_eq :
    leaf482InputLogOnePlusV = outerEnclosure 24
      (leaf482Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf482RoundedFacts : LeafRoundedFacts 8
    leaf482Certificate.logOnePlusV leaf482InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf482InputLogOnePlusV_eq }

private noncomputable def leaf482Inputs : Inputs :=
  inputsOfCaches globalInput sk48RoundedInputs
    chi63InputQChi innerPair71Input
    leaf482InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf482LowerChecked :
    lowerCheck 24 leaf482Box leaf482Inputs = true := by
  rfl'

private theorem leaf482CoversExact : CoversExact 8
    leaf482Box leaf482Certificate leaf482InnerLog leaf482Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk48RoundedFacts chi63RoundedFacts
    innerPair71RoundedFacts leaf482RoundedFacts (by rfl)

private theorem leaf482FlatSound : Sound leaf482Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf482CertificateValid
    leaf482InnerLogValid leaf482CoversExact leaf482LowerChecked

private noncomputable def leaf483Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (13/32), chiHi := (27/64) }

private noncomputable def leaf483Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108979/67108864) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34358024192) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (118190943/67108864) }, upper := { exponent := 0, mantissa := (1861/1024) } }, logOuter := sk41LogOuterCertificate, logK := sk41LogKCertificate, logChi := chi64LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717303807/68716048384) } }, logDArg := sk41LogDArgCertificate }

private noncomputable def leaf483InnerLog : WideLogData :=
  innerPair76Data

set_option maxRecDepth 1000000 in
private theorem leaf483LocalValidity :
    LeafFacts leaf483Box leaf483Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf483Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34358024192) }) = true
      norm_num [leaf483Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf483CertificateValid :
    WideCertificateValid leaf483Box leaf483Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk41ValidityFacts chi64ValidityFacts
    leaf483LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf483CoverageChecked :
    coverageCheck (innerAD leaf483Box) leaf483InnerLog = true := by
  rfl'

private theorem leaf483InnerLogValid :
    leaf483InnerLog.Valid 8 (innerAD leaf483Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint64PositiveFacts.valid leaf483CoverageChecked

private noncomputable def leaf483InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629387/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf483InputLogOnePlusV_eq :
    leaf483InputLogOnePlusV = outerEnclosure 24
      (leaf483Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf483RoundedFacts : LeafRoundedFacts 8
    leaf483Certificate.logOnePlusV leaf483InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf483InputLogOnePlusV_eq }

private noncomputable def leaf483Inputs : Inputs :=
  inputsOfCaches globalInput sk41RoundedInputs
    chi64InputQChi innerPair76Input
    leaf483InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf483LowerChecked :
    lowerCheck 24 leaf483Box leaf483Inputs = true := by
  rfl'

private theorem leaf483CoversExact : CoversExact 8
    leaf483Box leaf483Certificate leaf483InnerLog leaf483Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk41RoundedFacts chi64RoundedFacts
    innerPair76RoundedFacts leaf483RoundedFacts (by rfl)

private theorem leaf483FlatSound : Sound leaf483Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf483CertificateValid
    leaf483InnerLogValid leaf483CoversExact leaf483LowerChecked

private noncomputable def leaf484Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (27/64), chiHi := (7/16) }

private noncomputable def leaf484Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108981/67108864) }, vSqrt := { lower := (16383/16384), upper := (673711365/673685504) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (120156901/67108864) }, upper := { exponent := 0, mantissa := (473/256) } }, logOuter := sk41LogOuterCertificate, logK := sk41LogKCertificate, logChi := chi65LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (1347396869/1347371008) } }, logDArg := sk41LogDArgCertificate }

private noncomputable def leaf484InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf484LocalValidity :
    LeafFacts leaf484Box leaf484Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf484Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (673711365/673685504) }) = true
      norm_num [leaf484Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf484CertificateValid :
    WideCertificateValid leaf484Box leaf484Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk41ValidityFacts chi65ValidityFacts
    leaf484LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf484CoverageChecked :
    coverageCheck (innerAD leaf484Box) leaf484InnerLog = true := by
  rfl'

private theorem leaf484InnerLogValid :
    leaf484InnerLog.Valid 8 (innerAD leaf484Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf484CoverageChecked

private noncomputable def leaf484InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629403/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf484InputLogOnePlusV_eq :
    leaf484InputLogOnePlusV = outerEnclosure 24
      (leaf484Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf484RoundedFacts : LeafRoundedFacts 8
    leaf484Certificate.logOnePlusV leaf484InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf484InputLogOnePlusV_eq }

private noncomputable def leaf484Inputs : Inputs :=
  inputsOfCaches globalInput sk41RoundedInputs
    chi65InputQChi innerPair72Input
    leaf484InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf484LowerChecked :
    lowerCheck 24 leaf484Box leaf484Inputs = true := by
  rfl'

private theorem leaf484CoversExact : CoversExact 8
    leaf484Box leaf484Certificate leaf484InnerLog leaf484Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk41RoundedFacts chi65RoundedFacts
    innerPair72RoundedFacts leaf484RoundedFacts (by rfl)

private theorem leaf484FlatSound : Sound leaf484Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf484CertificateValid
    leaf484InnerLogValid leaf484CoversExact leaf484LowerChecked

private noncomputable def leaf485Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (13/32), chiHi := (27/64) }

private noncomputable def leaf485Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108981/67108864) }, vSqrt := { lower := (65531/65536), upper := (34359279615/34357968896) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (119894773/67108864) }, upper := { exponent := 0, mantissa := (59/32) } }, logOuter := sk42LogOuterCertificate, logK := sk42LogKCertificate, logChi := chi64LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68717248511/68715937792) } }, logDArg := sk42LogDArgCertificate }

private noncomputable def leaf485InnerLog : WideLogData :=
  innerPair225Data

set_option maxRecDepth 1000000 in
private theorem leaf485LocalValidity :
    LeafFacts leaf485Box leaf485Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf485Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34359279615/34357968896) }) = true
      norm_num [leaf485Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf485CertificateValid :
    WideCertificateValid leaf485Box leaf485Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk42ValidityFacts chi64ValidityFacts
    leaf485LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf485CoverageChecked :
    coverageCheck (innerAD leaf485Box) leaf485InnerLog = true := by
  rfl'

private theorem leaf485InnerLogValid :
    leaf485InnerLog.Valid 8 (innerAD leaf485Box) :=
  wideLogDataValid_of_cachedCheck endpoint68PositiveFacts
    endpoint61PositiveFacts.valid leaf485CoverageChecked

private noncomputable def leaf485InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629401/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf485InputLogOnePlusV_eq :
    leaf485InputLogOnePlusV = outerEnclosure 24
      (leaf485Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf485RoundedFacts : LeafRoundedFacts 8
    leaf485Certificate.logOnePlusV leaf485InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf485InputLogOnePlusV_eq }

private noncomputable def leaf485Inputs : Inputs :=
  inputsOfCaches globalInput sk42RoundedInputs
    chi64InputQChi innerPair225Input
    leaf485InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf485LowerChecked :
    lowerCheck 24 leaf485Box leaf485Inputs = true := by
  rfl'

private theorem leaf485CoversExact : CoversExact 8
    leaf485Box leaf485Certificate leaf485InnerLog leaf485Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk42RoundedFacts chi64RoundedFacts
    innerPair225RoundedFacts leaf485RoundedFacts (by rfl)

private theorem leaf485FlatSound : Sound leaf485Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf485CertificateValid
    leaf485InnerLogValid leaf485CoversExact leaf485LowerChecked

private noncomputable def leaf486Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (27/64), chiHi := (7/16) }

private noncomputable def leaf486Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108983/67108864) }, vSqrt := { lower := (65531/65536), upper := (6871855923/6871580672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (121926263/67108864) }, upper := { exponent := 0, mantissa := (15/8) } }, logOuter := sk42LogOuterCertificate, logK := sk42LogKCertificate, logChi := chi65LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (13743436595/13743161344) } }, logDArg := sk42LogDArgCertificate }

private noncomputable def leaf486InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf486LocalValidity :
    LeafFacts leaf486Box leaf486Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf486Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (6871855923/6871580672) }) = true
      norm_num [leaf486Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf486CertificateValid :
    WideCertificateValid leaf486Box leaf486Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk42ValidityFacts chi65ValidityFacts
    leaf486LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf486CoverageChecked :
    coverageCheck (innerAD leaf486Box) leaf486InnerLog = true := by
  rfl'

private theorem leaf486InnerLogValid :
    leaf486InnerLog.Valid 8 (innerAD leaf486Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf486CoverageChecked

private noncomputable def leaf486InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629417/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf486InputLogOnePlusV_eq :
    leaf486InputLogOnePlusV = outerEnclosure 24
      (leaf486Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf486RoundedFacts : LeafRoundedFacts 8
    leaf486Certificate.logOnePlusV leaf486InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf486InputLogOnePlusV_eq }

private noncomputable def leaf486Inputs : Inputs :=
  inputsOfCaches globalInput sk42RoundedInputs
    chi65InputQChi innerPair91Input
    leaf486InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf486LowerChecked :
    lowerCheck 24 leaf486Box leaf486Inputs = true := by
  rfl'

private theorem leaf486CoversExact : CoversExact 8
    leaf486Box leaf486Certificate leaf486InnerLog leaf486Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk42RoundedFacts chi65RoundedFacts
    innerPair91RoundedFacts leaf486RoundedFacts (by rfl)

private theorem leaf486FlatSound : Sound leaf486Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf486CertificateValid
    leaf486InnerLogValid leaf486CoversExact leaf486LowerChecked

private noncomputable def leaf487Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16), chiLo := (7/16), chiHi := (29/64) }

private noncomputable def leaf487Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108979/67108864) }, vSqrt := { lower := (16383/16384), upper := (2290618641/2290534400) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (118453071/67108864) }, upper := { exponent := 0, mantissa := (1865/1024) } }, logOuter := sk39LogOuterCertificate, logK := sk39LogKCertificate, logChi := chi66LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (4581153041/4581068800) } }, logDArg := sk39LogDArgCertificate }

private noncomputable def leaf487InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf487LocalValidity :
    LeafFacts leaf487Box leaf487Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf487Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (2290618641/2290534400) }) = true
      norm_num [leaf487Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf487CertificateValid :
    WideCertificateValid leaf487Box leaf487Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk39ValidityFacts chi66ValidityFacts
    leaf487LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf487CoverageChecked :
    coverageCheck (innerAD leaf487Box) leaf487InnerLog = true := by
  rfl'

private theorem leaf487InnerLogValid :
    leaf487InnerLog.Valid 8 (innerAD leaf487Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf487CoverageChecked

private noncomputable def leaf487InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629389/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf487InputLogOnePlusV_eq :
    leaf487InputLogOnePlusV = outerEnclosure 24
      (leaf487Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf487RoundedFacts : LeafRoundedFacts 8
    leaf487Certificate.logOnePlusV leaf487InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf487InputLogOnePlusV_eq }

private noncomputable def leaf487Inputs : Inputs :=
  inputsOfCaches globalInput sk39RoundedInputs
    chi66InputQChi innerPair72Input
    leaf487InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf487LowerChecked :
    lowerCheck 24 leaf487Box leaf487Inputs = true := by
  rfl'

private theorem leaf487CoversExact : CoversExact 8
    leaf487Box leaf487Certificate leaf487InnerLog leaf487Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk39RoundedFacts chi66RoundedFacts
    innerPair72RoundedFacts leaf487RoundedFacts (by rfl)

private theorem leaf487FlatSound : Sound leaf487Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf487CertificateValid
    leaf487InnerLogValid leaf487CoversExact leaf487LowerChecked

private noncomputable def leaf488Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16), chiLo := (29/64), chiHi := (15/32) }

private noncomputable def leaf488Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108981/67108864) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34357956608) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (120287965/67108864) }, upper := { exponent := 0, mantissa := (947/512) } }, logOuter := sk39LogOuterCertificate, logK := sk39LogKCertificate, logChi := chi67LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717236223/68715913216) } }, logDArg := sk39LogDArgCertificate }

private noncomputable def leaf488InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf488LocalValidity :
    LeafFacts leaf488Box leaf488Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf488Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34357956608) }) = true
      norm_num [leaf488Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf488CertificateValid :
    WideCertificateValid leaf488Box leaf488Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk39ValidityFacts chi67ValidityFacts
    leaf488LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf488CoverageChecked :
    coverageCheck (innerAD leaf488Box) leaf488InnerLog = true := by
  rfl'

private theorem leaf488InnerLogValid :
    leaf488InnerLog.Valid 8 (innerAD leaf488Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf488CoverageChecked

private noncomputable def leaf488InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (2907351/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf488InputLogOnePlusV_eq :
    leaf488InputLogOnePlusV = outerEnclosure 24
      (leaf488Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf488RoundedFacts : LeafRoundedFacts 8
    leaf488Certificate.logOnePlusV leaf488InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf488InputLogOnePlusV_eq }

private noncomputable def leaf488Inputs : Inputs :=
  inputsOfCaches globalInput sk39RoundedInputs
    chi67InputQChi innerPair72Input
    leaf488InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf488LowerChecked :
    lowerCheck 24 leaf488Box leaf488Inputs = true := by
  rfl'

private theorem leaf488CoversExact : CoversExact 8
    leaf488Box leaf488Certificate leaf488InnerLog leaf488Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk39RoundedFacts chi67RoundedFacts
    innerPair72RoundedFacts leaf488RoundedFacts (by rfl)

private theorem leaf488FlatSound : Sound leaf488Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf488CertificateValid
    leaf488InnerLogValid leaf488CoversExact leaf488LowerChecked

private noncomputable def leaf489Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8), chiLo := (7/16), chiHi := (29/64) }

private noncomputable def leaf489Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108981/67108864) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34357956608) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (120287965/67108864) }, upper := { exponent := 0, mantissa := (947/512) } }, logOuter := sk40LogOuterCertificate, logK := sk40LogKCertificate, logChi := chi66LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717236223/68715913216) } }, logDArg := sk40LogDArgCertificate }

private noncomputable def leaf489InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf489LocalValidity :
    LeafFacts leaf489Box leaf489Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf489Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34357956608) }) = true
      norm_num [leaf489Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf489CertificateValid :
    WideCertificateValid leaf489Box leaf489Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk40ValidityFacts chi66ValidityFacts
    leaf489LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf489CoverageChecked :
    coverageCheck (innerAD leaf489Box) leaf489InnerLog = true := by
  rfl'

private theorem leaf489InnerLogValid :
    leaf489InnerLog.Valid 8 (innerAD leaf489Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf489CoverageChecked

private noncomputable def leaf489InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (2907351/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf489InputLogOnePlusV_eq :
    leaf489InputLogOnePlusV = outerEnclosure 24
      (leaf489Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf489RoundedFacts : LeafRoundedFacts 8
    leaf489Certificate.logOnePlusV leaf489InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf489InputLogOnePlusV_eq }

private noncomputable def leaf489Inputs : Inputs :=
  inputsOfCaches globalInput sk40RoundedInputs
    chi66InputQChi innerPair72Input
    leaf489InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf489LowerChecked :
    lowerCheck 24 leaf489Box leaf489Inputs = true := by
  rfl'

private theorem leaf489CoversExact : CoversExact 8
    leaf489Box leaf489Certificate leaf489InnerLog leaf489Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk40RoundedFacts chi66RoundedFacts
    innerPair72RoundedFacts leaf489RoundedFacts (by rfl)

private theorem leaf489FlatSound : Sound leaf489Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf489CertificateValid
    leaf489InnerLogValid leaf489CoversExact leaf489LowerChecked

private noncomputable def leaf490Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8), chiLo := (29/64), chiHi := (15/32) }

private noncomputable def leaf490Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108983/67108864) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34357895168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (122188391/67108864) }, upper := { exponent := 0, mantissa := (481/256) } }, logOuter := sk40LogOuterCertificate, logK := sk40LogKCertificate, logChi := chi67LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717174783/68715790336) } }, logDArg := sk40LogDArgCertificate }

private noncomputable def leaf490InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf490LocalValidity :
    LeafFacts leaf490Box leaf490Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf490Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34357895168) }) = true
      norm_num [leaf490Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf490CertificateValid :
    WideCertificateValid leaf490Box leaf490Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk40ValidityFacts chi67ValidityFacts
    leaf490LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf490CoverageChecked :
    coverageCheck (innerAD leaf490Box) leaf490InnerLog = true := by
  rfl'

private theorem leaf490InnerLogValid :
    leaf490InnerLog.Valid 8 (innerAD leaf490Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf490CoverageChecked

private noncomputable def leaf490InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629419/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf490InputLogOnePlusV_eq :
    leaf490InputLogOnePlusV = outerEnclosure 24
      (leaf490Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf490RoundedFacts : LeafRoundedFacts 8
    leaf490Certificate.logOnePlusV leaf490InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf490InputLogOnePlusV_eq }

private noncomputable def leaf490Inputs : Inputs :=
  inputsOfCaches globalInput sk40RoundedInputs
    chi67InputQChi innerPair92Input
    leaf490InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf490LowerChecked :
    lowerCheck 24 leaf490Box leaf490Inputs = true := by
  rfl'

private theorem leaf490CoversExact : CoversExact 8
    leaf490Box leaf490Certificate leaf490InnerLog leaf490Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk40RoundedFacts chi67RoundedFacts
    innerPair92RoundedFacts leaf490RoundedFacts (by rfl)

private theorem leaf490FlatSound : Sound leaf490Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf490CertificateValid
    leaf490InnerLogValid leaf490CoversExact leaf490LowerChecked

private noncomputable def leaf491Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16), chiLo := (15/32), chiHi := (31/64) }

private noncomputable def leaf491Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108983/67108864) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34357897216) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (122122859/67108864) }, upper := { exponent := 0, mantissa := (1923/1024) } }, logOuter := sk39LogOuterCertificate, logK := sk39LogKCertificate, logChi := chi68LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717176831/68715794432) } }, logDArg := sk39LogDArgCertificate }

private noncomputable def leaf491InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf491LocalValidity :
    LeafFacts leaf491Box leaf491Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf491Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34357897216) }) = true
      norm_num [leaf491Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf491CertificateValid :
    WideCertificateValid leaf491Box leaf491Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk39ValidityFacts chi68ValidityFacts
    leaf491LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf491CoverageChecked :
    coverageCheck (innerAD leaf491Box) leaf491InnerLog = true := by
  rfl'

private theorem leaf491InnerLogValid :
    leaf491InnerLog.Valid 8 (innerAD leaf491Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf491CoverageChecked

private noncomputable def leaf491InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814709/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf491InputLogOnePlusV_eq :
    leaf491InputLogOnePlusV = outerEnclosure 24
      (leaf491Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf491RoundedFacts : LeafRoundedFacts 8
    leaf491Certificate.logOnePlusV leaf491InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf491InputLogOnePlusV_eq }

private noncomputable def leaf491Inputs : Inputs :=
  inputsOfCaches globalInput sk39RoundedInputs
    chi68InputQChi innerPair92Input
    leaf491InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf491LowerChecked :
    lowerCheck 24 leaf491Box leaf491Inputs = true := by
  rfl'

private theorem leaf491CoversExact : CoversExact 8
    leaf491Box leaf491Certificate leaf491InnerLog leaf491Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk39RoundedFacts chi68RoundedFacts
    innerPair92RoundedFacts leaf491RoundedFacts (by rfl)

private theorem leaf491FlatSound : Sound leaf491Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf491CertificateValid
    leaf491InnerLogValid leaf491CoversExact leaf491LowerChecked

private noncomputable def leaf492Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16), chiLo := (31/64), chiHi := (1/2) }

private noncomputable def leaf492Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108985/67108864) }, vSqrt := { lower := (16383/16384), upper := (3817697735/3817537536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (123957753/67108864) }, upper := { exponent := 0, mantissa := (61/32) } }, logOuter := sk39LogOuterCertificate, logK := sk39LogKCertificate, logChi := chi69LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (7635235271/7635075072) } }, logDArg := sk39LogDArgCertificate }

private noncomputable def leaf492InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf492LocalValidity :
    LeafFacts leaf492Box leaf492Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf492Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (3817697735/3817537536) }) = true
      norm_num [leaf492Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf492CertificateValid :
    WideCertificateValid leaf492Box leaf492Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk39ValidityFacts chi69ValidityFacts
    leaf492LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf492CoverageChecked :
    coverageCheck (innerAD leaf492Box) leaf492InnerLog = true := by
  rfl'

private theorem leaf492InnerLogValid :
    leaf492InnerLog.Valid 8 (innerAD leaf492Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf492CoverageChecked

private noncomputable def leaf492InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629433/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf492InputLogOnePlusV_eq :
    leaf492InputLogOnePlusV = outerEnclosure 24
      (leaf492Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf492RoundedFacts : LeafRoundedFacts 8
    leaf492Certificate.logOnePlusV leaf492InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf492InputLogOnePlusV_eq }

private noncomputable def leaf492Inputs : Inputs :=
  inputsOfCaches globalInput sk39RoundedInputs
    chi69InputQChi innerPair92Input
    leaf492InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf492LowerChecked :
    lowerCheck 24 leaf492Box leaf492Inputs = true := by
  rfl'

private theorem leaf492CoversExact : CoversExact 8
    leaf492Box leaf492Certificate leaf492InnerLog leaf492Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk39RoundedFacts chi69RoundedFacts
    innerPair92RoundedFacts leaf492RoundedFacts (by rfl)

private theorem leaf492FlatSound : Sound leaf492Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf492CertificateValid
    leaf492InnerLogValid leaf492CoversExact leaf492LowerChecked

private noncomputable def leaf493Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8), chiLo := (15/32), chiHi := (31/64) }

private noncomputable def leaf493Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108985/67108864) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34357833728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (124088817/67108864) }, upper := { exponent := 0, mantissa := (977/512) } }, logOuter := sk40LogOuterCertificate, logK := sk40LogKCertificate, logChi := chi68LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717113343/68715667456) } }, logDArg := sk40LogDArgCertificate }

private noncomputable def leaf493InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf493LocalValidity :
    LeafFacts leaf493Box leaf493Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf493Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34357833728) }) = true
      norm_num [leaf493Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf493CertificateValid :
    WideCertificateValid leaf493Box leaf493Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk40ValidityFacts chi68ValidityFacts
    leaf493LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf493CoverageChecked :
    coverageCheck (innerAD leaf493Box) leaf493InnerLog = true := by
  rfl'

private theorem leaf493InnerLogValid :
    leaf493InnerLog.Valid 8 (innerAD leaf493Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf493CoverageChecked

private noncomputable def leaf493InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814717/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf493InputLogOnePlusV_eq :
    leaf493InputLogOnePlusV = outerEnclosure 24
      (leaf493Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf493RoundedFacts : LeafRoundedFacts 8
    leaf493Certificate.logOnePlusV leaf493InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf493InputLogOnePlusV_eq }

private noncomputable def leaf493Inputs : Inputs :=
  inputsOfCaches globalInput sk40RoundedInputs
    chi68InputQChi innerPair92Input
    leaf493InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf493LowerChecked :
    lowerCheck 24 leaf493Box leaf493Inputs = true := by
  rfl'

private theorem leaf493CoversExact : CoversExact 8
    leaf493Box leaf493Certificate leaf493InnerLog leaf493Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk40RoundedFacts chi68RoundedFacts
    innerPair92RoundedFacts leaf493RoundedFacts (by rfl)

private theorem leaf493FlatSound : Sound leaf493Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf493CertificateValid
    leaf493InnerLogValid leaf493CoversExact leaf493LowerChecked

private noncomputable def leaf494Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8), chiLo := (31/64), chiHi := (1/2) }

private noncomputable def leaf494Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108987/67108864) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34357772288) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (125989243/67108864) }, upper := { exponent := 0, mantissa := (31/16) } }, logOuter := sk40LogOuterCertificate, logK := sk40LogKCertificate, logChi := chi69LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717051903/68715544576) } }, logDArg := sk40LogDArgCertificate }

private noncomputable def leaf494InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf494LocalValidity :
    LeafFacts leaf494Box leaf494Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf494Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34357772288) }) = true
      norm_num [leaf494Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf494CertificateValid :
    WideCertificateValid leaf494Box leaf494Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk40ValidityFacts chi69ValidityFacts
    leaf494LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf494CoverageChecked :
    coverageCheck (innerAD leaf494Box) leaf494InnerLog = true := by
  rfl'

private theorem leaf494InnerLogValid :
    leaf494InnerLog.Valid 8 (innerAD leaf494Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf494CoverageChecked

private noncomputable def leaf494InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629449/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf494InputLogOnePlusV_eq :
    leaf494InputLogOnePlusV = outerEnclosure 24
      (leaf494Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf494RoundedFacts : LeafRoundedFacts 8
    leaf494Certificate.logOnePlusV leaf494InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf494InputLogOnePlusV_eq }

private noncomputable def leaf494Inputs : Inputs :=
  inputsOfCaches globalInput sk40RoundedInputs
    chi69InputQChi innerPair100Input
    leaf494InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf494LowerChecked :
    lowerCheck 24 leaf494Box leaf494Inputs = true := by
  rfl'

private theorem leaf494CoversExact : CoversExact 8
    leaf494Box leaf494Certificate leaf494InnerLog leaf494Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk40RoundedFacts chi69RoundedFacts
    innerPair100RoundedFacts leaf494RoundedFacts (by rfl)

private theorem leaf494FlatSound : Sound leaf494Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf494CertificateValid
    leaf494InnerLogValid leaf494CoversExact leaf494LowerChecked

private noncomputable def leaf495Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (7/16), chiHi := (29/64) }

private noncomputable def leaf495Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108983/67108864) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34357897216) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (122122859/67108864) }, upper := { exponent := 0, mantissa := (1923/1024) } }, logOuter := sk41LogOuterCertificate, logK := sk41LogKCertificate, logChi := chi66LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717176831/68715794432) } }, logDArg := sk41LogDArgCertificate }

private noncomputable def leaf495InnerLog : WideLogData :=
  innerPair96Data

set_option maxRecDepth 1000000 in
private theorem leaf495LocalValidity :
    LeafFacts leaf495Box leaf495Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf495Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34357897216) }) = true
      norm_num [leaf495Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf495CertificateValid :
    WideCertificateValid leaf495Box leaf495Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk41ValidityFacts chi66ValidityFacts
    leaf495LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf495CoverageChecked :
    coverageCheck (innerAD leaf495Box) leaf495InnerLog = true := by
  rfl'

private theorem leaf495InnerLogValid :
    leaf495InnerLog.Valid 8 (innerAD leaf495Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint69PositiveFacts.valid leaf495CoverageChecked

private noncomputable def leaf495InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814709/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf495InputLogOnePlusV_eq :
    leaf495InputLogOnePlusV = outerEnclosure 24
      (leaf495Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf495RoundedFacts : LeafRoundedFacts 8
    leaf495Certificate.logOnePlusV leaf495InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf495InputLogOnePlusV_eq }

private noncomputable def leaf495Inputs : Inputs :=
  inputsOfCaches globalInput sk41RoundedInputs
    chi66InputQChi innerPair96Input
    leaf495InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf495LowerChecked :
    lowerCheck 24 leaf495Box leaf495Inputs = true := by
  rfl'

private theorem leaf495CoversExact : CoversExact 8
    leaf495Box leaf495Certificate leaf495InnerLog leaf495Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk41RoundedFacts chi66RoundedFacts
    innerPair96RoundedFacts leaf495RoundedFacts (by rfl)

private theorem leaf495FlatSound : Sound leaf495Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf495CertificateValid
    leaf495InnerLogValid leaf495CoversExact leaf495LowerChecked

private noncomputable def leaf496Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (29/64), chiHi := (15/32) }

private noncomputable def leaf496Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108985/67108864) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34357833728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (124088817/67108864) }, upper := { exponent := 0, mantissa := (977/512) } }, logOuter := sk41LogOuterCertificate, logK := sk41LogKCertificate, logChi := chi67LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717113343/68715667456) } }, logDArg := sk41LogDArgCertificate }

private noncomputable def leaf496InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf496LocalValidity :
    LeafFacts leaf496Box leaf496Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf496Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34357833728) }) = true
      norm_num [leaf496Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf496CertificateValid :
    WideCertificateValid leaf496Box leaf496Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk41ValidityFacts chi67ValidityFacts
    leaf496LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf496CoverageChecked :
    coverageCheck (innerAD leaf496Box) leaf496InnerLog = true := by
  rfl'

private theorem leaf496InnerLogValid :
    leaf496InnerLog.Valid 8 (innerAD leaf496Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf496CoverageChecked

private noncomputable def leaf496InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814717/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf496InputLogOnePlusV_eq :
    leaf496InputLogOnePlusV = outerEnclosure 24
      (leaf496Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf496RoundedFacts : LeafRoundedFacts 8
    leaf496Certificate.logOnePlusV leaf496InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf496InputLogOnePlusV_eq }

private noncomputable def leaf496Inputs : Inputs :=
  inputsOfCaches globalInput sk41RoundedInputs
    chi67InputQChi innerPair92Input
    leaf496InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf496LowerChecked :
    lowerCheck 24 leaf496Box leaf496Inputs = true := by
  rfl'

private theorem leaf496CoversExact : CoversExact 8
    leaf496Box leaf496Certificate leaf496InnerLog leaf496Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk41RoundedFacts chi67RoundedFacts
    innerPair92RoundedFacts leaf496RoundedFacts (by rfl)

private theorem leaf496FlatSound : Sound leaf496Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf496CertificateValid
    leaf496InnerLogValid leaf496CoversExact leaf496LowerChecked

private noncomputable def leaf497Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (7/16), chiHi := (29/64) }

private noncomputable def leaf497Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108985/67108864) }, vSqrt := { lower := (65531/65536), upper := (3817697735/3817537536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (123957753/67108864) }, upper := { exponent := 0, mantissa := (61/32) } }, logOuter := sk42LogOuterCertificate, logK := sk42LogKCertificate, logChi := chi66LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (7635235271/7635075072) } }, logDArg := sk42LogDArgCertificate }

private noncomputable def leaf497InnerLog : WideLogData :=
  innerPair200Data

set_option maxRecDepth 1000000 in
private theorem leaf497LocalValidity :
    LeafFacts leaf497Box leaf497Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf497Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (3817697735/3817537536) }) = true
      norm_num [leaf497Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf497CertificateValid :
    WideCertificateValid leaf497Box leaf497Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk42ValidityFacts chi66ValidityFacts
    leaf497LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf497CoverageChecked :
    coverageCheck (innerAD leaf497Box) leaf497InnerLog = true := by
  rfl'

private theorem leaf497InnerLogValid :
    leaf497InnerLog.Valid 8 (innerAD leaf497Box) :=
  wideLogDataValid_of_cachedCheck endpoint61PositiveFacts
    endpoint70PositiveFacts.valid leaf497CoverageChecked

private noncomputable def leaf497InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629433/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf497InputLogOnePlusV_eq :
    leaf497InputLogOnePlusV = outerEnclosure 24
      (leaf497Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf497RoundedFacts : LeafRoundedFacts 8
    leaf497Certificate.logOnePlusV leaf497InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf497InputLogOnePlusV_eq }

private noncomputable def leaf497Inputs : Inputs :=
  inputsOfCaches globalInput sk42RoundedInputs
    chi66InputQChi innerPair200Input
    leaf497InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf497LowerChecked :
    lowerCheck 24 leaf497Box leaf497Inputs = true := by
  rfl'

private theorem leaf497CoversExact : CoversExact 8
    leaf497Box leaf497Certificate leaf497InnerLog leaf497Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk42RoundedFacts chi66RoundedFacts
    innerPair200RoundedFacts leaf497RoundedFacts (by rfl)

private theorem leaf497FlatSound : Sound leaf497Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf497CertificateValid
    leaf497InnerLogValid leaf497CoversExact leaf497LowerChecked

private noncomputable def leaf498Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (29/64), chiHi := (15/32) }

private noncomputable def leaf498Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108987/67108864) }, vSqrt := { lower := (65531/65536), upper := (34359279615/34357772288) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (125989243/67108864) }, upper := { exponent := 0, mantissa := (31/16) } }, logOuter := sk42LogOuterCertificate, logK := sk42LogKCertificate, logChi := chi67LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68717051903/68715544576) } }, logDArg := sk42LogDArgCertificate }

private noncomputable def leaf498InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf498LocalValidity :
    LeafFacts leaf498Box leaf498Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf498Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34359279615/34357772288) }) = true
      norm_num [leaf498Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf498CertificateValid :
    WideCertificateValid leaf498Box leaf498Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk42ValidityFacts chi67ValidityFacts
    leaf498LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf498CoverageChecked :
    coverageCheck (innerAD leaf498Box) leaf498InnerLog = true := by
  rfl'

private theorem leaf498InnerLogValid :
    leaf498InnerLog.Valid 8 (innerAD leaf498Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf498CoverageChecked

private noncomputable def leaf498InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629449/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf498InputLogOnePlusV_eq :
    leaf498InputLogOnePlusV = outerEnclosure 24
      (leaf498Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf498RoundedFacts : LeafRoundedFacts 8
    leaf498Certificate.logOnePlusV leaf498InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf498InputLogOnePlusV_eq }

private noncomputable def leaf498Inputs : Inputs :=
  inputsOfCaches globalInput sk42RoundedInputs
    chi67InputQChi innerPair100Input
    leaf498InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf498LowerChecked :
    lowerCheck 24 leaf498Box leaf498Inputs = true := by
  rfl'

private theorem leaf498CoversExact : CoversExact 8
    leaf498Box leaf498Certificate leaf498InnerLog leaf498Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk42RoundedFacts chi67RoundedFacts
    innerPair100RoundedFacts leaf498RoundedFacts (by rfl)

private theorem leaf498FlatSound : Sound leaf498Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf498CertificateValid
    leaf498InnerLogValid leaf498CoversExact leaf498LowerChecked

private noncomputable def leaf499Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (15/32), chiHi := (31/64) }

private noncomputable def leaf499Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108987/67108864) }, vSqrt := { lower := (16383/16384), upper := (2290618641/2290518016) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (126054775/67108864) }, upper := { exponent := 0, mantissa := (1985/1024) } }, logOuter := sk41LogOuterCertificate, logK := sk41LogKCertificate, logChi := chi68LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (4581136657/4581036032) } }, logDArg := sk41LogDArgCertificate }

private noncomputable def leaf499InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf499LocalValidity :
    LeafFacts leaf499Box leaf499Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf499Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (2290618641/2290518016) }) = true
      norm_num [leaf499Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf499CertificateValid :
    WideCertificateValid leaf499Box leaf499Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk41ValidityFacts chi68ValidityFacts
    leaf499LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf499CoverageChecked :
    coverageCheck (innerAD leaf499Box) leaf499InnerLog = true := by
  rfl'

private theorem leaf499InnerLogValid :
    leaf499InnerLog.Valid 8 (innerAD leaf499Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf499CoverageChecked

private noncomputable def leaf499InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629449/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf499InputLogOnePlusV_eq :
    leaf499InputLogOnePlusV = outerEnclosure 24
      (leaf499Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf499RoundedFacts : LeafRoundedFacts 8
    leaf499Certificate.logOnePlusV leaf499InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf499InputLogOnePlusV_eq }

private noncomputable def leaf499Inputs : Inputs :=
  inputsOfCaches globalInput sk41RoundedInputs
    chi68InputQChi innerPair101Input
    leaf499InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf499LowerChecked :
    lowerCheck 24 leaf499Box leaf499Inputs = true := by
  rfl'

private theorem leaf499CoversExact : CoversExact 8
    leaf499Box leaf499Certificate leaf499InnerLog leaf499Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk41RoundedFacts chi68RoundedFacts
    innerPair101RoundedFacts leaf499RoundedFacts (by rfl)

private theorem leaf499FlatSound : Sound leaf499Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf499CertificateValid
    leaf499InnerLogValid leaf499CoversExact leaf499LowerChecked

private noncomputable def leaf500Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (31/64), chiHi := (1/2) }

private noncomputable def leaf500Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108989/67108864) }, vSqrt := { lower := (16383/16384), upper := (17179377663/17178853376) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (128020733/67108864) }, upper := { exponent := 0, mantissa := (63/32) } }, logOuter := sk41LogOuterCertificate, logK := sk41LogKCertificate, logChi := chi69LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (34358231039/34357706752) } }, logDArg := sk41LogDArgCertificate }

private noncomputable def leaf500InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf500LocalValidity :
    LeafFacts leaf500Box leaf500Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf500Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (17179377663/17178853376) }) = true
      norm_num [leaf500Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf500CertificateValid :
    WideCertificateValid leaf500Box leaf500Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk41ValidityFacts chi69ValidityFacts
    leaf500LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf500CoverageChecked :
    coverageCheck (innerAD leaf500Box) leaf500InnerLog = true := by
  rfl'

private theorem leaf500InnerLogValid :
    leaf500InnerLog.Valid 8 (innerAD leaf500Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf500CoverageChecked

private noncomputable def leaf500InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629337/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf500InputLogOnePlusV_eq :
    leaf500InputLogOnePlusV = outerEnclosure 24
      (leaf500Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf500RoundedFacts : LeafRoundedFacts 8
    leaf500Certificate.logOnePlusV leaf500InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf500InputLogOnePlusV_eq }

private noncomputable def leaf500Inputs : Inputs :=
  inputsOfCaches globalInput sk41RoundedInputs
    chi69InputQChi innerPair101Input
    leaf500InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf500LowerChecked :
    lowerCheck 24 leaf500Box leaf500Inputs = true := by
  rfl'

private theorem leaf500CoversExact : CoversExact 8
    leaf500Box leaf500Certificate leaf500InnerLog leaf500Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk41RoundedFacts chi69RoundedFacts
    innerPair101RoundedFacts leaf500RoundedFacts (by rfl)

private theorem leaf500FlatSound : Sound leaf500Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf500CertificateValid
    leaf500InnerLogValid leaf500CoversExact leaf500LowerChecked

private noncomputable def leaf501Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (15/32), chiHi := (31/64) }

private noncomputable def leaf501Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108989/67108864) }, vSqrt := { lower := (65531/65536), upper := (17179377663/17178853376) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (128020733/67108864) }, upper := { exponent := 0, mantissa := (63/32) } }, logOuter := sk42LogOuterCertificate, logK := sk42LogKCertificate, logChi := chi68LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (34358231039/34357706752) } }, logDArg := sk42LogDArgCertificate }

private noncomputable def leaf501InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf501LocalValidity :
    LeafFacts leaf501Box leaf501Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf501Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (17179377663/17178853376) }) = true
      norm_num [leaf501Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf501CertificateValid :
    WideCertificateValid leaf501Box leaf501Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk42ValidityFacts chi68ValidityFacts
    leaf501LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf501CoverageChecked :
    coverageCheck (innerAD leaf501Box) leaf501InnerLog = true := by
  rfl'

private theorem leaf501InnerLogValid :
    leaf501InnerLog.Valid 8 (innerAD leaf501Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf501CoverageChecked

private noncomputable def leaf501InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629337/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf501InputLogOnePlusV_eq :
    leaf501InputLogOnePlusV = outerEnclosure 24
      (leaf501Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf501RoundedFacts : LeafRoundedFacts 8
    leaf501Certificate.logOnePlusV leaf501InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf501InputLogOnePlusV_eq }

private noncomputable def leaf501Inputs : Inputs :=
  inputsOfCaches globalInput sk42RoundedInputs
    chi68InputQChi innerPair101Input
    leaf501InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf501LowerChecked :
    lowerCheck 24 leaf501Box leaf501Inputs = true := by
  rfl'

private theorem leaf501CoversExact : CoversExact 8
    leaf501Box leaf501Certificate leaf501InnerLog leaf501Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk42RoundedFacts chi68RoundedFacts
    innerPair101RoundedFacts leaf501RoundedFacts (by rfl)

private theorem leaf501FlatSound : Sound leaf501Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf501CertificateValid
    leaf501InnerLogValid leaf501CoversExact leaf501LowerChecked

private noncomputable def leaf502Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (31/64), chiHi := (1/2) }

private noncomputable def leaf502Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67108991/67108864) }, vSqrt := { lower := (65531/65536), upper := (5726459221/5726273536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (130052223/67108864) }, upper := { exponent := 1, mantissa := (1) } }, logOuter := sk42LogOuterCertificate, logK := sk42LogKCertificate, logChi := chi69LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (11452732757/11452547072) } }, logDArg := sk42LogDArgCertificate }

private noncomputable def leaf502InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf502LocalValidity :
    LeafFacts leaf502Box leaf502Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf502Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (5726459221/5726273536) }) = true
      norm_num [leaf502Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf502CertificateValid :
    WideCertificateValid leaf502Box leaf502Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk42ValidityFacts chi69ValidityFacts
    leaf502LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf502CoverageChecked :
    coverageCheck (innerAD leaf502Box) leaf502InnerLog = true := by
  rfl'

private theorem leaf502InnerLogValid :
    leaf502InnerLog.Valid 8 (innerAD leaf502Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf502CoverageChecked

private noncomputable def leaf502InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629353/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf502InputLogOnePlusV_eq :
    leaf502InputLogOnePlusV = outerEnclosure 24
      (leaf502Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf502RoundedFacts : LeafRoundedFacts 8
    leaf502Certificate.logOnePlusV leaf502InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf502InputLogOnePlusV_eq }

private noncomputable def leaf502Inputs : Inputs :=
  inputsOfCaches globalInput sk42RoundedInputs
    chi69InputQChi innerPair108Input
    leaf502InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf502LowerChecked :
    lowerCheck 24 leaf502Box leaf502Inputs = true := by
  rfl'

private theorem leaf502CoversExact : CoversExact 8
    leaf502Box leaf502Certificate leaf502InnerLog leaf502Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk42RoundedFacts chi69RoundedFacts
    innerPair108RoundedFacts leaf502RoundedFacts (by rfl)

private theorem leaf502FlatSound : Sound leaf502Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf502CertificateValid
    leaf502InnerLogValid leaf502CoversExact leaf502LowerChecked

private noncomputable def component11Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (25/16), chiLo := (3/8), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component11Node0_sound : Sound component11Node0Box :=
  sound_of_literal_split component11Node0Box leaf443Box leaf444Box
    .chi (25/64) (by rfl) (by rfl)
    leaf443FlatSound leaf444FlatSound

private noncomputable def component11Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (25/16), chiLo := (3/8), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component11Node1_sound : Sound component11Node1Box :=
  sound_of_literal_split component11Node1Box component11Node0Box leaf445Box
    .chi (13/32) (by rfl) (by rfl)
    component11Node0_sound leaf445FlatSound

private noncomputable def component11Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/16), kHi := (13/8), chiLo := (3/8), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component11Node2_sound : Sound component11Node2Box :=
  sound_of_literal_split component11Node2Box leaf446Box leaf447Box
    .chi (25/64) (by rfl) (by rfl)
    leaf446FlatSound leaf447FlatSound

private noncomputable def component11Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/16), kHi := (13/8), chiLo := (13/32), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component11Node3_sound : Sound component11Node3Box :=
  sound_of_literal_split component11Node3Box leaf448Box leaf449Box
    .chi (27/64) (by rfl) (by rfl)
    leaf448FlatSound leaf449FlatSound

private noncomputable def component11Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/16), kHi := (13/8), chiLo := (3/8), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component11Node4_sound : Sound component11Node4Box :=
  sound_of_literal_split component11Node4Box component11Node2Box component11Node3Box
    .chi (13/32) (by rfl) (by rfl)
    component11Node2_sound component11Node3_sound

private noncomputable def component11Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (13/8), chiLo := (3/8), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component11Node5_sound : Sound component11Node5Box :=
  sound_of_literal_split component11Node5Box component11Node1Box component11Node4Box
    .k (25/16) (by rfl) (by rfl)
    component11Node1_sound component11Node4_sound

private noncomputable def component11Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (25/16), chiLo := (7/16), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component11Node6_sound : Sound component11Node6Box :=
  sound_of_literal_split component11Node6Box leaf450Box leaf451Box
    .chi (15/32) (by rfl) (by rfl)
    leaf450FlatSound leaf451FlatSound

private noncomputable def component11Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/16), kHi := (13/8), chiLo := (7/16), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component11Node7_sound : Sound component11Node7Box :=
  sound_of_literal_split component11Node7Box leaf452Box leaf453Box
    .chi (15/32) (by rfl) (by rfl)
    leaf452FlatSound leaf453FlatSound

private noncomputable def component11Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (13/8), chiLo := (7/16), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component11Node8_sound : Sound component11Node8Box :=
  sound_of_literal_split component11Node8Box component11Node6Box component11Node7Box
    .k (25/16) (by rfl) (by rfl)
    component11Node6_sound component11Node7_sound

private noncomputable def component11Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (13/8), chiLo := (3/8), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component11Node9_sound : Sound component11Node9Box :=
  sound_of_literal_split component11Node9Box component11Node5Box component11Node8Box
    .chi (7/16) (by rfl) (by rfl)
    component11Node5_sound component11Node8_sound

private noncomputable def component11Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (27/16), chiLo := (3/8), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component11Node10_sound : Sound component11Node10Box :=
  sound_of_literal_split component11Node10Box leaf454Box leaf455Box
    .chi (25/64) (by rfl) (by rfl)
    leaf454FlatSound leaf455FlatSound

private noncomputable def component11Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (3/8), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component11Node11_sound : Sound component11Node11Box :=
  sound_of_literal_split component11Node11Box leaf456Box leaf457Box
    .chi (25/64) (by rfl) (by rfl)
    leaf456FlatSound leaf457FlatSound

private noncomputable def component11Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (7/4), chiLo := (3/8), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component11Node12_sound : Sound component11Node12Box :=
  sound_of_literal_split component11Node12Box component11Node10Box component11Node11Box
    .k (27/16) (by rfl) (by rfl)
    component11Node10_sound component11Node11_sound

private noncomputable def component11Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (27/16), chiLo := (13/32), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component11Node13_sound : Sound component11Node13Box :=
  sound_of_literal_split component11Node13Box leaf458Box leaf459Box
    .chi (27/64) (by rfl) (by rfl)
    leaf458FlatSound leaf459FlatSound

private noncomputable def component11Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (13/32), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component11Node14_sound : Sound component11Node14Box :=
  sound_of_literal_split component11Node14Box leaf460Box leaf461Box
    .chi (27/64) (by rfl) (by rfl)
    leaf460FlatSound leaf461FlatSound

private noncomputable def component11Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (7/4), chiLo := (13/32), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component11Node15_sound : Sound component11Node15Box :=
  sound_of_literal_split component11Node15Box component11Node13Box component11Node14Box
    .k (27/16) (by rfl) (by rfl)
    component11Node13_sound component11Node14_sound

private noncomputable def component11Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (7/4), chiLo := (3/8), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component11Node16_sound : Sound component11Node16Box :=
  sound_of_literal_split component11Node16Box component11Node12Box component11Node15Box
    .chi (13/32) (by rfl) (by rfl)
    component11Node12_sound component11Node15_sound

private noncomputable def component11Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (27/16), chiLo := (7/16), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component11Node17_sound : Sound component11Node17Box :=
  sound_of_literal_split component11Node17Box leaf462Box leaf463Box
    .chi (29/64) (by rfl) (by rfl)
    leaf462FlatSound leaf463FlatSound

private noncomputable def component11Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (7/16), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component11Node18_sound : Sound component11Node18Box :=
  sound_of_literal_split component11Node18Box leaf464Box leaf465Box
    .chi (29/64) (by rfl) (by rfl)
    leaf464FlatSound leaf465FlatSound

private noncomputable def component11Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (7/4), chiLo := (7/16), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component11Node19_sound : Sound component11Node19Box :=
  sound_of_literal_split component11Node19Box component11Node17Box component11Node18Box
    .k (27/16) (by rfl) (by rfl)
    component11Node17_sound component11Node18_sound

private noncomputable def component11Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (15/32), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component11Node20_sound : Sound component11Node20Box :=
  sound_of_literal_split component11Node20Box leaf467Box leaf468Box
    .chi (31/64) (by rfl) (by rfl)
    leaf467FlatSound leaf468FlatSound

private noncomputable def component11Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (7/4), chiLo := (15/32), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component11Node21_sound : Sound component11Node21Box :=
  sound_of_literal_split component11Node21Box leaf466Box component11Node20Box
    .k (27/16) (by rfl) (by rfl)
    leaf466FlatSound component11Node20_sound

private noncomputable def component11Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (7/4), chiLo := (7/16), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component11Node22_sound : Sound component11Node22Box :=
  sound_of_literal_split component11Node22Box component11Node19Box component11Node21Box
    .chi (15/32) (by rfl) (by rfl)
    component11Node19_sound component11Node21_sound

private noncomputable def component11Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (7/4), chiLo := (3/8), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component11Node23_sound : Sound component11Node23Box :=
  sound_of_literal_split component11Node23Box component11Node16Box component11Node22Box
    .chi (7/16) (by rfl) (by rfl)
    component11Node16_sound component11Node22_sound

private noncomputable def component11Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (7/4), chiLo := (3/8), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component11Node24_sound : Sound component11Node24Box :=
  sound_of_literal_split component11Node24Box component11Node9Box component11Node23Box
    .k (13/8) (by rfl) (by rfl)
    component11Node9_sound component11Node23_sound

private noncomputable def component11Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16), chiLo := (3/8), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component11Node25_sound : Sound component11Node25Box :=
  sound_of_literal_split component11Node25Box leaf469Box leaf470Box
    .chi (25/64) (by rfl) (by rfl)
    leaf469FlatSound leaf470FlatSound

private noncomputable def component11Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8), chiLo := (3/8), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component11Node26_sound : Sound component11Node26Box :=
  sound_of_literal_split component11Node26Box leaf471Box leaf472Box
    .chi (25/64) (by rfl) (by rfl)
    leaf471FlatSound leaf472FlatSound

private noncomputable def component11Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (15/8), chiLo := (3/8), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component11Node27_sound : Sound component11Node27Box :=
  sound_of_literal_split component11Node27Box component11Node25Box component11Node26Box
    .k (29/16) (by rfl) (by rfl)
    component11Node25_sound component11Node26_sound

private noncomputable def component11Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16), chiLo := (13/32), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component11Node28_sound : Sound component11Node28Box :=
  sound_of_literal_split component11Node28Box leaf473Box leaf474Box
    .chi (27/64) (by rfl) (by rfl)
    leaf473FlatSound leaf474FlatSound

private noncomputable def component11Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8), chiLo := (13/32), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component11Node29_sound : Sound component11Node29Box :=
  sound_of_literal_split component11Node29Box leaf475Box leaf476Box
    .chi (27/64) (by rfl) (by rfl)
    leaf475FlatSound leaf476FlatSound

private noncomputable def component11Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (15/8), chiLo := (13/32), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component11Node30_sound : Sound component11Node30Box :=
  sound_of_literal_split component11Node30Box component11Node28Box component11Node29Box
    .k (29/16) (by rfl) (by rfl)
    component11Node28_sound component11Node29_sound

private noncomputable def component11Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (15/8), chiLo := (3/8), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component11Node31_sound : Sound component11Node31Box :=
  sound_of_literal_split component11Node31Box component11Node27Box component11Node30Box
    .chi (13/32) (by rfl) (by rfl)
    component11Node27_sound component11Node30_sound

private noncomputable def component11Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (3/8), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component11Node32_sound : Sound component11Node32Box :=
  sound_of_literal_split component11Node32Box leaf477Box leaf478Box
    .chi (25/64) (by rfl) (by rfl)
    leaf477FlatSound leaf478FlatSound

private noncomputable def component11Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (3/8), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component11Node33_sound : Sound component11Node33Box :=
  sound_of_literal_split component11Node33Box leaf479Box leaf480Box
    .k (63/32) (by rfl) (by rfl)
    leaf479FlatSound leaf480FlatSound

private noncomputable def component11Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (25/64), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component11Node34_sound : Sound component11Node34Box :=
  sound_of_literal_split component11Node34Box leaf481Box leaf482Box
    .k (63/32) (by rfl) (by rfl)
    leaf481FlatSound leaf482FlatSound

private noncomputable def component11Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (3/8), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component11Node35_sound : Sound component11Node35Box :=
  sound_of_literal_split component11Node35Box component11Node33Box component11Node34Box
    .chi (25/64) (by rfl) (by rfl)
    component11Node33_sound component11Node34_sound

private noncomputable def component11Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (3/8), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component11Node36_sound : Sound component11Node36Box :=
  sound_of_literal_split component11Node36Box component11Node32Box component11Node35Box
    .k (31/16) (by rfl) (by rfl)
    component11Node32_sound component11Node35_sound

private noncomputable def component11Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (13/32), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component11Node37_sound : Sound component11Node37Box :=
  sound_of_literal_split component11Node37Box leaf483Box leaf484Box
    .chi (27/64) (by rfl) (by rfl)
    leaf483FlatSound leaf484FlatSound

private noncomputable def component11Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (13/32), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component11Node38_sound : Sound component11Node38Box :=
  sound_of_literal_split component11Node38Box leaf485Box leaf486Box
    .chi (27/64) (by rfl) (by rfl)
    leaf485FlatSound leaf486FlatSound

private noncomputable def component11Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (13/32), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component11Node39_sound : Sound component11Node39Box :=
  sound_of_literal_split component11Node39Box component11Node37Box component11Node38Box
    .k (31/16) (by rfl) (by rfl)
    component11Node37_sound component11Node38_sound

private noncomputable def component11Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (3/8), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component11Node40_sound : Sound component11Node40Box :=
  sound_of_literal_split component11Node40Box component11Node36Box component11Node39Box
    .chi (13/32) (by rfl) (by rfl)
    component11Node36_sound component11Node39_sound

private noncomputable def component11Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (2), chiLo := (3/8), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component11Node41_sound : Sound component11Node41Box :=
  sound_of_literal_split component11Node41Box component11Node31Box component11Node40Box
    .k (15/8) (by rfl) (by rfl)
    component11Node31_sound component11Node40_sound

private noncomputable def component11Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16), chiLo := (7/16), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component11Node42_sound : Sound component11Node42Box :=
  sound_of_literal_split component11Node42Box leaf487Box leaf488Box
    .chi (29/64) (by rfl) (by rfl)
    leaf487FlatSound leaf488FlatSound

private noncomputable def component11Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8), chiLo := (7/16), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component11Node43_sound : Sound component11Node43Box :=
  sound_of_literal_split component11Node43Box leaf489Box leaf490Box
    .chi (29/64) (by rfl) (by rfl)
    leaf489FlatSound leaf490FlatSound

private noncomputable def component11Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (15/8), chiLo := (7/16), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component11Node44_sound : Sound component11Node44Box :=
  sound_of_literal_split component11Node44Box component11Node42Box component11Node43Box
    .k (29/16) (by rfl) (by rfl)
    component11Node42_sound component11Node43_sound

private noncomputable def component11Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16), chiLo := (15/32), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component11Node45_sound : Sound component11Node45Box :=
  sound_of_literal_split component11Node45Box leaf491Box leaf492Box
    .chi (31/64) (by rfl) (by rfl)
    leaf491FlatSound leaf492FlatSound

private noncomputable def component11Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8), chiLo := (15/32), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component11Node46_sound : Sound component11Node46Box :=
  sound_of_literal_split component11Node46Box leaf493Box leaf494Box
    .chi (31/64) (by rfl) (by rfl)
    leaf493FlatSound leaf494FlatSound

private noncomputable def component11Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (15/8), chiLo := (15/32), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component11Node47_sound : Sound component11Node47Box :=
  sound_of_literal_split component11Node47Box component11Node45Box component11Node46Box
    .k (29/16) (by rfl) (by rfl)
    component11Node45_sound component11Node46_sound

private noncomputable def component11Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (15/8), chiLo := (7/16), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component11Node48_sound : Sound component11Node48Box :=
  sound_of_literal_split component11Node48Box component11Node44Box component11Node47Box
    .chi (15/32) (by rfl) (by rfl)
    component11Node44_sound component11Node47_sound

private noncomputable def component11Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (7/16), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component11Node49_sound : Sound component11Node49Box :=
  sound_of_literal_split component11Node49Box leaf495Box leaf496Box
    .chi (29/64) (by rfl) (by rfl)
    leaf495FlatSound leaf496FlatSound

private noncomputable def component11Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (7/16), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component11Node50_sound : Sound component11Node50Box :=
  sound_of_literal_split component11Node50Box leaf497Box leaf498Box
    .chi (29/64) (by rfl) (by rfl)
    leaf497FlatSound leaf498FlatSound

private noncomputable def component11Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (7/16), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component11Node51_sound : Sound component11Node51Box :=
  sound_of_literal_split component11Node51Box component11Node49Box component11Node50Box
    .k (31/16) (by rfl) (by rfl)
    component11Node49_sound component11Node50_sound

private noncomputable def component11Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (15/32), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component11Node52_sound : Sound component11Node52Box :=
  sound_of_literal_split component11Node52Box leaf499Box leaf500Box
    .chi (31/64) (by rfl) (by rfl)
    leaf499FlatSound leaf500FlatSound

private noncomputable def component11Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (15/32), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component11Node53_sound : Sound component11Node53Box :=
  sound_of_literal_split component11Node53Box leaf501Box leaf502Box
    .chi (31/64) (by rfl) (by rfl)
    leaf501FlatSound leaf502FlatSound

private noncomputable def component11Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (15/32), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component11Node54_sound : Sound component11Node54Box :=
  sound_of_literal_split component11Node54Box component11Node52Box component11Node53Box
    .k (31/16) (by rfl) (by rfl)
    component11Node52_sound component11Node53_sound

private noncomputable def component11Node55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (7/16), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component11Node55_sound : Sound component11Node55Box :=
  sound_of_literal_split component11Node55Box component11Node51Box component11Node54Box
    .chi (15/32) (by rfl) (by rfl)
    component11Node51_sound component11Node54_sound

private noncomputable def component11Node56Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (2), chiLo := (7/16), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component11Node56_sound : Sound component11Node56Box :=
  sound_of_literal_split component11Node56Box component11Node48Box component11Node55Box
    .k (15/8) (by rfl) (by rfl)
    component11Node48_sound component11Node55_sound

private noncomputable def component11Node57Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (2), chiLo := (3/8), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component11Node57_sound : Sound component11Node57Box :=
  sound_of_literal_split component11Node57Box component11Node41Box component11Node56Box
    .chi (7/16) (by rfl) (by rfl)
    component11Node41_sound component11Node56_sound

noncomputable def component11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (2), chiLo := (3/8), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
theorem component11_sound : Sound component11Box :=
  sound_of_literal_split component11Box component11Node24Box component11Node57Box
    .k (7/4) (by rfl) (by rfl)
    component11Node24_sound component11Node57_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
