import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch5
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

private noncomputable def leaf3783Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (73/32), chiLo := (3/8), chiHi := (25/64) }

private noncomputable def leaf3783Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217923/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68715739136) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (247424063/134217728) }, upper := { exponent := 0, mantissa := (3873/2048) } }, logOuter := sk85LogOuterCertificate, logK := sk85LogKCertificate, logChi := chi62LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434232831/137431478272) } }, logDArg := sk85LogDArgCertificate }

private noncomputable def leaf3783InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf3783LocalValidity :
    LeafFacts leaf3783Box leaf3783Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3783Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68715739136) }) = true
      norm_num [leaf3783Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3783CertificateValid :
    WideCertificateValid leaf3783Box leaf3783Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk85ValidityFacts chi62ValidityFacts
    leaf3783LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3783CoverageChecked :
    coverageCheck (innerAD leaf3783Box) leaf3783InnerLog = true := by
  rfl'

private theorem leaf3783InnerLogValid :
    leaf3783InnerLog.Valid 8 (innerAD leaf3783Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf3783CoverageChecked

private noncomputable def leaf3783InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629417/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3783InputLogOnePlusV_eq :
    leaf3783InputLogOnePlusV = outerEnclosure 24
      (leaf3783Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3783RoundedFacts : LeafRoundedFacts 8
    leaf3783Certificate.logOnePlusV leaf3783InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3783InputLogOnePlusV_eq }

private noncomputable def leaf3783Inputs : Inputs :=
  inputsOfCaches globalInput sk85RoundedInputs
    chi62InputQChi innerPair92Input
    leaf3783InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3783LowerChecked :
    lowerCheck 24 leaf3783Box leaf3783Inputs = true := by
  rfl'

private theorem leaf3783CoversExact : CoversExact 8
    leaf3783Box leaf3783Certificate leaf3783InnerLog leaf3783Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk85RoundedFacts chi62RoundedFacts
    innerPair92RoundedFacts leaf3783RoundedFacts (by rfl)

private theorem leaf3783FlatSound : Sound leaf3783Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3783CertificateValid
    leaf3783InnerLogValid leaf3783CoversExact leaf3783LowerChecked

private noncomputable def leaf3784Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (73/32), kHi := (37/16), chiLo := (3/8), chiHi := (25/64) }

private noncomputable def leaf3784Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217925/134217728) }, vSqrt := { lower := (65531/65536), upper := (22906164565/22905229312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (248996829/134217728) }, upper := { exponent := 0, mantissa := (1949/1024) } }, logOuter := sk86LogOuterCertificate, logK := sk86LogKCertificate, logChi := chi62LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (45811393877/45810458624) } }, logDArg := sk86LogDArgCertificate }

private noncomputable def leaf3784InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf3784LocalValidity :
    LeafFacts leaf3784Box leaf3784Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3784Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (22906164565/22905229312) }) = true
      norm_num [leaf3784Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3784CertificateValid :
    WideCertificateValid leaf3784Box leaf3784Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk86ValidityFacts chi62ValidityFacts
    leaf3784LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3784CoverageChecked :
    coverageCheck (innerAD leaf3784Box) leaf3784InnerLog = true := by
  rfl'

private theorem leaf3784InnerLogValid :
    leaf3784InnerLog.Valid 8 (innerAD leaf3784Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf3784CoverageChecked

private noncomputable def leaf3784InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629423/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3784InputLogOnePlusV_eq :
    leaf3784InputLogOnePlusV = outerEnclosure 24
      (leaf3784Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3784RoundedFacts : LeafRoundedFacts 8
    leaf3784Certificate.logOnePlusV leaf3784InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3784InputLogOnePlusV_eq }

private noncomputable def leaf3784Inputs : Inputs :=
  inputsOfCaches globalInput sk86RoundedInputs
    chi62InputQChi innerPair92Input
    leaf3784InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3784LowerChecked :
    lowerCheck 24 leaf3784Box leaf3784Inputs = true := by
  rfl'

private theorem leaf3784CoversExact : CoversExact 8
    leaf3784Box leaf3784Certificate leaf3784InnerLog leaf3784Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk86RoundedFacts chi62RoundedFacts
    innerPair92RoundedFacts leaf3784RoundedFacts (by rfl)

private theorem leaf3784FlatSound : Sound leaf3784Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3784CertificateValid
    leaf3784InnerLogValid leaf3784CoversExact leaf3784LowerChecked

private noncomputable def leaf3785Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (73/32), chiLo := (25/64), chiHi := (13/32) }

private noncomputable def leaf3785Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217925/134217728) }, vSqrt := { lower := (65531/65536), upper := (22906164565/22905196544) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (252142365/134217728) }, upper := { exponent := 0, mantissa := (1973/1024) } }, logOuter := sk85LogOuterCertificate, logK := sk85LogKCertificate, logChi := chi63LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (45811361109/45810393088) } }, logDArg := sk85LogDArgCertificate }

private noncomputable def leaf3785InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3785LocalValidity :
    LeafFacts leaf3785Box leaf3785Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3785Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (22906164565/22905196544) }) = true
      norm_num [leaf3785Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3785CertificateValid :
    WideCertificateValid leaf3785Box leaf3785Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk85ValidityFacts chi63ValidityFacts
    leaf3785LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3785CoverageChecked :
    coverageCheck (innerAD leaf3785Box) leaf3785InnerLog = true := by
  rfl'

private theorem leaf3785InnerLogValid :
    leaf3785InnerLog.Valid 8 (innerAD leaf3785Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3785CoverageChecked

private noncomputable def leaf3785InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629435/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3785InputLogOnePlusV_eq :
    leaf3785InputLogOnePlusV = outerEnclosure 24
      (leaf3785Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3785RoundedFacts : LeafRoundedFacts 8
    leaf3785Certificate.logOnePlusV leaf3785InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3785InputLogOnePlusV_eq }

private noncomputable def leaf3785Inputs : Inputs :=
  inputsOfCaches globalInput sk85RoundedInputs
    chi63InputQChi innerPair100Input
    leaf3785InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3785LowerChecked :
    lowerCheck 24 leaf3785Box leaf3785Inputs = true := by
  rfl'

private theorem leaf3785CoversExact : CoversExact 8
    leaf3785Box leaf3785Certificate leaf3785InnerLog leaf3785Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk85RoundedFacts chi63RoundedFacts
    innerPair100RoundedFacts leaf3785RoundedFacts (by rfl)

private theorem leaf3785FlatSound : Sound leaf3785Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3785CertificateValid
    leaf3785InnerLogValid leaf3785CoversExact leaf3785LowerChecked

private noncomputable def leaf3786Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (73/32), kHi := (37/16), chiLo := (25/64), chiHi := (13/32) }

private noncomputable def leaf3786Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217927/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68715536384) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (253780663/134217728) }, upper := { exponent := 0, mantissa := (993/512) } }, logOuter := sk86LogOuterCertificate, logK := sk86LogKCertificate, logChi := chi63LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434030079/137431072768) } }, logDArg := sk86LogDArgCertificate }

private noncomputable def leaf3786InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf3786LocalValidity :
    LeafFacts leaf3786Box leaf3786Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3786Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68715536384) }) = true
      norm_num [leaf3786Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3786CertificateValid :
    WideCertificateValid leaf3786Box leaf3786Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk86ValidityFacts chi63ValidityFacts
    leaf3786LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3786CoverageChecked :
    coverageCheck (innerAD leaf3786Box) leaf3786InnerLog = true := by
  rfl'

private theorem leaf3786InnerLogValid :
    leaf3786InnerLog.Valid 8 (innerAD leaf3786Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf3786CoverageChecked

private noncomputable def leaf3786InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814721/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3786InputLogOnePlusV_eq :
    leaf3786InputLogOnePlusV = outerEnclosure 24
      (leaf3786Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3786RoundedFacts : LeafRoundedFacts 8
    leaf3786Certificate.logOnePlusV leaf3786InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3786InputLogOnePlusV_eq }

private noncomputable def leaf3786Inputs : Inputs :=
  inputsOfCaches globalInput sk86RoundedInputs
    chi63InputQChi innerPair101Input
    leaf3786InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3786LowerChecked :
    lowerCheck 24 leaf3786Box leaf3786Inputs = true := by
  rfl'

private theorem leaf3786CoversExact : CoversExact 8
    leaf3786Box leaf3786Certificate leaf3786InnerLog leaf3786Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk86RoundedFacts chi63RoundedFacts
    innerPair101RoundedFacts leaf3786RoundedFacts (by rfl)

private theorem leaf3786FlatSound : Sound leaf3786Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3786CertificateValid
    leaf3786InnerLogValid leaf3786CoversExact leaf3786LowerChecked

private noncomputable def leaf3787Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (75/32), chiLo := (3/8), chiHi := (25/64) }

private noncomputable def leaf3787Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217927/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68715636736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (250569595/134217728) }, upper := { exponent := 0, mantissa := (3923/2048) } }, logOuter := sk79LogOuterCertificate, logK := sk79LogKCertificate, logChi := chi62LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434130431/137431273472) } }, logDArg := sk79LogDArgCertificate }

private noncomputable def leaf3787InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf3787LocalValidity :
    LeafFacts leaf3787Box leaf3787Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3787Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68715636736) }) = true
      norm_num [leaf3787Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3787CertificateValid :
    WideCertificateValid leaf3787Box leaf3787Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk79ValidityFacts chi62ValidityFacts
    leaf3787LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3787CoverageChecked :
    coverageCheck (innerAD leaf3787Box) leaf3787InnerLog = true := by
  rfl'

private theorem leaf3787InnerLogValid :
    leaf3787InnerLog.Valid 8 (innerAD leaf3787Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf3787CoverageChecked

private noncomputable def leaf3787InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814715/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3787InputLogOnePlusV_eq :
    leaf3787InputLogOnePlusV = outerEnclosure 24
      (leaf3787Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3787RoundedFacts : LeafRoundedFacts 8
    leaf3787Certificate.logOnePlusV leaf3787InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3787InputLogOnePlusV_eq }

private noncomputable def leaf3787Inputs : Inputs :=
  inputsOfCaches globalInput sk79RoundedInputs
    chi62InputQChi innerPair92Input
    leaf3787InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3787LowerChecked :
    lowerCheck 24 leaf3787Box leaf3787Inputs = true := by
  rfl'

private theorem leaf3787CoversExact : CoversExact 8
    leaf3787Box leaf3787Certificate leaf3787InnerLog leaf3787Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk79RoundedFacts chi62RoundedFacts
    innerPair92RoundedFacts leaf3787RoundedFacts (by rfl)

private theorem leaf3787FlatSound : Sound leaf3787Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3787CertificateValid
    leaf3787InnerLogValid leaf3787CoversExact leaf3787LowerChecked

private noncomputable def leaf3788Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (75/32), kHi := (19/8), chiLo := (3/8), chiHi := (25/64) }

private noncomputable def leaf3788Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217929/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68715585536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (252142361/134217728) }, upper := { exponent := 0, mantissa := (987/512) } }, logOuter := sk80LogOuterCertificate, logK := sk80LogKCertificate, logChi := chi62LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434079231/137431171072) } }, logDArg := sk80LogDArgCertificate }

private noncomputable def leaf3788InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3788LocalValidity :
    LeafFacts leaf3788Box leaf3788Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3788Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68715585536) }) = true
      norm_num [leaf3788Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3788CertificateValid :
    WideCertificateValid leaf3788Box leaf3788Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk80ValidityFacts chi62ValidityFacts
    leaf3788LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3788CoverageChecked :
    coverageCheck (innerAD leaf3788Box) leaf3788InnerLog = true := by
  rfl'

private theorem leaf3788InnerLogValid :
    leaf3788InnerLog.Valid 8 (innerAD leaf3788Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3788CoverageChecked

private noncomputable def leaf3788InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907359/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3788InputLogOnePlusV_eq :
    leaf3788InputLogOnePlusV = outerEnclosure 24
      (leaf3788Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3788RoundedFacts : LeafRoundedFacts 8
    leaf3788Certificate.logOnePlusV leaf3788InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3788InputLogOnePlusV_eq }

private noncomputable def leaf3788Inputs : Inputs :=
  inputsOfCaches globalInput sk80RoundedInputs
    chi62InputQChi innerPair100Input
    leaf3788InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3788LowerChecked :
    lowerCheck 24 leaf3788Box leaf3788Inputs = true := by
  rfl'

private theorem leaf3788CoversExact : CoversExact 8
    leaf3788Box leaf3788Certificate leaf3788InnerLog leaf3788Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk80RoundedFacts chi62RoundedFacts
    innerPair100RoundedFacts leaf3788RoundedFacts (by rfl)

private theorem leaf3788FlatSound : Sound leaf3788Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3788CertificateValid
    leaf3788InnerLogValid leaf3788CoversExact leaf3788LowerChecked

private noncomputable def leaf3789Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (75/32), chiLo := (25/64), chiHi := (13/32) }

private noncomputable def leaf3789Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217929/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68715483136) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (255418961/134217728) }, upper := { exponent := 0, mantissa := (1999/1024) } }, logOuter := sk79LogOuterCertificate, logK := sk79LogKCertificate, logChi := chi63LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137433976831/137430966272) } }, logDArg := sk79LogDArgCertificate }

private noncomputable def leaf3789InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf3789LocalValidity :
    LeafFacts leaf3789Box leaf3789Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3789Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68715483136) }) = true
      norm_num [leaf3789Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3789CertificateValid :
    WideCertificateValid leaf3789Box leaf3789Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk79ValidityFacts chi63ValidityFacts
    leaf3789LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3789CoverageChecked :
    coverageCheck (innerAD leaf3789Box) leaf3789InnerLog = true := by
  rfl'

private theorem leaf3789InnerLogValid :
    leaf3789InnerLog.Valid 8 (innerAD leaf3789Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf3789CoverageChecked

private noncomputable def leaf3789InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (1453681/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3789InputLogOnePlusV_eq :
    leaf3789InputLogOnePlusV = outerEnclosure 24
      (leaf3789Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3789RoundedFacts : LeafRoundedFacts 8
    leaf3789Certificate.logOnePlusV leaf3789InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3789InputLogOnePlusV_eq }

private noncomputable def leaf3789Inputs : Inputs :=
  inputsOfCaches globalInput sk79RoundedInputs
    chi63InputQChi innerPair101Input
    leaf3789InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3789LowerChecked :
    lowerCheck 24 leaf3789Box leaf3789Inputs = true := by
  rfl'

private theorem leaf3789CoversExact : CoversExact 8
    leaf3789Box leaf3789Certificate leaf3789InnerLog leaf3789Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk79RoundedFacts chi63RoundedFacts
    innerPair101RoundedFacts leaf3789RoundedFacts (by rfl)

private theorem leaf3789FlatSound : Sound leaf3789Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3789CertificateValid
    leaf3789InnerLogValid leaf3789CoversExact leaf3789LowerChecked

private noncomputable def leaf3790Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (75/32), kHi := (19/8), chiLo := (25/64), chiHi := (13/32) }

private noncomputable def leaf3790Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217931/134217728) }, vSqrt := { lower := (65531/65536), upper := (22906164565/22905143296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (257057259/134217728) }, upper := { exponent := 0, mantissa := (503/256) } }, logOuter := sk80LogOuterCertificate, logK := sk80LogKCertificate, logChi := chi63LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (45811307861/45810286592) } }, logDArg := sk80LogDArgCertificate }

private noncomputable def leaf3790InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf3790LocalValidity :
    LeafFacts leaf3790Box leaf3790Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3790Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (22906164565/22905143296) }) = true
      norm_num [leaf3790Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3790CertificateValid :
    WideCertificateValid leaf3790Box leaf3790Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk80ValidityFacts chi63ValidityFacts
    leaf3790LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3790CoverageChecked :
    coverageCheck (innerAD leaf3790Box) leaf3790InnerLog = true := by
  rfl'

private theorem leaf3790InnerLogValid :
    leaf3790InnerLog.Valid 8 (innerAD leaf3790Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf3790CoverageChecked

private noncomputable def leaf3790InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629455/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3790InputLogOnePlusV_eq :
    leaf3790InputLogOnePlusV = outerEnclosure 24
      (leaf3790Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3790RoundedFacts : LeafRoundedFacts 8
    leaf3790Certificate.logOnePlusV leaf3790InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3790InputLogOnePlusV_eq }

private noncomputable def leaf3790Inputs : Inputs :=
  inputsOfCaches globalInput sk80RoundedInputs
    chi63InputQChi innerPair101Input
    leaf3790InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3790LowerChecked :
    lowerCheck 24 leaf3790Box leaf3790Inputs = true := by
  rfl'

private theorem leaf3790CoversExact : CoversExact 8
    leaf3790Box leaf3790Certificate leaf3790InnerLog leaf3790Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk80RoundedFacts chi63RoundedFacts
    innerPair101RoundedFacts leaf3790RoundedFacts (by rfl)

private theorem leaf3790FlatSound : Sound leaf3790Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3790CertificateValid
    leaf3790InnerLogValid leaf3790CoversExact leaf3790LowerChecked

private noncomputable def leaf3791Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (73/32), chiLo := (13/32), chiHi := (27/64) }

private noncomputable def leaf3791Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217927/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68715440128) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (256860667/134217728) }, upper := { exponent := 0, mantissa := (4019/2048) } }, logOuter := sk85LogOuterCertificate, logK := sk85LogKCertificate, logChi := chi64LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137433933823/137430880256) } }, logDArg := sk85LogDArgCertificate }

private noncomputable def leaf3791InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf3791LocalValidity :
    LeafFacts leaf3791Box leaf3791Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3791Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68715440128) }) = true
      norm_num [leaf3791Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3791CertificateValid :
    WideCertificateValid leaf3791Box leaf3791Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk85ValidityFacts chi64ValidityFacts
    leaf3791LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3791CoverageChecked :
    coverageCheck (innerAD leaf3791Box) leaf3791InnerLog = true := by
  rfl'

private theorem leaf3791InnerLogValid :
    leaf3791InnerLog.Valid 8 (innerAD leaf3791Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf3791CoverageChecked

private noncomputable def leaf3791InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814727/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3791InputLogOnePlusV_eq :
    leaf3791InputLogOnePlusV = outerEnclosure 24
      (leaf3791Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3791RoundedFacts : LeafRoundedFacts 8
    leaf3791Certificate.logOnePlusV leaf3791InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3791InputLogOnePlusV_eq }

private noncomputable def leaf3791Inputs : Inputs :=
  inputsOfCaches globalInput sk85RoundedInputs
    chi64InputQChi innerPair101Input
    leaf3791InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3791LowerChecked :
    lowerCheck 24 leaf3791Box leaf3791Inputs = true := by
  rfl'

private theorem leaf3791CoversExact : CoversExact 8
    leaf3791Box leaf3791Certificate leaf3791InnerLog leaf3791Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk85RoundedFacts chi64RoundedFacts
    innerPair101RoundedFacts leaf3791RoundedFacts (by rfl)

private theorem leaf3791FlatSound : Sound leaf3791Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3791CertificateValid
    leaf3791InnerLogValid leaf3791CoversExact leaf3791LowerChecked

private noncomputable def leaf3792Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (73/32), kHi := (37/16), chiLo := (13/32), chiHi := (27/64) }

private noncomputable def leaf3792Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217929/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68715384832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (258564497/134217728) }, upper := { exponent := 0, mantissa := (2023/1024) } }, logOuter := sk86LogOuterCertificate, logK := sk86LogKCertificate, logChi := chi64LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137433878527/137430769664) } }, logDArg := sk86LogDArgCertificate }

private noncomputable def leaf3792InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf3792LocalValidity :
    LeafFacts leaf3792Box leaf3792Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3792Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68715384832) }) = true
      norm_num [leaf3792Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3792CertificateValid :
    WideCertificateValid leaf3792Box leaf3792Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk86ValidityFacts chi64ValidityFacts
    leaf3792LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3792CoverageChecked :
    coverageCheck (innerAD leaf3792Box) leaf3792InnerLog = true := by
  rfl'

private theorem leaf3792InnerLogValid :
    leaf3792InnerLog.Valid 8 (innerAD leaf3792Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf3792CoverageChecked

private noncomputable def leaf3792InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907365/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3792InputLogOnePlusV_eq :
    leaf3792InputLogOnePlusV = outerEnclosure 24
      (leaf3792Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3792RoundedFacts : LeafRoundedFacts 8
    leaf3792Certificate.logOnePlusV leaf3792InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3792InputLogOnePlusV_eq }

private noncomputable def leaf3792Inputs : Inputs :=
  inputsOfCaches globalInput sk86RoundedInputs
    chi64InputQChi innerPair101Input
    leaf3792InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3792LowerChecked :
    lowerCheck 24 leaf3792Box leaf3792Inputs = true := by
  rfl'

private theorem leaf3792CoversExact : CoversExact 8
    leaf3792Box leaf3792Certificate leaf3792InnerLog leaf3792Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk86RoundedFacts chi64RoundedFacts
    innerPair101RoundedFacts leaf3792RoundedFacts (by rfl)

private theorem leaf3792FlatSound : Sound leaf3792Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3792CertificateValid
    leaf3792InnerLogValid leaf3792CoversExact leaf3792LowerChecked

private noncomputable def leaf3793Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (73/32), chiLo := (27/64), chiHi := (7/16) }

private noncomputable def leaf3793Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217929/134217728) }, vSqrt := { lower := (65531/65536), upper := (34358722559/34357645312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (261578969/134217728) }, upper := { exponent := 0, mantissa := (1023/512) } }, logOuter := sk85LogOuterCertificate, logK := sk85LogKCertificate, logChi := chi65LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68716367871/68715290624) } }, logDArg := sk85LogDArgCertificate }

private noncomputable def leaf3793InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf3793LocalValidity :
    LeafFacts leaf3793Box leaf3793Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3793Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358722559/34357645312) }) = true
      norm_num [leaf3793Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3793CertificateValid :
    WideCertificateValid leaf3793Box leaf3793Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk85ValidityFacts chi65ValidityFacts
    leaf3793LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3793CoverageChecked :
    coverageCheck (innerAD leaf3793Box) leaf3793InnerLog = true := by
  rfl'

private theorem leaf3793InnerLogValid :
    leaf3793InnerLog.Valid 8 (innerAD leaf3793Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf3793CoverageChecked

private noncomputable def leaf3793InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (363417/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf3793InputLogOnePlusV_eq :
    leaf3793InputLogOnePlusV = outerEnclosure 24
      (leaf3793Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3793RoundedFacts : LeafRoundedFacts 8
    leaf3793Certificate.logOnePlusV leaf3793InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3793InputLogOnePlusV_eq }

private noncomputable def leaf3793Inputs : Inputs :=
  inputsOfCaches globalInput sk85RoundedInputs
    chi65InputQChi innerPair108Input
    leaf3793InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3793LowerChecked :
    lowerCheck 24 leaf3793Box leaf3793Inputs = true := by
  rfl'

private theorem leaf3793CoversExact : CoversExact 8
    leaf3793Box leaf3793Certificate leaf3793InnerLog leaf3793Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk85RoundedFacts chi65RoundedFacts
    innerPair108RoundedFacts leaf3793RoundedFacts (by rfl)

private theorem leaf3793FlatSound : Sound leaf3793Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3793CertificateValid
    leaf3793InnerLogValid leaf3793CoversExact leaf3793LowerChecked

private noncomputable def leaf3794Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (73/32), kHi := (37/16), chiLo := (27/64), chiHi := (7/16) }

private noncomputable def leaf3794Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217931/134217728) }, vSqrt := { lower := (65531/65536), upper := (34358722559/34357616640) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (263348331/134217728) }, upper := { exponent := 1, mantissa := (515/512) } }, logOuter := sk86LogOuterCertificate, logK := sk86LogKCertificate, logChi := chi65LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68716339199/68715233280) } }, logDArg := sk86LogDArgCertificate }

private noncomputable def leaf3794InnerLog : WideLogData :=
  innerPair110Data

set_option maxRecDepth 1000000 in
private theorem leaf3794LocalValidity :
    LeafFacts leaf3794Box leaf3794Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3794Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358722559/34357616640) }) = true
      norm_num [leaf3794Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3794CertificateValid :
    WideCertificateValid leaf3794Box leaf3794Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk86ValidityFacts chi65ValidityFacts
    leaf3794LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3794CoverageChecked :
    coverageCheck (innerAD leaf3794Box) leaf3794InnerLog = true := by
  rfl'

private theorem leaf3794InnerLogValid :
    leaf3794InnerLog.Valid 8 (innerAD leaf3794Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint72PositiveFacts.valid leaf3794CoverageChecked

private noncomputable def leaf3794InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629351/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3794InputLogOnePlusV_eq :
    leaf3794InputLogOnePlusV = outerEnclosure 24
      (leaf3794Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3794RoundedFacts : LeafRoundedFacts 8
    leaf3794Certificate.logOnePlusV leaf3794InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3794InputLogOnePlusV_eq }

private noncomputable def leaf3794Inputs : Inputs :=
  inputsOfCaches globalInput sk86RoundedInputs
    chi65InputQChi innerPair110Input
    leaf3794InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3794LowerChecked :
    lowerCheck 24 leaf3794Box leaf3794Inputs = true := by
  rfl'

private theorem leaf3794CoversExact : CoversExact 8
    leaf3794Box leaf3794Certificate leaf3794InnerLog leaf3794Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk86RoundedFacts chi65RoundedFacts
    innerPair110RoundedFacts leaf3794RoundedFacts (by rfl)

private theorem leaf3794FlatSound : Sound leaf3794Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3794CertificateValid
    leaf3794InnerLogValid leaf3794CoversExact leaf3794LowerChecked

private noncomputable def leaf3795Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (75/32), chiLo := (13/32), chiHi := (27/64) }

private noncomputable def leaf3795Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217931/134217728) }, vSqrt := { lower := (65531/65536), upper := (288728761/288719872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (260268327/134217728) }, upper := { exponent := 0, mantissa := (4073/2048) } }, logOuter := sk79LogOuterCertificate, logK := sk79LogKCertificate, logChi := chi64LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (577448633/577439744) } }, logDArg := sk79LogDArgCertificate }

private noncomputable def leaf3795InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf3795LocalValidity :
    LeafFacts leaf3795Box leaf3795Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3795Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (288728761/288719872) }) = true
      norm_num [leaf3795Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3795CertificateValid :
    WideCertificateValid leaf3795Box leaf3795Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk79ValidityFacts chi64ValidityFacts
    leaf3795LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3795CoverageChecked :
    coverageCheck (innerAD leaf3795Box) leaf3795InnerLog = true := by
  rfl'

private theorem leaf3795InnerLogValid :
    leaf3795InnerLog.Valid 8 (innerAD leaf3795Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf3795CoverageChecked

private noncomputable def leaf3795InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629339/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3795InputLogOnePlusV_eq :
    leaf3795InputLogOnePlusV = outerEnclosure 24
      (leaf3795Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3795RoundedFacts : LeafRoundedFacts 8
    leaf3795Certificate.logOnePlusV leaf3795InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3795InputLogOnePlusV_eq }

private noncomputable def leaf3795Inputs : Inputs :=
  inputsOfCaches globalInput sk79RoundedInputs
    chi64InputQChi innerPair108Input
    leaf3795InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3795LowerChecked :
    lowerCheck 24 leaf3795Box leaf3795Inputs = true := by
  rfl'

private theorem leaf3795CoversExact : CoversExact 8
    leaf3795Box leaf3795Certificate leaf3795InnerLog leaf3795Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk79RoundedFacts chi64RoundedFacts
    innerPair108RoundedFacts leaf3795RoundedFacts (by rfl)

private theorem leaf3795FlatSound : Sound leaf3795Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3795CertificateValid
    leaf3795InnerLogValid leaf3795CoversExact leaf3795LowerChecked

private noncomputable def leaf3796Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (75/32), kHi := (19/8), chiLo := (13/32), chiHi := (27/64) }

private noncomputable def leaf3796Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217933/134217728) }, vSqrt := { lower := (65531/65536), upper := (34358722559/34357637120) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (261972157/134217728) }, upper := { exponent := 1, mantissa := (1025/1024) } }, logOuter := sk80LogOuterCertificate, logK := sk80LogKCertificate, logChi := chi64LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68716359679/68715274240) } }, logDArg := sk80LogDArgCertificate }

private noncomputable def leaf3796InnerLog : WideLogData :=
  innerPair110Data

set_option maxRecDepth 1000000 in
private theorem leaf3796LocalValidity :
    LeafFacts leaf3796Box leaf3796Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3796Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358722559/34357637120) }) = true
      norm_num [leaf3796Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3796CertificateValid :
    WideCertificateValid leaf3796Box leaf3796Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk80ValidityFacts chi64ValidityFacts
    leaf3796LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3796CoverageChecked :
    coverageCheck (innerAD leaf3796Box) leaf3796InnerLog = true := by
  rfl'

private theorem leaf3796InnerLogValid :
    leaf3796InnerLog.Valid 8 (innerAD leaf3796Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint72PositiveFacts.valid leaf3796CoverageChecked

private noncomputable def leaf3796InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814673/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3796InputLogOnePlusV_eq :
    leaf3796InputLogOnePlusV = outerEnclosure 24
      (leaf3796Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3796RoundedFacts : LeafRoundedFacts 8
    leaf3796Certificate.logOnePlusV leaf3796InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3796InputLogOnePlusV_eq }

private noncomputable def leaf3796Inputs : Inputs :=
  inputsOfCaches globalInput sk80RoundedInputs
    chi64InputQChi innerPair110Input
    leaf3796InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3796LowerChecked :
    lowerCheck 24 leaf3796Box leaf3796Inputs = true := by
  rfl'

private theorem leaf3796CoversExact : CoversExact 8
    leaf3796Box leaf3796Certificate leaf3796InnerLog leaf3796Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk80RoundedFacts chi64RoundedFacts
    innerPair110RoundedFacts leaf3796RoundedFacts (by rfl)

private theorem leaf3796FlatSound : Sound leaf3796Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3796CertificateValid
    leaf3796InnerLogValid leaf3796CoversExact leaf3796LowerChecked

private noncomputable def leaf3797Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (75/32), chiLo := (27/64), chiHi := (7/16) }

private noncomputable def leaf3797Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217933/134217728) }, vSqrt := { lower := (65531/65536), upper := (34358722559/34357587968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (265117693/134217728) }, upper := { exponent := 1, mantissa := (1037/1024) } }, logOuter := sk79LogOuterCertificate, logK := sk79LogKCertificate, logChi := chi65LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68716310527/68715175936) } }, logDArg := sk79LogDArgCertificate }

private noncomputable def leaf3797InnerLog : WideLogData :=
  innerPair110Data

set_option maxRecDepth 1000000 in
private theorem leaf3797LocalValidity :
    LeafFacts leaf3797Box leaf3797Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3797Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358722559/34357587968) }) = true
      norm_num [leaf3797Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3797CertificateValid :
    WideCertificateValid leaf3797Box leaf3797Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk79ValidityFacts chi65ValidityFacts
    leaf3797LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3797CoverageChecked :
    coverageCheck (innerAD leaf3797Box) leaf3797InnerLog = true := by
  rfl'

private theorem leaf3797InnerLogValid :
    leaf3797InnerLog.Valid 8 (innerAD leaf3797Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint72PositiveFacts.valid leaf3797CoverageChecked

private noncomputable def leaf3797InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814679/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3797InputLogOnePlusV_eq :
    leaf3797InputLogOnePlusV = outerEnclosure 24
      (leaf3797Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3797RoundedFacts : LeafRoundedFacts 8
    leaf3797Certificate.logOnePlusV leaf3797InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3797InputLogOnePlusV_eq }

private noncomputable def leaf3797Inputs : Inputs :=
  inputsOfCaches globalInput sk79RoundedInputs
    chi65InputQChi innerPair110Input
    leaf3797InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3797LowerChecked :
    lowerCheck 24 leaf3797Box leaf3797Inputs = true := by
  rfl'

private theorem leaf3797CoversExact : CoversExact 8
    leaf3797Box leaf3797Certificate leaf3797InnerLog leaf3797Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk79RoundedFacts chi65RoundedFacts
    innerPair110RoundedFacts leaf3797RoundedFacts (by rfl)

private theorem leaf3797FlatSound : Sound leaf3797Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3797CertificateValid
    leaf3797InnerLogValid leaf3797CoversExact leaf3797LowerChecked

private noncomputable def leaf3798Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (75/32), kHi := (19/8), chiLo := (27/64), chiHi := (7/16) }

private noncomputable def leaf3798Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217935/134217728) }, vSqrt := { lower := (65531/65536), upper := (34358722559/34357559296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (266887055/134217728) }, upper := { exponent := 1, mantissa := (261/256) } }, logOuter := sk80LogOuterCertificate, logK := sk80LogKCertificate, logChi := chi65LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68716281855/68715118592) } }, logDArg := sk80LogDArgCertificate }

private noncomputable def leaf3798InnerLog : WideLogData :=
  innerPair110Data

set_option maxRecDepth 1000000 in
private theorem leaf3798LocalValidity :
    LeafFacts leaf3798Box leaf3798Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3798Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358722559/34357559296) }) = true
      norm_num [leaf3798Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3798CertificateValid :
    WideCertificateValid leaf3798Box leaf3798Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk80ValidityFacts chi65ValidityFacts
    leaf3798LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3798CoverageChecked :
    coverageCheck (innerAD leaf3798Box) leaf3798InnerLog = true := by
  rfl'

private theorem leaf3798InnerLogValid :
    leaf3798InnerLog.Valid 8 (innerAD leaf3798Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint72PositiveFacts.valid leaf3798CoverageChecked

private noncomputable def leaf3798InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629365/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3798InputLogOnePlusV_eq :
    leaf3798InputLogOnePlusV = outerEnclosure 24
      (leaf3798Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3798RoundedFacts : LeafRoundedFacts 8
    leaf3798Certificate.logOnePlusV leaf3798InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3798InputLogOnePlusV_eq }

private noncomputable def leaf3798Inputs : Inputs :=
  inputsOfCaches globalInput sk80RoundedInputs
    chi65InputQChi innerPair110Input
    leaf3798InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3798LowerChecked :
    lowerCheck 24 leaf3798Box leaf3798Inputs = true := by
  rfl'

private theorem leaf3798CoversExact : CoversExact 8
    leaf3798Box leaf3798Certificate leaf3798InnerLog leaf3798Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk80RoundedFacts chi65RoundedFacts
    innerPair110RoundedFacts leaf3798RoundedFacts (by rfl)

private theorem leaf3798FlatSound : Sound leaf3798Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3798CertificateValid
    leaf3798InnerLogValid leaf3798CoversExact leaf3798LowerChecked

private noncomputable def leaf3799Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (77/32), chiLo := (3/8), chiHi := (25/64) }

private noncomputable def leaf3799Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217931/134217728) }, vSqrt := { lower := (65531/65536), upper := (22906164565/22905178112) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (253715127/134217728) }, upper := { exponent := 0, mantissa := (3973/2048) } }, logOuter := sk81LogOuterCertificate, logK := sk81LogKCertificate, logChi := chi62LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (45811342677/45810356224) } }, logDArg := sk81LogDArgCertificate }

private noncomputable def leaf3799InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf3799LocalValidity :
    LeafFacts leaf3799Box leaf3799Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3799Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (22906164565/22905178112) }) = true
      norm_num [leaf3799Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3799CertificateValid :
    WideCertificateValid leaf3799Box leaf3799Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk81ValidityFacts chi62ValidityFacts
    leaf3799LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3799CoverageChecked :
    coverageCheck (innerAD leaf3799Box) leaf3799InnerLog = true := by
  rfl'

private theorem leaf3799InnerLogValid :
    leaf3799InnerLog.Valid 8 (innerAD leaf3799Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf3799CoverageChecked

private noncomputable def leaf3799InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814721/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3799InputLogOnePlusV_eq :
    leaf3799InputLogOnePlusV = outerEnclosure 24
      (leaf3799Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3799RoundedFacts : LeafRoundedFacts 8
    leaf3799Certificate.logOnePlusV leaf3799InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3799InputLogOnePlusV_eq }

private noncomputable def leaf3799Inputs : Inputs :=
  inputsOfCaches globalInput sk81RoundedInputs
    chi62InputQChi innerPair101Input
    leaf3799InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3799LowerChecked :
    lowerCheck 24 leaf3799Box leaf3799Inputs = true := by
  rfl'

private theorem leaf3799CoversExact : CoversExact 8
    leaf3799Box leaf3799Certificate leaf3799InnerLog leaf3799Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk81RoundedFacts chi62RoundedFacts
    innerPair101RoundedFacts leaf3799RoundedFacts (by rfl)

private theorem leaf3799FlatSound : Sound leaf3799Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3799CertificateValid
    leaf3799InnerLogValid leaf3799CoversExact leaf3799LowerChecked

private noncomputable def leaf3800Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (77/32), kHi := (39/16), chiLo := (3/8), chiHi := (25/64) }

private noncomputable def leaf3800Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217933/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68715483136) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (255287893/134217728) }, upper := { exponent := 0, mantissa := (1999/1024) } }, logOuter := sk82LogOuterCertificate, logK := sk82LogKCertificate, logChi := chi62LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137433976831/137430966272) } }, logDArg := sk82LogDArgCertificate }

private noncomputable def leaf3800InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf3800LocalValidity :
    LeafFacts leaf3800Box leaf3800Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3800Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68715483136) }) = true
      norm_num [leaf3800Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3800CertificateValid :
    WideCertificateValid leaf3800Box leaf3800Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk82ValidityFacts chi62ValidityFacts
    leaf3800LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3800CoverageChecked :
    coverageCheck (innerAD leaf3800Box) leaf3800InnerLog = true := by
  rfl'

private theorem leaf3800InnerLogValid :
    leaf3800InnerLog.Valid 8 (innerAD leaf3800Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf3800CoverageChecked

private noncomputable def leaf3800InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (1453681/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3800InputLogOnePlusV_eq :
    leaf3800InputLogOnePlusV = outerEnclosure 24
      (leaf3800Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3800RoundedFacts : LeafRoundedFacts 8
    leaf3800Certificate.logOnePlusV leaf3800InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3800InputLogOnePlusV_eq }

private noncomputable def leaf3800Inputs : Inputs :=
  inputsOfCaches globalInput sk82RoundedInputs
    chi62InputQChi innerPair101Input
    leaf3800InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3800LowerChecked :
    lowerCheck 24 leaf3800Box leaf3800Inputs = true := by
  rfl'

private theorem leaf3800CoversExact : CoversExact 8
    leaf3800Box leaf3800Certificate leaf3800InnerLog leaf3800Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk82RoundedFacts chi62RoundedFacts
    innerPair101RoundedFacts leaf3800RoundedFacts (by rfl)

private theorem leaf3800FlatSound : Sound leaf3800Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3800CertificateValid
    leaf3800InnerLogValid leaf3800CoversExact leaf3800LowerChecked

private noncomputable def leaf3801Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (77/32), chiLo := (25/64), chiHi := (13/32) }

private noncomputable def leaf3801Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217933/134217728) }, vSqrt := { lower := (65531/65536), upper := (13743698739/13743075328) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (258695557/134217728) }, upper := { exponent := 0, mantissa := (2025/1024) } }, logOuter := sk81LogOuterCertificate, logK := sk81LogKCertificate, logChi := chi63LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (27486774067/27486150656) } }, logDArg := sk81LogDArgCertificate }

private noncomputable def leaf3801InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf3801LocalValidity :
    LeafFacts leaf3801Box leaf3801Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3801Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (13743698739/13743075328) }) = true
      norm_num [leaf3801Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3801CertificateValid :
    WideCertificateValid leaf3801Box leaf3801Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk81ValidityFacts chi63ValidityFacts
    leaf3801LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3801CoverageChecked :
    coverageCheck (innerAD leaf3801Box) leaf3801InnerLog = true := by
  rfl'

private theorem leaf3801InnerLogValid :
    leaf3801InnerLog.Valid 8 (innerAD leaf3801Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf3801CoverageChecked

private noncomputable def leaf3801InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629461/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3801InputLogOnePlusV_eq :
    leaf3801InputLogOnePlusV = outerEnclosure 24
      (leaf3801Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3801RoundedFacts : LeafRoundedFacts 8
    leaf3801Certificate.logOnePlusV leaf3801InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3801InputLogOnePlusV_eq }

private noncomputable def leaf3801Inputs : Inputs :=
  inputsOfCaches globalInput sk81RoundedInputs
    chi63InputQChi innerPair101Input
    leaf3801InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3801LowerChecked :
    lowerCheck 24 leaf3801Box leaf3801Inputs = true := by
  rfl'

private theorem leaf3801CoversExact : CoversExact 8
    leaf3801Box leaf3801Certificate leaf3801InnerLog leaf3801Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk81RoundedFacts chi63RoundedFacts
    innerPair101RoundedFacts leaf3801RoundedFacts (by rfl)

private theorem leaf3801FlatSound : Sound leaf3801Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3801CertificateValid
    leaf3801InnerLogValid leaf3801CoversExact leaf3801LowerChecked

private noncomputable def leaf3802Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (77/32), kHi := (39/16), chiLo := (25/64), chiHi := (13/32) }

private noncomputable def leaf3802Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217935/134217728) }, vSqrt := { lower := (65531/65536), upper := (34358722559/34357661696) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (260333855/134217728) }, upper := { exponent := 0, mantissa := (1019/512) } }, logOuter := sk82LogOuterCertificate, logK := sk82LogKCertificate, logChi := chi63LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68716384255/68715323392) } }, logDArg := sk82LogDArgCertificate }

private noncomputable def leaf3802InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf3802LocalValidity :
    LeafFacts leaf3802Box leaf3802Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3802Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358722559/34357661696) }) = true
      norm_num [leaf3802Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3802CertificateValid :
    WideCertificateValid leaf3802Box leaf3802Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk82ValidityFacts chi63ValidityFacts
    leaf3802LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3802CoverageChecked :
    coverageCheck (innerAD leaf3802Box) leaf3802InnerLog = true := by
  rfl'

private theorem leaf3802InnerLogValid :
    leaf3802InnerLog.Valid 8 (innerAD leaf3802Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf3802CoverageChecked

private noncomputable def leaf3802InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907335/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3802InputLogOnePlusV_eq :
    leaf3802InputLogOnePlusV = outerEnclosure 24
      (leaf3802Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3802RoundedFacts : LeafRoundedFacts 8
    leaf3802Certificate.logOnePlusV leaf3802InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3802InputLogOnePlusV_eq }

private noncomputable def leaf3802Inputs : Inputs :=
  inputsOfCaches globalInput sk82RoundedInputs
    chi63InputQChi innerPair108Input
    leaf3802InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3802LowerChecked :
    lowerCheck 24 leaf3802Box leaf3802Inputs = true := by
  rfl'

private theorem leaf3802CoversExact : CoversExact 8
    leaf3802Box leaf3802Certificate leaf3802InnerLog leaf3802Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk82RoundedFacts chi63RoundedFacts
    innerPair108RoundedFacts leaf3802RoundedFacts (by rfl)

private theorem leaf3802FlatSound : Sound leaf3802Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3802CertificateValid
    leaf3802InnerLogValid leaf3802CoversExact leaf3802LowerChecked

private noncomputable def leaf3803Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (79/32), chiLo := (3/8), chiHi := (25/64) }

private noncomputable def leaf3803Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217935/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68715431936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (256860659/134217728) }, upper := { exponent := 0, mantissa := (4023/2048) } }, logOuter := sk83LogOuterCertificate, logK := sk83LogKCertificate, logChi := chi62LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137433925631/137430863872) } }, logDArg := sk83LogDArgCertificate }

private noncomputable def leaf3803InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf3803LocalValidity :
    LeafFacts leaf3803Box leaf3803Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3803Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68715431936) }) = true
      norm_num [leaf3803Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3803CertificateValid :
    WideCertificateValid leaf3803Box leaf3803Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk83ValidityFacts chi62ValidityFacts
    leaf3803LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3803CoverageChecked :
    coverageCheck (innerAD leaf3803Box) leaf3803InnerLog = true := by
  rfl'

private theorem leaf3803InnerLogValid :
    leaf3803InnerLog.Valid 8 (innerAD leaf3803Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf3803CoverageChecked

private noncomputable def leaf3803InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629455/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3803InputLogOnePlusV_eq :
    leaf3803InputLogOnePlusV = outerEnclosure 24
      (leaf3803Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3803RoundedFacts : LeafRoundedFacts 8
    leaf3803Certificate.logOnePlusV leaf3803InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3803InputLogOnePlusV_eq }

private noncomputable def leaf3803Inputs : Inputs :=
  inputsOfCaches globalInput sk83RoundedInputs
    chi62InputQChi innerPair101Input
    leaf3803InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3803LowerChecked :
    lowerCheck 24 leaf3803Box leaf3803Inputs = true := by
  rfl'

private theorem leaf3803CoversExact : CoversExact 8
    leaf3803Box leaf3803Certificate leaf3803InnerLog leaf3803Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk83RoundedFacts chi62RoundedFacts
    innerPair101RoundedFacts leaf3803RoundedFacts (by rfl)

private theorem leaf3803FlatSound : Sound leaf3803Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3803CertificateValid
    leaf3803InnerLogValid leaf3803CoversExact leaf3803LowerChecked

private noncomputable def leaf3804Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (79/32), kHi := (5/2), chiLo := (3/8), chiHi := (25/64) }

private noncomputable def leaf3804Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217937/134217728) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905126912) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (258433425/134217728) }, upper := { exponent := 0, mantissa := (253/128) } }, logOuter := sk84LogOuterCertificate, logK := sk84LogKCertificate, logChi := chi62LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811291477/45810253824) } }, logDArg := sk84LogDArgCertificate }

private noncomputable def leaf3804InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf3804LocalValidity :
    LeafFacts leaf3804Box leaf3804Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3804Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905126912) }) = true
      norm_num [leaf3804Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3804CertificateValid :
    WideCertificateValid leaf3804Box leaf3804Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk84ValidityFacts chi62ValidityFacts
    leaf3804LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3804CoverageChecked :
    coverageCheck (innerAD leaf3804Box) leaf3804InnerLog = true := by
  rfl'

private theorem leaf3804InnerLogValid :
    leaf3804InnerLog.Valid 8 (innerAD leaf3804Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf3804CoverageChecked

private noncomputable def leaf3804InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629461/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3804InputLogOnePlusV_eq :
    leaf3804InputLogOnePlusV = outerEnclosure 24
      (leaf3804Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3804RoundedFacts : LeafRoundedFacts 8
    leaf3804Certificate.logOnePlusV leaf3804InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3804InputLogOnePlusV_eq }

private noncomputable def leaf3804Inputs : Inputs :=
  inputsOfCaches globalInput sk84RoundedInputs
    chi62InputQChi innerPair101Input
    leaf3804InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3804LowerChecked :
    lowerCheck 24 leaf3804Box leaf3804Inputs = true := by
  rfl'

private theorem leaf3804CoversExact : CoversExact 8
    leaf3804Box leaf3804Certificate leaf3804InnerLog leaf3804Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk84RoundedFacts chi62RoundedFacts
    innerPair101RoundedFacts leaf3804RoundedFacts (by rfl)

private theorem leaf3804FlatSound : Sound leaf3804Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3804CertificateValid
    leaf3804InnerLogValid leaf3804CoversExact leaf3804LowerChecked

private noncomputable def leaf3805Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (79/32), chiLo := (25/64), chiHi := (13/32) }

private noncomputable def leaf3805Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217937/134217728) }, vSqrt := { lower := (65531/65536), upper := (34358722559/34357635072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (261972153/134217728) }, upper := { exponent := 1, mantissa := (2051/2048) } }, logOuter := sk83LogOuterCertificate, logK := sk83LogKCertificate, logChi := chi63LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68716357631/68715270144) } }, logDArg := sk83LogDArgCertificate }

private noncomputable def leaf3805InnerLog : WideLogData :=
  innerPair110Data

set_option maxRecDepth 1000000 in
private theorem leaf3805LocalValidity :
    LeafFacts leaf3805Box leaf3805Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3805Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358722559/34357635072) }) = true
      norm_num [leaf3805Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3805CertificateValid :
    WideCertificateValid leaf3805Box leaf3805Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk83ValidityFacts chi63ValidityFacts
    leaf3805LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3805CoverageChecked :
    coverageCheck (innerAD leaf3805Box) leaf3805InnerLog = true := by
  rfl'

private theorem leaf3805InnerLogValid :
    leaf3805InnerLog.Valid 8 (innerAD leaf3805Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint72PositiveFacts.valid leaf3805CoverageChecked

private noncomputable def leaf3805InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814673/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3805InputLogOnePlusV_eq :
    leaf3805InputLogOnePlusV = outerEnclosure 24
      (leaf3805Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3805RoundedFacts : LeafRoundedFacts 8
    leaf3805Certificate.logOnePlusV leaf3805InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3805InputLogOnePlusV_eq }

private noncomputable def leaf3805Inputs : Inputs :=
  inputsOfCaches globalInput sk83RoundedInputs
    chi63InputQChi innerPair110Input
    leaf3805InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3805LowerChecked :
    lowerCheck 24 leaf3805Box leaf3805Inputs = true := by
  rfl'

private theorem leaf3805CoversExact : CoversExact 8
    leaf3805Box leaf3805Certificate leaf3805InnerLog leaf3805Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk83RoundedFacts chi63RoundedFacts
    innerPair110RoundedFacts leaf3805RoundedFacts (by rfl)

private theorem leaf3805FlatSound : Sound leaf3805Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3805CertificateValid
    leaf3805InnerLogValid leaf3805CoversExact leaf3805LowerChecked

private noncomputable def leaf3806Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (79/32), kHi := (5/2), chiLo := (25/64), chiHi := (13/32) }

private noncomputable def leaf3806Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217939/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357608448) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (263610451/134217728) }, upper := { exponent := 1, mantissa := (129/128) } }, logOuter := sk84LogOuterCertificate, logK := sk84LogKCertificate, logChi := chi63LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716331007/68715216896) } }, logDArg := sk84LogDArgCertificate }

private noncomputable def leaf3806InnerLog : WideLogData :=
  innerPair110Data

set_option maxRecDepth 1000000 in
private theorem leaf3806LocalValidity :
    LeafFacts leaf3806Box leaf3806Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3806Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357608448) }) = true
      norm_num [leaf3806Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3806CertificateValid :
    WideCertificateValid leaf3806Box leaf3806Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk84ValidityFacts chi63ValidityFacts
    leaf3806LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3806CoverageChecked :
    coverageCheck (innerAD leaf3806Box) leaf3806InnerLog = true := by
  rfl'

private theorem leaf3806InnerLogValid :
    leaf3806InnerLog.Valid 8 (innerAD leaf3806Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint72PositiveFacts.valid leaf3806CoverageChecked

private noncomputable def leaf3806InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629353/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3806InputLogOnePlusV_eq :
    leaf3806InputLogOnePlusV = outerEnclosure 24
      (leaf3806Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3806RoundedFacts : LeafRoundedFacts 8
    leaf3806Certificate.logOnePlusV leaf3806InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3806InputLogOnePlusV_eq }

private noncomputable def leaf3806Inputs : Inputs :=
  inputsOfCaches globalInput sk84RoundedInputs
    chi63InputQChi innerPair110Input
    leaf3806InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3806LowerChecked :
    lowerCheck 24 leaf3806Box leaf3806Inputs = true := by
  rfl'

private theorem leaf3806CoversExact : CoversExact 8
    leaf3806Box leaf3806Certificate leaf3806InnerLog leaf3806Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk84RoundedFacts chi63RoundedFacts
    innerPair110RoundedFacts leaf3806RoundedFacts (by rfl)

private theorem leaf3806FlatSound : Sound leaf3806Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3806CertificateValid
    leaf3806InnerLogValid leaf3806CoversExact leaf3806LowerChecked

private noncomputable def leaf3807Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (77/32), chiLo := (13/32), chiHi := (27/64) }

private noncomputable def leaf3807Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217935/134217728) }, vSqrt := { lower := (65531/65536), upper := (34358722559/34357609472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (263675987/134217728) }, upper := { exponent := 1, mantissa := (4127/4096) } }, logOuter := sk81LogOuterCertificate, logK := sk81LogKCertificate, logChi := chi64LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68716332031/68715218944) } }, logDArg := sk81LogDArgCertificate }

private noncomputable def leaf3807InnerLog : WideLogData :=
  innerPair110Data

set_option maxRecDepth 1000000 in
private theorem leaf3807LocalValidity :
    LeafFacts leaf3807Box leaf3807Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3807Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358722559/34357609472) }) = true
      norm_num [leaf3807Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3807CertificateValid :
    WideCertificateValid leaf3807Box leaf3807Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk81ValidityFacts chi64ValidityFacts
    leaf3807LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3807CoverageChecked :
    coverageCheck (innerAD leaf3807Box) leaf3807InnerLog = true := by
  rfl'

private theorem leaf3807InnerLogValid :
    leaf3807InnerLog.Valid 8 (innerAD leaf3807Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint72PositiveFacts.valid leaf3807CoverageChecked

private noncomputable def leaf3807InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629353/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3807InputLogOnePlusV_eq :
    leaf3807InputLogOnePlusV = outerEnclosure 24
      (leaf3807Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3807RoundedFacts : LeafRoundedFacts 8
    leaf3807Certificate.logOnePlusV leaf3807InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3807InputLogOnePlusV_eq }

private noncomputable def leaf3807Inputs : Inputs :=
  inputsOfCaches globalInput sk81RoundedInputs
    chi64InputQChi innerPair110Input
    leaf3807InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3807LowerChecked :
    lowerCheck 24 leaf3807Box leaf3807Inputs = true := by
  rfl'

private theorem leaf3807CoversExact : CoversExact 8
    leaf3807Box leaf3807Certificate leaf3807InnerLog leaf3807Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk81RoundedFacts chi64RoundedFacts
    innerPair110RoundedFacts leaf3807RoundedFacts (by rfl)

private theorem leaf3807FlatSound : Sound leaf3807Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3807CertificateValid
    leaf3807InnerLogValid leaf3807CoversExact leaf3807LowerChecked

private noncomputable def leaf3808Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (77/32), kHi := (39/16), chiLo := (13/32), chiHi := (27/64) }

private noncomputable def leaf3808Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217937/134217728) }, vSqrt := { lower := (65531/65536), upper := (34358722559/34357581824) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (265379817/134217728) }, upper := { exponent := 1, mantissa := (2077/2048) } }, logOuter := sk82LogOuterCertificate, logK := sk82LogKCertificate, logChi := chi64LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68716304383/68715163648) } }, logDArg := sk82LogDArgCertificate }

private noncomputable def leaf3808InnerLog : WideLogData :=
  innerPair110Data

set_option maxRecDepth 1000000 in
private theorem leaf3808LocalValidity :
    LeafFacts leaf3808Box leaf3808Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3808Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358722559/34357581824) }) = true
      norm_num [leaf3808Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3808CertificateValid :
    WideCertificateValid leaf3808Box leaf3808Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk82ValidityFacts chi64ValidityFacts
    leaf3808LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3808CoverageChecked :
    coverageCheck (innerAD leaf3808Box) leaf3808InnerLog = true := by
  rfl'

private theorem leaf3808InnerLogValid :
    leaf3808InnerLog.Valid 8 (innerAD leaf3808Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint72PositiveFacts.valid leaf3808CoverageChecked

private noncomputable def leaf3808InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629359/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3808InputLogOnePlusV_eq :
    leaf3808InputLogOnePlusV = outerEnclosure 24
      (leaf3808Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3808RoundedFacts : LeafRoundedFacts 8
    leaf3808Certificate.logOnePlusV leaf3808InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3808InputLogOnePlusV_eq }

private noncomputable def leaf3808Inputs : Inputs :=
  inputsOfCaches globalInput sk82RoundedInputs
    chi64InputQChi innerPair110Input
    leaf3808InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3808LowerChecked :
    lowerCheck 24 leaf3808Box leaf3808Inputs = true := by
  rfl'

private theorem leaf3808CoversExact : CoversExact 8
    leaf3808Box leaf3808Certificate leaf3808InnerLog leaf3808Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk82RoundedFacts chi64RoundedFacts
    innerPair110RoundedFacts leaf3808RoundedFacts (by rfl)

private theorem leaf3808FlatSound : Sound leaf3808Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3808CertificateValid
    leaf3808InnerLogValid leaf3808CoversExact leaf3808LowerChecked

private noncomputable def leaf3809Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (77/32), chiLo := (27/64), chiHi := (7/16) }

private noncomputable def leaf3809Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217937/134217728) }, vSqrt := { lower := (65531/65536), upper := (34358722559/34357530624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (268656417/268435456) }, upper := { exponent := 1, mantissa := (1051/1024) } }, logOuter := sk81LogOuterCertificate, logK := sk81LogKCertificate, logChi := chi65LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68716253183/68715061248) } }, logDArg := sk81LogDArgCertificate }

private noncomputable def leaf3809InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf3809LocalValidity :
    LeafFacts leaf3809Box leaf3809Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3809Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358722559/34357530624) }) = true
      norm_num [leaf3809Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3809CertificateValid :
    WideCertificateValid leaf3809Box leaf3809Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk81ValidityFacts chi65ValidityFacts
    leaf3809LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3809CoverageChecked :
    coverageCheck (innerAD leaf3809Box) leaf3809InnerLog = true := by
  rfl'

private theorem leaf3809InnerLogValid :
    leaf3809InnerLog.Valid 8 (innerAD leaf3809Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf3809CoverageChecked

private noncomputable def leaf3809InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907343/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3809InputLogOnePlusV_eq :
    leaf3809InputLogOnePlusV = outerEnclosure 24
      (leaf3809Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3809RoundedFacts : LeafRoundedFacts 8
    leaf3809Certificate.logOnePlusV leaf3809InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3809InputLogOnePlusV_eq }

private noncomputable def leaf3809Inputs : Inputs :=
  inputsOfCaches globalInput sk81RoundedInputs
    chi65InputQChi innerPair116Input
    leaf3809InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3809LowerChecked :
    lowerCheck 24 leaf3809Box leaf3809Inputs = true := by
  rfl'

private theorem leaf3809CoversExact : CoversExact 8
    leaf3809Box leaf3809Certificate leaf3809InnerLog leaf3809Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk81RoundedFacts chi65RoundedFacts
    innerPair116RoundedFacts leaf3809RoundedFacts (by rfl)

private theorem leaf3809FlatSound : Sound leaf3809Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3809CertificateValid
    leaf3809InnerLogValid leaf3809CoversExact leaf3809LowerChecked

private noncomputable def leaf3810Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (77/32), kHi := (39/16), chiLo := (27/64), chiHi := (7/16) }

private noncomputable def leaf3810Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217939/134217728) }, vSqrt := { lower := (65531/65536), upper := (34358722559/34357501952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (270425779/268435456) }, upper := { exponent := 1, mantissa := (529/512) } }, logOuter := sk82LogOuterCertificate, logK := sk82LogKCertificate, logChi := chi65LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68716224511/68715003904) } }, logDArg := sk82LogDArgCertificate }

private noncomputable def leaf3810InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf3810LocalValidity :
    LeafFacts leaf3810Box leaf3810Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3810Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358722559/34357501952) }) = true
      norm_num [leaf3810Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3810CertificateValid :
    WideCertificateValid leaf3810Box leaf3810Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk82ValidityFacts chi65ValidityFacts
    leaf3810LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3810CoverageChecked :
    coverageCheck (innerAD leaf3810Box) leaf3810InnerLog = true := by
  rfl'

private theorem leaf3810InnerLogValid :
    leaf3810InnerLog.Valid 8 (innerAD leaf3810Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf3810CoverageChecked

private noncomputable def leaf3810InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629379/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3810InputLogOnePlusV_eq :
    leaf3810InputLogOnePlusV = outerEnclosure 24
      (leaf3810Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3810RoundedFacts : LeafRoundedFacts 8
    leaf3810Certificate.logOnePlusV leaf3810InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3810InputLogOnePlusV_eq }

private noncomputable def leaf3810Inputs : Inputs :=
  inputsOfCaches globalInput sk82RoundedInputs
    chi65InputQChi innerPair117Input
    leaf3810InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3810LowerChecked :
    lowerCheck 24 leaf3810Box leaf3810Inputs = true := by
  rfl'

private theorem leaf3810CoversExact : CoversExact 8
    leaf3810Box leaf3810Certificate leaf3810InnerLog leaf3810Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk82RoundedFacts chi65RoundedFacts
    innerPair117RoundedFacts leaf3810RoundedFacts (by rfl)

private theorem leaf3810FlatSound : Sound leaf3810Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3810CertificateValid
    leaf3810InnerLogValid leaf3810CoversExact leaf3810LowerChecked

private noncomputable def leaf3811Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (79/32), chiLo := (13/32), chiHi := (27/64) }

private noncomputable def leaf3811Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217939/134217728) }, vSqrt := { lower := (65531/65536), upper := (34358722559/34357554176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (267083647/134217728) }, upper := { exponent := 1, mantissa := (4181/4096) } }, logOuter := sk83LogOuterCertificate, logK := sk83LogKCertificate, logChi := chi64LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68716276735/68715108352) } }, logDArg := sk83LogDArgCertificate }

private noncomputable def leaf3811InnerLog : WideLogData :=
  innerPair110Data

set_option maxRecDepth 1000000 in
private theorem leaf3811LocalValidity :
    LeafFacts leaf3811Box leaf3811Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3811Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358722559/34357554176) }) = true
      norm_num [leaf3811Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3811CertificateValid :
    WideCertificateValid leaf3811Box leaf3811Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk83ValidityFacts chi64ValidityFacts
    leaf3811LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3811CoverageChecked :
    coverageCheck (innerAD leaf3811Box) leaf3811InnerLog = true := by
  rfl'

private theorem leaf3811InnerLogValid :
    leaf3811InnerLog.Valid 8 (innerAD leaf3811Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint72PositiveFacts.valid leaf3811CoverageChecked

private noncomputable def leaf3811InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814683/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3811InputLogOnePlusV_eq :
    leaf3811InputLogOnePlusV = outerEnclosure 24
      (leaf3811Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3811RoundedFacts : LeafRoundedFacts 8
    leaf3811Certificate.logOnePlusV leaf3811InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3811InputLogOnePlusV_eq }

private noncomputable def leaf3811Inputs : Inputs :=
  inputsOfCaches globalInput sk83RoundedInputs
    chi64InputQChi innerPair110Input
    leaf3811InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3811LowerChecked :
    lowerCheck 24 leaf3811Box leaf3811Inputs = true := by
  rfl'

private theorem leaf3811CoversExact : CoversExact 8
    leaf3811Box leaf3811Certificate leaf3811InnerLog leaf3811Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk83RoundedFacts chi64RoundedFacts
    innerPair110RoundedFacts leaf3811RoundedFacts (by rfl)

private theorem leaf3811FlatSound : Sound leaf3811Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3811CertificateValid
    leaf3811InnerLogValid leaf3811CoversExact leaf3811LowerChecked

private noncomputable def leaf3812Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (79/32), kHi := (5/2), chiLo := (13/32), chiHi := (27/64) }

private noncomputable def leaf3812Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217941/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357526528) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (268787477/268435456) }, upper := { exponent := 1, mantissa := (263/256) } }, logOuter := sk84LogOuterCertificate, logK := sk84LogKCertificate, logChi := chi64LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716249087/68715053056) } }, logDArg := sk84LogDArgCertificate }

private noncomputable def leaf3812InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf3812LocalValidity :
    LeafFacts leaf3812Box leaf3812Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3812Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357526528) }) = true
      norm_num [leaf3812Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3812CertificateValid :
    WideCertificateValid leaf3812Box leaf3812Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk84ValidityFacts chi64ValidityFacts
    leaf3812LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3812CoverageChecked :
    coverageCheck (innerAD leaf3812Box) leaf3812InnerLog = true := by
  rfl'

private theorem leaf3812InnerLogValid :
    leaf3812InnerLog.Valid 8 (innerAD leaf3812Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf3812CoverageChecked

private noncomputable def leaf3812InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629373/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3812InputLogOnePlusV_eq :
    leaf3812InputLogOnePlusV = outerEnclosure 24
      (leaf3812Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3812RoundedFacts : LeafRoundedFacts 8
    leaf3812Certificate.logOnePlusV leaf3812InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3812InputLogOnePlusV_eq }

private noncomputable def leaf3812Inputs : Inputs :=
  inputsOfCaches globalInput sk84RoundedInputs
    chi64InputQChi innerPair116Input
    leaf3812InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3812LowerChecked :
    lowerCheck 24 leaf3812Box leaf3812Inputs = true := by
  rfl'

private theorem leaf3812CoversExact : CoversExact 8
    leaf3812Box leaf3812Certificate leaf3812InnerLog leaf3812Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk84RoundedFacts chi64RoundedFacts
    innerPair116RoundedFacts leaf3812RoundedFacts (by rfl)

private theorem leaf3812FlatSound : Sound leaf3812Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3812CertificateValid
    leaf3812InnerLogValid leaf3812CoversExact leaf3812LowerChecked

private noncomputable def leaf3813Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (79/32), chiLo := (27/64), chiHi := (7/16) }

private noncomputable def leaf3813Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217941/134217728) }, vSqrt := { lower := (65531/65536), upper := (2021101327/2021027840) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (272195141/268435456) }, upper := { exponent := 1, mantissa := (1065/1024) } }, logOuter := sk83LogOuterCertificate, logK := sk83LogKCertificate, logChi := chi65LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (4042129167/4042055680) } }, logDArg := sk83LogDArgCertificate }

private noncomputable def leaf3813InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf3813LocalValidity :
    LeafFacts leaf3813Box leaf3813Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3813Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (2021101327/2021027840) }) = true
      norm_num [leaf3813Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3813CertificateValid :
    WideCertificateValid leaf3813Box leaf3813Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk83ValidityFacts chi65ValidityFacts
    leaf3813LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3813CoverageChecked :
    coverageCheck (innerAD leaf3813Box) leaf3813InnerLog = true := by
  rfl'

private theorem leaf3813InnerLogValid :
    leaf3813InnerLog.Valid 8 (innerAD leaf3813Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf3813CoverageChecked

private noncomputable def leaf3813InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814693/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3813InputLogOnePlusV_eq :
    leaf3813InputLogOnePlusV = outerEnclosure 24
      (leaf3813Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3813RoundedFacts : LeafRoundedFacts 8
    leaf3813Certificate.logOnePlusV leaf3813InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3813InputLogOnePlusV_eq }

private noncomputable def leaf3813Inputs : Inputs :=
  inputsOfCaches globalInput sk83RoundedInputs
    chi65InputQChi innerPair117Input
    leaf3813InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3813LowerChecked :
    lowerCheck 24 leaf3813Box leaf3813Inputs = true := by
  rfl'

private theorem leaf3813CoversExact : CoversExact 8
    leaf3813Box leaf3813Certificate leaf3813InnerLog leaf3813Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk83RoundedFacts chi65RoundedFacts
    innerPair117RoundedFacts leaf3813RoundedFacts (by rfl)

private theorem leaf3813FlatSound : Sound leaf3813Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3813CertificateValid
    leaf3813InnerLogValid leaf3813CoversExact leaf3813LowerChecked

private noncomputable def leaf3814Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (79/32), kHi := (5/2), chiLo := (27/64), chiHi := (7/16) }

private noncomputable def leaf3814Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217943/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357444608) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (273964503/268435456) }, upper := { exponent := 1, mantissa := (67/64) } }, logOuter := sk84LogOuterCertificate, logK := sk84LogKCertificate, logChi := chi65LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716167167/68714889216) } }, logDArg := sk84LogDArgCertificate }

private noncomputable def leaf3814InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf3814LocalValidity :
    LeafFacts leaf3814Box leaf3814Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3814Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357444608) }) = true
      norm_num [leaf3814Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3814CertificateValid :
    WideCertificateValid leaf3814Box leaf3814Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk84ValidityFacts chi65ValidityFacts
    leaf3814LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3814CoverageChecked :
    coverageCheck (innerAD leaf3814Box) leaf3814InnerLog = true := by
  rfl'

private theorem leaf3814InnerLogValid :
    leaf3814InnerLog.Valid 8 (innerAD leaf3814Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf3814CoverageChecked

private noncomputable def leaf3814InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629393/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3814InputLogOnePlusV_eq :
    leaf3814InputLogOnePlusV = outerEnclosure 24
      (leaf3814Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3814RoundedFacts : LeafRoundedFacts 8
    leaf3814Certificate.logOnePlusV leaf3814InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3814InputLogOnePlusV_eq }

private noncomputable def leaf3814Inputs : Inputs :=
  inputsOfCaches globalInput sk84RoundedInputs
    chi65InputQChi innerPair117Input
    leaf3814InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3814LowerChecked :
    lowerCheck 24 leaf3814Box leaf3814Inputs = true := by
  rfl'

private theorem leaf3814CoversExact : CoversExact 8
    leaf3814Box leaf3814Certificate leaf3814InnerLog leaf3814Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk84RoundedFacts chi65RoundedFacts
    innerPair117RoundedFacts leaf3814RoundedFacts (by rfl)

private theorem leaf3814FlatSound : Sound leaf3814Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3814CertificateValid
    leaf3814InnerLogValid leaf3814CoversExact leaf3814LowerChecked

private noncomputable def leaf3815Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (73/32), chiLo := (7/16), chiHi := (29/64) }

private noncomputable def leaf3815Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217931/134217728) }, vSqrt := { lower := (65531/65536), upper := (34358722559/34357570560) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (266297271/134217728) }, upper := { exponent := 1, mantissa := (4165/4096) } }, logOuter := sk85LogOuterCertificate, logK := sk85LogKCertificate, logChi := chi66LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68716293119/68715141120) } }, logDArg := sk85LogDArgCertificate }

private noncomputable def leaf3815InnerLog : WideLogData :=
  innerPair110Data

set_option maxRecDepth 1000000 in
private theorem leaf3815LocalValidity :
    LeafFacts leaf3815Box leaf3815Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3815Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358722559/34357570560) }) = true
      norm_num [leaf3815Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3815CertificateValid :
    WideCertificateValid leaf3815Box leaf3815Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk85ValidityFacts chi66ValidityFacts
    leaf3815LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3815CoverageChecked :
    coverageCheck (innerAD leaf3815Box) leaf3815InnerLog = true := by
  rfl'

private theorem leaf3815InnerLogValid :
    leaf3815InnerLog.Valid 8 (innerAD leaf3815Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint72PositiveFacts.valid leaf3815CoverageChecked

private noncomputable def leaf3815InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814681/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3815InputLogOnePlusV_eq :
    leaf3815InputLogOnePlusV = outerEnclosure 24
      (leaf3815Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3815RoundedFacts : LeafRoundedFacts 8
    leaf3815Certificate.logOnePlusV leaf3815InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3815InputLogOnePlusV_eq }

private noncomputable def leaf3815Inputs : Inputs :=
  inputsOfCaches globalInput sk85RoundedInputs
    chi66InputQChi innerPair110Input
    leaf3815InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3815LowerChecked :
    lowerCheck 24 leaf3815Box leaf3815Inputs = true := by
  rfl'

private theorem leaf3815CoversExact : CoversExact 8
    leaf3815Box leaf3815Certificate leaf3815InnerLog leaf3815Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk85RoundedFacts chi66RoundedFacts
    innerPair110RoundedFacts leaf3815RoundedFacts (by rfl)

private theorem leaf3815FlatSound : Sound leaf3815Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3815CertificateValid
    leaf3815InnerLogValid leaf3815CoversExact leaf3815LowerChecked

private noncomputable def leaf3816Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (73/32), kHi := (37/16), chiLo := (7/16), chiHi := (29/64) }

private noncomputable def leaf3816Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217933/134217728) }, vSqrt := { lower := (65531/65536), upper := (34358722559/34357540864) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (268132165/134217728) }, upper := { exponent := 1, mantissa := (2097/2048) } }, logOuter := sk86LogOuterCertificate, logK := sk86LogKCertificate, logChi := chi66LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68716263423/68715081728) } }, logDArg := sk86LogDArgCertificate }

private noncomputable def leaf3816InnerLog : WideLogData :=
  innerPair110Data

set_option maxRecDepth 1000000 in
private theorem leaf3816LocalValidity :
    LeafFacts leaf3816Box leaf3816Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3816Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358722559/34357540864) }) = true
      norm_num [leaf3816Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3816CertificateValid :
    WideCertificateValid leaf3816Box leaf3816Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk86ValidityFacts chi66ValidityFacts
    leaf3816LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3816CoverageChecked :
    coverageCheck (innerAD leaf3816Box) leaf3816InnerLog = true := by
  rfl'

private theorem leaf3816InnerLogValid :
    leaf3816InnerLog.Valid 8 (innerAD leaf3816Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint72PositiveFacts.valid leaf3816CoverageChecked

private noncomputable def leaf3816InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629369/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3816InputLogOnePlusV_eq :
    leaf3816InputLogOnePlusV = outerEnclosure 24
      (leaf3816Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3816RoundedFacts : LeafRoundedFacts 8
    leaf3816Certificate.logOnePlusV leaf3816InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3816InputLogOnePlusV_eq }

private noncomputable def leaf3816Inputs : Inputs :=
  inputsOfCaches globalInput sk86RoundedInputs
    chi66InputQChi innerPair110Input
    leaf3816InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3816LowerChecked :
    lowerCheck 24 leaf3816Box leaf3816Inputs = true := by
  rfl'

private theorem leaf3816CoversExact : CoversExact 8
    leaf3816Box leaf3816Certificate leaf3816InnerLog leaf3816Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk86RoundedFacts chi66RoundedFacts
    innerPair110RoundedFacts leaf3816RoundedFacts (by rfl)

private theorem leaf3816FlatSound : Sound leaf3816Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3816CertificateValid
    leaf3816InnerLogValid leaf3816CoversExact leaf3816LowerChecked

private noncomputable def leaf3817Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (73/32), chiLo := (29/64), chiHi := (15/32) }

private noncomputable def leaf3817Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217933/134217728) }, vSqrt := { lower := (65531/65536), upper := (34358722559/34357495808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (271015573/268435456) }, upper := { exponent := 1, mantissa := (2119/2048) } }, logOuter := sk85LogOuterCertificate, logK := sk85LogKCertificate, logChi := chi67LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68716218367/68714991616) } }, logDArg := sk85LogDArgCertificate }

private noncomputable def leaf3817InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf3817LocalValidity :
    LeafFacts leaf3817Box leaf3817Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3817Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358722559/34357495808) }) = true
      norm_num [leaf3817Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3817CertificateValid :
    WideCertificateValid leaf3817Box leaf3817Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk85ValidityFacts chi67ValidityFacts
    leaf3817LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3817CoverageChecked :
    coverageCheck (innerAD leaf3817Box) leaf3817InnerLog = true := by
  rfl'

private theorem leaf3817InnerLogValid :
    leaf3817InnerLog.Valid 8 (innerAD leaf3817Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf3817CoverageChecked

private noncomputable def leaf3817InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907345/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3817InputLogOnePlusV_eq :
    leaf3817InputLogOnePlusV = outerEnclosure 24
      (leaf3817Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3817RoundedFacts : LeafRoundedFacts 8
    leaf3817Certificate.logOnePlusV leaf3817InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3817InputLogOnePlusV_eq }

private noncomputable def leaf3817Inputs : Inputs :=
  inputsOfCaches globalInput sk85RoundedInputs
    chi67InputQChi innerPair117Input
    leaf3817InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3817LowerChecked :
    lowerCheck 24 leaf3817Box leaf3817Inputs = true := by
  rfl'

private theorem leaf3817CoversExact : CoversExact 8
    leaf3817Box leaf3817Certificate leaf3817InnerLog leaf3817Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk85RoundedFacts chi67RoundedFacts
    innerPair117RoundedFacts leaf3817RoundedFacts (by rfl)

private theorem leaf3817FlatSound : Sound leaf3817Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3817CertificateValid
    leaf3817InnerLogValid leaf3817CoversExact leaf3817LowerChecked

private noncomputable def leaf3818Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (73/32), kHi := (37/16), chiLo := (29/64), chiHi := (15/32) }

private noncomputable def leaf3818Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217935/134217728) }, vSqrt := { lower := (65531/65536), upper := (34358722559/34357465088) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (272915999/268435456) }, upper := { exponent := 1, mantissa := (1067/1024) } }, logOuter := sk86LogOuterCertificate, logK := sk86LogKCertificate, logChi := chi67LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68716187647/68714930176) } }, logDArg := sk86LogDArgCertificate }

private noncomputable def leaf3818InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf3818LocalValidity :
    LeafFacts leaf3818Box leaf3818Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3818Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358722559/34357465088) }) = true
      norm_num [leaf3818Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3818CertificateValid :
    WideCertificateValid leaf3818Box leaf3818Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk86ValidityFacts chi67ValidityFacts
    leaf3818LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3818CoverageChecked :
    coverageCheck (innerAD leaf3818Box) leaf3818InnerLog = true := by
  rfl'

private theorem leaf3818InnerLogValid :
    leaf3818InnerLog.Valid 8 (innerAD leaf3818Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf3818CoverageChecked

private noncomputable def leaf3818InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907347/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3818InputLogOnePlusV_eq :
    leaf3818InputLogOnePlusV = outerEnclosure 24
      (leaf3818Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3818RoundedFacts : LeafRoundedFacts 8
    leaf3818Certificate.logOnePlusV leaf3818InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3818InputLogOnePlusV_eq }

private noncomputable def leaf3818Inputs : Inputs :=
  inputsOfCaches globalInput sk86RoundedInputs
    chi67InputQChi innerPair117Input
    leaf3818InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3818LowerChecked :
    lowerCheck 24 leaf3818Box leaf3818Inputs = true := by
  rfl'

private theorem leaf3818CoversExact : CoversExact 8
    leaf3818Box leaf3818Certificate leaf3818InnerLog leaf3818Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk86RoundedFacts chi67RoundedFacts
    innerPair117RoundedFacts leaf3818RoundedFacts (by rfl)

private theorem leaf3818FlatSound : Sound leaf3818Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3818CertificateValid
    leaf3818InnerLogValid leaf3818CoversExact leaf3818LowerChecked

private noncomputable def leaf3819Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (75/32), chiLo := (7/16), chiHi := (29/64) }

private noncomputable def leaf3819Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217935/134217728) }, vSqrt := { lower := (65531/65536), upper := (34358722559/34357511168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (269967059/268435456) }, upper := { exponent := 1, mantissa := (4223/4096) } }, logOuter := sk79LogOuterCertificate, logK := sk79LogKCertificate, logChi := chi66LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68716233727/68715022336) } }, logDArg := sk79LogDArgCertificate }

private noncomputable def leaf3819InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf3819LocalValidity :
    LeafFacts leaf3819Box leaf3819Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3819Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358722559/34357511168) }) = true
      norm_num [leaf3819Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3819CertificateValid :
    WideCertificateValid leaf3819Box leaf3819Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk79ValidityFacts chi66ValidityFacts
    leaf3819LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3819CoverageChecked :
    coverageCheck (innerAD leaf3819Box) leaf3819InnerLog = true := by
  rfl'

private theorem leaf3819InnerLogValid :
    leaf3819InnerLog.Valid 8 (innerAD leaf3819Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf3819CoverageChecked

private noncomputable def leaf3819InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629377/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3819InputLogOnePlusV_eq :
    leaf3819InputLogOnePlusV = outerEnclosure 24
      (leaf3819Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3819RoundedFacts : LeafRoundedFacts 8
    leaf3819Certificate.logOnePlusV leaf3819InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3819InputLogOnePlusV_eq }

private noncomputable def leaf3819Inputs : Inputs :=
  inputsOfCaches globalInput sk79RoundedInputs
    chi66InputQChi innerPair116Input
    leaf3819InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3819LowerChecked :
    lowerCheck 24 leaf3819Box leaf3819Inputs = true := by
  rfl'

private theorem leaf3819CoversExact : CoversExact 8
    leaf3819Box leaf3819Certificate leaf3819InnerLog leaf3819Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk79RoundedFacts chi66RoundedFacts
    innerPair116RoundedFacts leaf3819RoundedFacts (by rfl)

private theorem leaf3819FlatSound : Sound leaf3819Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3819CertificateValid
    leaf3819InnerLogValid leaf3819CoversExact leaf3819LowerChecked

private noncomputable def leaf3820Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (75/32), kHi := (19/8), chiLo := (7/16), chiHi := (29/64) }

private noncomputable def leaf3820Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217937/134217728) }, vSqrt := { lower := (65531/65536), upper := (34358722559/34357481472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (271801953/268435456) }, upper := { exponent := 1, mantissa := (1063/1024) } }, logOuter := sk80LogOuterCertificate, logK := sk80LogKCertificate, logChi := chi66LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68716204031/68714962944) } }, logDArg := sk80LogDArgCertificate }

private noncomputable def leaf3820InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf3820LocalValidity :
    LeafFacts leaf3820Box leaf3820Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3820Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358722559/34357481472) }) = true
      norm_num [leaf3820Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3820CertificateValid :
    WideCertificateValid leaf3820Box leaf3820Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk80ValidityFacts chi66ValidityFacts
    leaf3820LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3820CoverageChecked :
    coverageCheck (innerAD leaf3820Box) leaf3820InnerLog = true := by
  rfl'

private theorem leaf3820InnerLogValid :
    leaf3820InnerLog.Valid 8 (innerAD leaf3820Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf3820CoverageChecked

private noncomputable def leaf3820InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (1453673/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3820InputLogOnePlusV_eq :
    leaf3820InputLogOnePlusV = outerEnclosure 24
      (leaf3820Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3820RoundedFacts : LeafRoundedFacts 8
    leaf3820Certificate.logOnePlusV leaf3820InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3820InputLogOnePlusV_eq }

private noncomputable def leaf3820Inputs : Inputs :=
  inputsOfCaches globalInput sk80RoundedInputs
    chi66InputQChi innerPair117Input
    leaf3820InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3820LowerChecked :
    lowerCheck 24 leaf3820Box leaf3820Inputs = true := by
  rfl'

private theorem leaf3820CoversExact : CoversExact 8
    leaf3820Box leaf3820Certificate leaf3820InnerLog leaf3820Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk80RoundedFacts chi66RoundedFacts
    innerPair117RoundedFacts leaf3820RoundedFacts (by rfl)

private theorem leaf3820FlatSound : Sound leaf3820Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3820CertificateValid
    leaf3820InnerLogValid leaf3820CoversExact leaf3820LowerChecked

private noncomputable def leaf3821Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (75/32), chiLo := (29/64), chiHi := (15/32) }

private noncomputable def leaf3821Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217937/134217728) }, vSqrt := { lower := (65531/65536), upper := (34358722559/34357434368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (274816425/268435456) }, upper := { exponent := 1, mantissa := (2149/2048) } }, logOuter := sk79LogOuterCertificate, logK := sk79LogKCertificate, logChi := chi67LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68716156927/68714868736) } }, logDArg := sk79LogDArgCertificate }

private noncomputable def leaf3821InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf3821LocalValidity :
    LeafFacts leaf3821Box leaf3821Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3821Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358722559/34357434368) }) = true
      norm_num [leaf3821Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3821CertificateValid :
    WideCertificateValid leaf3821Box leaf3821Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk79ValidityFacts chi67ValidityFacts
    leaf3821LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3821CoverageChecked :
    coverageCheck (innerAD leaf3821Box) leaf3821InnerLog = true := by
  rfl'

private theorem leaf3821InnerLogValid :
    leaf3821InnerLog.Valid 8 (innerAD leaf3821Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf3821CoverageChecked

private noncomputable def leaf3821InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629395/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3821InputLogOnePlusV_eq :
    leaf3821InputLogOnePlusV = outerEnclosure 24
      (leaf3821Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3821RoundedFacts : LeafRoundedFacts 8
    leaf3821Certificate.logOnePlusV leaf3821InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3821InputLogOnePlusV_eq }

private noncomputable def leaf3821Inputs : Inputs :=
  inputsOfCaches globalInput sk79RoundedInputs
    chi67InputQChi innerPair117Input
    leaf3821InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3821LowerChecked :
    lowerCheck 24 leaf3821Box leaf3821Inputs = true := by
  rfl'

private theorem leaf3821CoversExact : CoversExact 8
    leaf3821Box leaf3821Certificate leaf3821InnerLog leaf3821Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk79RoundedFacts chi67RoundedFacts
    innerPair117RoundedFacts leaf3821RoundedFacts (by rfl)

private theorem leaf3821FlatSound : Sound leaf3821Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3821CertificateValid
    leaf3821InnerLogValid leaf3821CoversExact leaf3821LowerChecked

private noncomputable def leaf3822Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (75/32), kHi := (19/8), chiLo := (29/64), chiHi := (15/32) }

private noncomputable def leaf3822Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217939/134217728) }, vSqrt := { lower := (65531/65536), upper := (2021101327/2021023744) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (276716851/268435456) }, upper := { exponent := 1, mantissa := (541/512) } }, logOuter := sk80LogOuterCertificate, logK := sk80LogKCertificate, logChi := chi67LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (4042125071/4042047488) } }, logDArg := sk80LogDArgCertificate }

private noncomputable def leaf3822InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf3822LocalValidity :
    LeafFacts leaf3822Box leaf3822Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3822Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (2021101327/2021023744) }) = true
      norm_num [leaf3822Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3822CertificateValid :
    WideCertificateValid leaf3822Box leaf3822Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk80ValidityFacts chi67ValidityFacts
    leaf3822LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3822CoverageChecked :
    coverageCheck (innerAD leaf3822Box) leaf3822InnerLog = true := by
  rfl'

private theorem leaf3822InnerLogValid :
    leaf3822InnerLog.Valid 8 (innerAD leaf3822Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf3822CoverageChecked

private noncomputable def leaf3822InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629403/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3822InputLogOnePlusV_eq :
    leaf3822InputLogOnePlusV = outerEnclosure 24
      (leaf3822Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3822RoundedFacts : LeafRoundedFacts 8
    leaf3822Certificate.logOnePlusV leaf3822InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3822InputLogOnePlusV_eq }

private noncomputable def leaf3822Inputs : Inputs :=
  inputsOfCaches globalInput sk80RoundedInputs
    chi67InputQChi innerPair117Input
    leaf3822InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3822LowerChecked :
    lowerCheck 24 leaf3822Box leaf3822Inputs = true := by
  rfl'

private theorem leaf3822CoversExact : CoversExact 8
    leaf3822Box leaf3822Certificate leaf3822InnerLog leaf3822Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk80RoundedFacts chi67RoundedFacts
    innerPair117RoundedFacts leaf3822RoundedFacts (by rfl)

private theorem leaf3822FlatSound : Sound leaf3822Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3822CertificateValid
    leaf3822InnerLogValid leaf3822CoversExact leaf3822LowerChecked

private noncomputable def leaf3823Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (73/32), chiLo := (15/32), chiHi := (31/64) }

private noncomputable def leaf3823Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217935/134217728) }, vSqrt := { lower := (65531/65536), upper := (288728761/288717824) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (275733875/268435456) }, upper := { exponent := 1, mantissa := (4311/4096) } }, logOuter := sk85LogOuterCertificate, logK := sk85LogKCertificate, logChi := chi68LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (577446585/577435648) } }, logDArg := sk85LogDArgCertificate }

private noncomputable def leaf3823InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf3823LocalValidity :
    LeafFacts leaf3823Box leaf3823Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3823Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (288728761/288717824) }) = true
      norm_num [leaf3823Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3823CertificateValid :
    WideCertificateValid leaf3823Box leaf3823Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk85ValidityFacts chi68ValidityFacts
    leaf3823LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3823CoverageChecked :
    coverageCheck (innerAD leaf3823Box) leaf3823InnerLog = true := by
  rfl'

private theorem leaf3823InnerLogValid :
    leaf3823InnerLog.Valid 8 (innerAD leaf3823Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf3823CoverageChecked

private noncomputable def leaf3823InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629399/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3823InputLogOnePlusV_eq :
    leaf3823InputLogOnePlusV = outerEnclosure 24
      (leaf3823Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3823RoundedFacts : LeafRoundedFacts 8
    leaf3823Certificate.logOnePlusV leaf3823InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3823InputLogOnePlusV_eq }

private noncomputable def leaf3823Inputs : Inputs :=
  inputsOfCaches globalInput sk85RoundedInputs
    chi68InputQChi innerPair117Input
    leaf3823InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3823LowerChecked :
    lowerCheck 24 leaf3823Box leaf3823Inputs = true := by
  rfl'

private theorem leaf3823CoversExact : CoversExact 8
    leaf3823Box leaf3823Certificate leaf3823InnerLog leaf3823Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk85RoundedFacts chi68RoundedFacts
    innerPair117RoundedFacts leaf3823RoundedFacts (by rfl)

private theorem leaf3823FlatSound : Sound leaf3823Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3823CertificateValid
    leaf3823InnerLogValid leaf3823CoversExact leaf3823LowerChecked

private noncomputable def leaf3824Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (73/32), kHi := (37/16), chiLo := (15/32), chiHi := (31/64) }

private noncomputable def leaf3824Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217937/134217728) }, vSqrt := { lower := (65531/65536), upper := (34358722559/34357389312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (277699833/268435456) }, upper := { exponent := 1, mantissa := (2171/2048) } }, logOuter := sk86LogOuterCertificate, logK := sk86LogKCertificate, logChi := chi68LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68716111871/68714778624) } }, logDArg := sk86LogDArgCertificate }

private noncomputable def leaf3824InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf3824LocalValidity :
    LeafFacts leaf3824Box leaf3824Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3824Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358722559/34357389312) }) = true
      norm_num [leaf3824Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3824CertificateValid :
    WideCertificateValid leaf3824Box leaf3824Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk86ValidityFacts chi68ValidityFacts
    leaf3824LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3824CoverageChecked :
    coverageCheck (innerAD leaf3824Box) leaf3824InnerLog = true := by
  rfl'

private theorem leaf3824InnerLogValid :
    leaf3824InnerLog.Valid 8 (innerAD leaf3824Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf3824CoverageChecked

private noncomputable def leaf3824InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814703/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3824InputLogOnePlusV_eq :
    leaf3824InputLogOnePlusV = outerEnclosure 24
      (leaf3824Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3824RoundedFacts : LeafRoundedFacts 8
    leaf3824Certificate.logOnePlusV leaf3824InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3824InputLogOnePlusV_eq }

private noncomputable def leaf3824Inputs : Inputs :=
  inputsOfCaches globalInput sk86RoundedInputs
    chi68InputQChi innerPair242Input
    leaf3824InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3824LowerChecked :
    lowerCheck 24 leaf3824Box leaf3824Inputs = true := by
  rfl'

private theorem leaf3824CoversExact : CoversExact 8
    leaf3824Box leaf3824Certificate leaf3824InnerLog leaf3824Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk86RoundedFacts chi68RoundedFacts
    innerPair242RoundedFacts leaf3824RoundedFacts (by rfl)

private theorem leaf3824FlatSound : Sound leaf3824Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3824CertificateValid
    leaf3824InnerLogValid leaf3824CoversExact leaf3824LowerChecked

private noncomputable def leaf3825Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (31/64), chiHi := (1/2) }

private noncomputable def leaf3825Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109001/67108864) }, vSqrt := { lower := (65531/65536), upper := (2454196809/2454093824) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (140209673/134217728) }, upper := { exponent := 1, mantissa := (69/64) } }, logOuter := sk69LogOuterCertificate, logK := sk69LogKCertificate, logChi := chi69LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (4908290633/4908187648) } }, logDArg := sk69LogDArgCertificate }

private noncomputable def leaf3825InnerLog : WideLogData :=
  innerPair322Data

set_option maxRecDepth 1000000 in
private theorem leaf3825LocalValidity :
    LeafFacts leaf3825Box leaf3825Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3825Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (2454196809/2454093824) }) = true
      norm_num [leaf3825Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3825CertificateValid :
    WideCertificateValid leaf3825Box leaf3825Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk69ValidityFacts chi69ValidityFacts
    leaf3825LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3825CoverageChecked :
    coverageCheck (innerAD leaf3825Box) leaf3825InnerLog = true := by
  rfl'

private theorem leaf3825InnerLogValid :
    leaf3825InnerLog.Valid 8 (innerAD leaf3825Box) :=
  wideLogDataValid_of_cachedCheck endpoint86PositiveFacts
    endpoint88PositiveFacts.valid leaf3825CoverageChecked

private noncomputable def leaf3825InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629433/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3825InputLogOnePlusV_eq :
    leaf3825InputLogOnePlusV = outerEnclosure 24
      (leaf3825Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3825RoundedFacts : LeafRoundedFacts 8
    leaf3825Certificate.logOnePlusV leaf3825InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3825InputLogOnePlusV_eq }

private noncomputable def leaf3825Inputs : Inputs :=
  inputsOfCaches globalInput sk69RoundedInputs
    chi69InputQChi innerPair322Input
    leaf3825InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3825LowerChecked :
    lowerCheck 24 leaf3825Box leaf3825Inputs = true := by
  rfl'

private theorem leaf3825CoversExact : CoversExact 8
    leaf3825Box leaf3825Certificate leaf3825InnerLog leaf3825Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk69RoundedFacts chi69RoundedFacts
    innerPair322RoundedFacts leaf3825RoundedFacts (by rfl)

private theorem leaf3825FlatSound : Sound leaf3825Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3825CertificateValid
    leaf3825InnerLogValid leaf3825CoversExact leaf3825LowerChecked

private noncomputable def leaf3826Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (75/32), chiLo := (15/32), chiHi := (31/64) }

private noncomputable def leaf3826Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217939/134217728) }, vSqrt := { lower := (65531/65536), upper := (34358722559/34357357568) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (279665791/268435456) }, upper := { exponent := 1, mantissa := (4373/4096) } }, logOuter := sk79LogOuterCertificate, logK := sk79LogKCertificate, logChi := chi68LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68716080127/68714715136) } }, logDArg := sk79LogDArgCertificate }

private noncomputable def leaf3826InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf3826LocalValidity :
    LeafFacts leaf3826Box leaf3826Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3826Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358722559/34357357568) }) = true
      norm_num [leaf3826Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3826CertificateValid :
    WideCertificateValid leaf3826Box leaf3826Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk79ValidityFacts chi68ValidityFacts
    leaf3826LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3826CoverageChecked :
    coverageCheck (innerAD leaf3826Box) leaf3826InnerLog = true := by
  rfl'

private theorem leaf3826InnerLogValid :
    leaf3826InnerLog.Valid 8 (innerAD leaf3826Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf3826CoverageChecked

private noncomputable def leaf3826InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814707/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3826InputLogOnePlusV_eq :
    leaf3826InputLogOnePlusV = outerEnclosure 24
      (leaf3826Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3826RoundedFacts : LeafRoundedFacts 8
    leaf3826Certificate.logOnePlusV leaf3826InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3826InputLogOnePlusV_eq }

private noncomputable def leaf3826Inputs : Inputs :=
  inputsOfCaches globalInput sk79RoundedInputs
    chi68InputQChi innerPair243Input
    leaf3826InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3826LowerChecked :
    lowerCheck 24 leaf3826Box leaf3826Inputs = true := by
  rfl'

private theorem leaf3826CoversExact : CoversExact 8
    leaf3826Box leaf3826Certificate leaf3826InnerLog leaf3826Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk79RoundedFacts chi68RoundedFacts
    innerPair243RoundedFacts leaf3826RoundedFacts (by rfl)

private theorem leaf3826FlatSound : Sound leaf3826Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3826CertificateValid
    leaf3826InnerLogValid leaf3826CoversExact leaf3826LowerChecked

private noncomputable def leaf3827Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (75/32), kHi := (19/8), chiLo := (15/32), chiHi := (31/64) }

private noncomputable def leaf3827Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217941/134217728) }, vSqrt := { lower := (65531/65536), upper := (34358722559/34357325824) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (281631749/268435456) }, upper := { exponent := 1, mantissa := (1101/1024) } }, logOuter := sk80LogOuterCertificate, logK := sk80LogKCertificate, logChi := chi68LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68716048383/68714651648) } }, logDArg := sk80LogDArgCertificate }

private noncomputable def leaf3827InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf3827LocalValidity :
    LeafFacts leaf3827Box leaf3827Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3827Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358722559/34357325824) }) = true
      norm_num [leaf3827Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3827CertificateValid :
    WideCertificateValid leaf3827Box leaf3827Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk80ValidityFacts chi68ValidityFacts
    leaf3827LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3827CoverageChecked :
    coverageCheck (innerAD leaf3827Box) leaf3827InnerLog = true := by
  rfl'

private theorem leaf3827InnerLogValid :
    leaf3827InnerLog.Valid 8 (innerAD leaf3827Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf3827CoverageChecked

private noncomputable def leaf3827InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814711/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3827InputLogOnePlusV_eq :
    leaf3827InputLogOnePlusV = outerEnclosure 24
      (leaf3827Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3827RoundedFacts : LeafRoundedFacts 8
    leaf3827Certificate.logOnePlusV leaf3827InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3827InputLogOnePlusV_eq }

private noncomputable def leaf3827Inputs : Inputs :=
  inputsOfCaches globalInput sk80RoundedInputs
    chi68InputQChi innerPair243Input
    leaf3827InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3827LowerChecked :
    lowerCheck 24 leaf3827Box leaf3827Inputs = true := by
  rfl'

private theorem leaf3827CoversExact : CoversExact 8
    leaf3827Box leaf3827Certificate leaf3827InnerLog leaf3827Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk80RoundedFacts chi68RoundedFacts
    innerPair243RoundedFacts leaf3827RoundedFacts (by rfl)

private theorem leaf3827FlatSound : Sound leaf3827Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3827CertificateValid
    leaf3827InnerLogValid leaf3827CoversExact leaf3827LowerChecked

private noncomputable def leaf3828Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (75/32), chiLo := (31/64), chiHi := (1/2) }

private noncomputable def leaf3828Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217941/134217728) }, vSqrt := { lower := (65531/65536), upper := (34358722559/34357280768) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (284515157/268435456) }, upper := { exponent := 1, mantissa := (139/128) } }, logOuter := sk79LogOuterCertificate, logK := sk79LogKCertificate, logChi := chi69LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68716003327/68714561536) } }, logDArg := sk79LogDArgCertificate }

private noncomputable def leaf3828InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf3828LocalValidity :
    LeafFacts leaf3828Box leaf3828Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3828Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358722559/34357280768) }) = true
      norm_num [leaf3828Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3828CertificateValid :
    WideCertificateValid leaf3828Box leaf3828Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk79ValidityFacts chi69ValidityFacts
    leaf3828LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3828CoverageChecked :
    coverageCheck (innerAD leaf3828Box) leaf3828InnerLog = true := by
  rfl'

private theorem leaf3828InnerLogValid :
    leaf3828InnerLog.Valid 8 (innerAD leaf3828Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf3828CoverageChecked

private noncomputable def leaf3828InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629433/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3828InputLogOnePlusV_eq :
    leaf3828InputLogOnePlusV = outerEnclosure 24
      (leaf3828Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3828RoundedFacts : LeafRoundedFacts 8
    leaf3828Certificate.logOnePlusV leaf3828InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3828InputLogOnePlusV_eq }

private noncomputable def leaf3828Inputs : Inputs :=
  inputsOfCaches globalInput sk79RoundedInputs
    chi69InputQChi innerPair243Input
    leaf3828InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3828LowerChecked :
    lowerCheck 24 leaf3828Box leaf3828Inputs = true := by
  rfl'

private theorem leaf3828CoversExact : CoversExact 8
    leaf3828Box leaf3828Certificate leaf3828InnerLog leaf3828Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk79RoundedFacts chi69RoundedFacts
    innerPair243RoundedFacts leaf3828RoundedFacts (by rfl)

private theorem leaf3828FlatSound : Sound leaf3828Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3828CertificateValid
    leaf3828InnerLogValid leaf3828CoversExact leaf3828LowerChecked

private noncomputable def leaf3829Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (75/32), kHi := (19/8), chiLo := (31/64), chiHi := (1/2) }

private noncomputable def leaf3829Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217943/134217728) }, vSqrt := { lower := (65531/65536), upper := (34358722559/34357248000) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (286546647/268435456) }, upper := { exponent := 1, mantissa := (35/32) } }, logOuter := sk80LogOuterCertificate, logK := sk80LogKCertificate, logChi := chi69LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68715970559/68714496000) } }, logDArg := sk80LogDArgCertificate }

private noncomputable def leaf3829InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf3829LocalValidity :
    LeafFacts leaf3829Box leaf3829Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3829Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358722559/34357248000) }) = true
      norm_num [leaf3829Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3829CertificateValid :
    WideCertificateValid leaf3829Box leaf3829Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk80ValidityFacts chi69ValidityFacts
    leaf3829LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3829CoverageChecked :
    coverageCheck (innerAD leaf3829Box) leaf3829InnerLog = true := by
  rfl'

private theorem leaf3829InnerLogValid :
    leaf3829InnerLog.Valid 8 (innerAD leaf3829Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf3829CoverageChecked

private noncomputable def leaf3829InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629441/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3829InputLogOnePlusV_eq :
    leaf3829InputLogOnePlusV = outerEnclosure 24
      (leaf3829Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3829RoundedFacts : LeafRoundedFacts 8
    leaf3829Certificate.logOnePlusV leaf3829InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3829InputLogOnePlusV_eq }

private noncomputable def leaf3829Inputs : Inputs :=
  inputsOfCaches globalInput sk80RoundedInputs
    chi69InputQChi innerPair249Input
    leaf3829InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3829LowerChecked :
    lowerCheck 24 leaf3829Box leaf3829Inputs = true := by
  rfl'

private theorem leaf3829CoversExact : CoversExact 8
    leaf3829Box leaf3829Certificate leaf3829InnerLog leaf3829Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk80RoundedFacts chi69RoundedFacts
    innerPair249RoundedFacts leaf3829RoundedFacts (by rfl)

private theorem leaf3829FlatSound : Sound leaf3829Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3829CertificateValid
    leaf3829InnerLogValid leaf3829CoversExact leaf3829LowerChecked

private noncomputable def leaf3830Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (77/32), chiLo := (7/16), chiHi := (29/64) }

private noncomputable def leaf3830Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217939/134217728) }, vSqrt := { lower := (65531/65536), upper := (1108345889/1108304896) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (273636847/268435456) }, upper := { exponent := 1, mantissa := (4281/4096) } }, logOuter := sk81LogOuterCertificate, logK := sk81LogKCertificate, logChi := chi66LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (2216650785/2216609792) } }, logDArg := sk81LogDArgCertificate }

private noncomputable def leaf3830InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf3830LocalValidity :
    LeafFacts leaf3830Box leaf3830Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3830Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (1108345889/1108304896) }) = true
      norm_num [leaf3830Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3830CertificateValid :
    WideCertificateValid leaf3830Box leaf3830Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk81ValidityFacts chi66ValidityFacts
    leaf3830LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3830CoverageChecked :
    coverageCheck (innerAD leaf3830Box) leaf3830InnerLog = true := by
  rfl'

private theorem leaf3830InnerLogValid :
    leaf3830InnerLog.Valid 8 (innerAD leaf3830Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf3830CoverageChecked

private noncomputable def leaf3830InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629391/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3830InputLogOnePlusV_eq :
    leaf3830InputLogOnePlusV = outerEnclosure 24
      (leaf3830Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3830RoundedFacts : LeafRoundedFacts 8
    leaf3830Certificate.logOnePlusV leaf3830InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3830InputLogOnePlusV_eq }

private noncomputable def leaf3830Inputs : Inputs :=
  inputsOfCaches globalInput sk81RoundedInputs
    chi66InputQChi innerPair117Input
    leaf3830InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3830LowerChecked :
    lowerCheck 24 leaf3830Box leaf3830Inputs = true := by
  rfl'

private theorem leaf3830CoversExact : CoversExact 8
    leaf3830Box leaf3830Certificate leaf3830InnerLog leaf3830Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk81RoundedFacts chi66RoundedFacts
    innerPair117RoundedFacts leaf3830RoundedFacts (by rfl)

private theorem leaf3830FlatSound : Sound leaf3830Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3830CertificateValid
    leaf3830InnerLogValid leaf3830CoversExact leaf3830LowerChecked

private noncomputable def leaf3831Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (77/32), kHi := (39/16), chiLo := (7/16), chiHi := (29/64) }

private noncomputable def leaf3831Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217941/134217728) }, vSqrt := { lower := (65531/65536), upper := (34358722559/34357422080) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (275471741/268435456) }, upper := { exponent := 1, mantissa := (2155/2048) } }, logOuter := sk82LogOuterCertificate, logK := sk82LogKCertificate, logChi := chi66LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68716144639/68714844160) } }, logDArg := sk82LogDArgCertificate }

private noncomputable def leaf3831InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf3831LocalValidity :
    LeafFacts leaf3831Box leaf3831Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3831Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358722559/34357422080) }) = true
      norm_num [leaf3831Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3831CertificateValid :
    WideCertificateValid leaf3831Box leaf3831Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk82ValidityFacts chi66ValidityFacts
    leaf3831LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3831CoverageChecked :
    coverageCheck (innerAD leaf3831Box) leaf3831InnerLog = true := by
  rfl'

private theorem leaf3831InnerLogValid :
    leaf3831InnerLog.Valid 8 (innerAD leaf3831Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf3831CoverageChecked

private noncomputable def leaf3831InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814699/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3831InputLogOnePlusV_eq :
    leaf3831InputLogOnePlusV = outerEnclosure 24
      (leaf3831Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3831RoundedFacts : LeafRoundedFacts 8
    leaf3831Certificate.logOnePlusV leaf3831InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3831InputLogOnePlusV_eq }

private noncomputable def leaf3831Inputs : Inputs :=
  inputsOfCaches globalInput sk82RoundedInputs
    chi66InputQChi innerPair117Input
    leaf3831InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3831LowerChecked :
    lowerCheck 24 leaf3831Box leaf3831Inputs = true := by
  rfl'

private theorem leaf3831CoversExact : CoversExact 8
    leaf3831Box leaf3831Certificate leaf3831InnerLog leaf3831Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk82RoundedFacts chi66RoundedFacts
    innerPair117RoundedFacts leaf3831RoundedFacts (by rfl)

private theorem leaf3831FlatSound : Sound leaf3831Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3831CertificateValid
    leaf3831InnerLogValid leaf3831CoversExact leaf3831LowerChecked

private noncomputable def leaf3832Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (77/32), chiLo := (29/64), chiHi := (15/32) }

private noncomputable def leaf3832Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217941/134217728) }, vSqrt := { lower := (65531/65536), upper := (34358722559/34357372928) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (278617277/268435456) }, upper := { exponent := 1, mantissa := (2179/2048) } }, logOuter := sk81LogOuterCertificate, logK := sk81LogKCertificate, logChi := chi67LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68716095487/68714745856) } }, logDArg := sk81LogDArgCertificate }

private noncomputable def leaf3832InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf3832LocalValidity :
    LeafFacts leaf3832Box leaf3832Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3832Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358722559/34357372928) }) = true
      norm_num [leaf3832Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3832CertificateValid :
    WideCertificateValid leaf3832Box leaf3832Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk81ValidityFacts chi67ValidityFacts
    leaf3832LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3832CoverageChecked :
    coverageCheck (innerAD leaf3832Box) leaf3832InnerLog = true := by
  rfl'

private theorem leaf3832InnerLogValid :
    leaf3832InnerLog.Valid 8 (innerAD leaf3832Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf3832CoverageChecked

private noncomputable def leaf3832InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814705/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3832InputLogOnePlusV_eq :
    leaf3832InputLogOnePlusV = outerEnclosure 24
      (leaf3832Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3832RoundedFacts : LeafRoundedFacts 8
    leaf3832Certificate.logOnePlusV leaf3832InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3832InputLogOnePlusV_eq }

private noncomputable def leaf3832Inputs : Inputs :=
  inputsOfCaches globalInput sk81RoundedInputs
    chi67InputQChi innerPair243Input
    leaf3832InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3832LowerChecked :
    lowerCheck 24 leaf3832Box leaf3832Inputs = true := by
  rfl'

private theorem leaf3832CoversExact : CoversExact 8
    leaf3832Box leaf3832Certificate leaf3832InnerLog leaf3832Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk81RoundedFacts chi67RoundedFacts
    innerPair243RoundedFacts leaf3832RoundedFacts (by rfl)

private theorem leaf3832FlatSound : Sound leaf3832Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3832CertificateValid
    leaf3832InnerLogValid leaf3832CoversExact leaf3832LowerChecked

private noncomputable def leaf3833Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (77/32), kHi := (39/16), chiLo := (29/64), chiHi := (15/32) }

private noncomputable def leaf3833Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217943/134217728) }, vSqrt := { lower := (65531/65536), upper := (4908388937/4908191744) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (280517703/268435456) }, upper := { exponent := 1, mantissa := (1097/1024) } }, logOuter := sk82LogOuterCertificate, logK := sk82LogKCertificate, logChi := chi67LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (9816580681/9816383488) } }, logDArg := sk82LogDArgCertificate }

private noncomputable def leaf3833InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf3833LocalValidity :
    LeafFacts leaf3833Box leaf3833Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3833Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (4908388937/4908191744) }) = true
      norm_num [leaf3833Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3833CertificateValid :
    WideCertificateValid leaf3833Box leaf3833Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk82ValidityFacts chi67ValidityFacts
    leaf3833LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3833CoverageChecked :
    coverageCheck (innerAD leaf3833Box) leaf3833InnerLog = true := by
  rfl'

private theorem leaf3833InnerLogValid :
    leaf3833InnerLog.Valid 8 (innerAD leaf3833Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf3833CoverageChecked

private noncomputable def leaf3833InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814709/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3833InputLogOnePlusV_eq :
    leaf3833InputLogOnePlusV = outerEnclosure 24
      (leaf3833Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3833RoundedFacts : LeafRoundedFacts 8
    leaf3833Certificate.logOnePlusV leaf3833InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3833InputLogOnePlusV_eq }

private noncomputable def leaf3833Inputs : Inputs :=
  inputsOfCaches globalInput sk82RoundedInputs
    chi67InputQChi innerPair243Input
    leaf3833InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3833LowerChecked :
    lowerCheck 24 leaf3833Box leaf3833Inputs = true := by
  rfl'

private theorem leaf3833CoversExact : CoversExact 8
    leaf3833Box leaf3833Certificate leaf3833InnerLog leaf3833Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk82RoundedFacts chi67RoundedFacts
    innerPair243RoundedFacts leaf3833RoundedFacts (by rfl)

private theorem leaf3833FlatSound : Sound leaf3833Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3833CertificateValid
    leaf3833InnerLogValid leaf3833CoversExact leaf3833LowerChecked

private noncomputable def leaf3834Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (79/32), chiLo := (7/16), chiHi := (29/64) }

private noncomputable def leaf3834Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217943/134217728) }, vSqrt := { lower := (65531/65536), upper := (4908388937/4908198912) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (277306635/268435456) }, upper := { exponent := 1, mantissa := (4339/4096) } }, logOuter := sk83LogOuterCertificate, logK := sk83LogKCertificate, logChi := chi66LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (9816587849/9816397824) } }, logDArg := sk83LogDArgCertificate }

private noncomputable def leaf3834InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf3834LocalValidity :
    LeafFacts leaf3834Box leaf3834Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3834Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (4908388937/4908198912) }) = true
      norm_num [leaf3834Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3834CertificateValid :
    WideCertificateValid leaf3834Box leaf3834Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk83ValidityFacts chi66ValidityFacts
    leaf3834LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3834CoverageChecked :
    coverageCheck (innerAD leaf3834Box) leaf3834InnerLog = true := by
  rfl'

private theorem leaf3834InnerLogValid :
    leaf3834InnerLog.Valid 8 (innerAD leaf3834Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf3834CoverageChecked

private noncomputable def leaf3834InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814703/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3834InputLogOnePlusV_eq :
    leaf3834InputLogOnePlusV = outerEnclosure 24
      (leaf3834Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3834RoundedFacts : LeafRoundedFacts 8
    leaf3834Certificate.logOnePlusV leaf3834InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3834InputLogOnePlusV_eq }

private noncomputable def leaf3834Inputs : Inputs :=
  inputsOfCaches globalInput sk83RoundedInputs
    chi66InputQChi innerPair242Input
    leaf3834InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3834LowerChecked :
    lowerCheck 24 leaf3834Box leaf3834Inputs = true := by
  rfl'

private theorem leaf3834CoversExact : CoversExact 8
    leaf3834Box leaf3834Certificate leaf3834InnerLog leaf3834Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk83RoundedFacts chi66RoundedFacts
    innerPair242RoundedFacts leaf3834RoundedFacts (by rfl)

private theorem leaf3834FlatSound : Sound leaf3834Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3834CertificateValid
    leaf3834InnerLogValid leaf3834CoversExact leaf3834LowerChecked

private noncomputable def leaf3835Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (79/32), kHi := (5/2), chiLo := (7/16), chiHi := (29/64) }

private noncomputable def leaf3835Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217945/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357362688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (279141529/268435456) }, upper := { exponent := 1, mantissa := (273/256) } }, logOuter := sk84LogOuterCertificate, logK := sk84LogKCertificate, logChi := chi66LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716085247/68714725376) } }, logDArg := sk84LogDArgCertificate }

private noncomputable def leaf3835InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf3835LocalValidity :
    LeafFacts leaf3835Box leaf3835Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3835Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357362688) }) = true
      norm_num [leaf3835Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3835CertificateValid :
    WideCertificateValid leaf3835Box leaf3835Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk84ValidityFacts chi66ValidityFacts
    leaf3835LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3835CoverageChecked :
    coverageCheck (innerAD leaf3835Box) leaf3835InnerLog = true := by
  rfl'

private theorem leaf3835InnerLogValid :
    leaf3835InnerLog.Valid 8 (innerAD leaf3835Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf3835CoverageChecked

private noncomputable def leaf3835InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629413/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3835InputLogOnePlusV_eq :
    leaf3835InputLogOnePlusV = outerEnclosure 24
      (leaf3835Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3835RoundedFacts : LeafRoundedFacts 8
    leaf3835Certificate.logOnePlusV leaf3835InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3835InputLogOnePlusV_eq }

private noncomputable def leaf3835Inputs : Inputs :=
  inputsOfCaches globalInput sk84RoundedInputs
    chi66InputQChi innerPair243Input
    leaf3835InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3835LowerChecked :
    lowerCheck 24 leaf3835Box leaf3835Inputs = true := by
  rfl'

private theorem leaf3835CoversExact : CoversExact 8
    leaf3835Box leaf3835Certificate leaf3835InnerLog leaf3835Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk84RoundedFacts chi66RoundedFacts
    innerPair243RoundedFacts leaf3835RoundedFacts (by rfl)

private theorem leaf3835FlatSound : Sound leaf3835Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3835CertificateValid
    leaf3835InnerLogValid leaf3835CoversExact leaf3835LowerChecked

private noncomputable def leaf3836Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (79/32), chiLo := (29/64), chiHi := (15/32) }

private noncomputable def leaf3836Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217945/134217728) }, vSqrt := { lower := (65531/65536), upper := (34358722559/34357311488) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (282418129/268435456) }, upper := { exponent := 1, mantissa := (2209/2048) } }, logOuter := sk83LogOuterCertificate, logK := sk83LogKCertificate, logChi := chi67LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68716034047/68714622976) } }, logDArg := sk83LogDArgCertificate }

private noncomputable def leaf3836InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf3836LocalValidity :
    LeafFacts leaf3836Box leaf3836Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3836Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358722559/34357311488) }) = true
      norm_num [leaf3836Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3836CertificateValid :
    WideCertificateValid leaf3836Box leaf3836Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk83ValidityFacts chi67ValidityFacts
    leaf3836LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3836CoverageChecked :
    coverageCheck (innerAD leaf3836Box) leaf3836InnerLog = true := by
  rfl'

private theorem leaf3836InnerLogValid :
    leaf3836InnerLog.Valid 8 (innerAD leaf3836Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf3836CoverageChecked

private noncomputable def leaf3836InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629425/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3836InputLogOnePlusV_eq :
    leaf3836InputLogOnePlusV = outerEnclosure 24
      (leaf3836Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3836RoundedFacts : LeafRoundedFacts 8
    leaf3836Certificate.logOnePlusV leaf3836InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3836InputLogOnePlusV_eq }

private noncomputable def leaf3836Inputs : Inputs :=
  inputsOfCaches globalInput sk83RoundedInputs
    chi67InputQChi innerPair243Input
    leaf3836InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3836LowerChecked :
    lowerCheck 24 leaf3836Box leaf3836Inputs = true := by
  rfl'

private theorem leaf3836CoversExact : CoversExact 8
    leaf3836Box leaf3836Certificate leaf3836InnerLog leaf3836Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk83RoundedFacts chi67RoundedFacts
    innerPair243RoundedFacts leaf3836RoundedFacts (by rfl)

private theorem leaf3836FlatSound : Sound leaf3836Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3836CertificateValid
    leaf3836InnerLogValid leaf3836CoversExact leaf3836LowerChecked

private noncomputable def leaf3837Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (79/32), kHi := (5/2), chiLo := (29/64), chiHi := (15/32) }

private noncomputable def leaf3837Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217947/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357280768) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (284318555/268435456) }, upper := { exponent := 1, mantissa := (139/128) } }, logOuter := sk84LogOuterCertificate, logK := sk84LogKCertificate, logChi := chi67LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716003327/68714561536) } }, logDArg := sk84LogDArgCertificate }

private noncomputable def leaf3837InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf3837LocalValidity :
    LeafFacts leaf3837Box leaf3837Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3837Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357280768) }) = true
      norm_num [leaf3837Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3837CertificateValid :
    WideCertificateValid leaf3837Box leaf3837Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk84ValidityFacts chi67ValidityFacts
    leaf3837LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3837CoverageChecked :
    coverageCheck (innerAD leaf3837Box) leaf3837InnerLog = true := by
  rfl'

private theorem leaf3837InnerLogValid :
    leaf3837InnerLog.Valid 8 (innerAD leaf3837Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf3837CoverageChecked

private noncomputable def leaf3837InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629433/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3837InputLogOnePlusV_eq :
    leaf3837InputLogOnePlusV = outerEnclosure 24
      (leaf3837Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3837RoundedFacts : LeafRoundedFacts 8
    leaf3837Certificate.logOnePlusV leaf3837InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3837InputLogOnePlusV_eq }

private noncomputable def leaf3837Inputs : Inputs :=
  inputsOfCaches globalInput sk84RoundedInputs
    chi67InputQChi innerPair243Input
    leaf3837InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3837LowerChecked :
    lowerCheck 24 leaf3837Box leaf3837Inputs = true := by
  rfl'

private theorem leaf3837CoversExact : CoversExact 8
    leaf3837Box leaf3837Certificate leaf3837InnerLog leaf3837Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk84RoundedFacts chi67RoundedFacts
    innerPair243RoundedFacts leaf3837RoundedFacts (by rfl)

private theorem leaf3837FlatSound : Sound leaf3837Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3837CertificateValid
    leaf3837InnerLogValid leaf3837CoversExact leaf3837LowerChecked

private noncomputable def leaf3838Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (77/32), chiLo := (15/32), chiHi := (31/64) }

private noncomputable def leaf3838Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217943/134217728) }, vSqrt := { lower := (65531/65536), upper := (34358722559/34357294080) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (283597707/268435456) }, upper := { exponent := 1, mantissa := (4435/4096) } }, logOuter := sk81LogOuterCertificate, logK := sk81LogKCertificate, logChi := chi68LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68716016639/68714588160) } }, logDArg := sk81LogDArgCertificate }

private noncomputable def leaf3838InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf3838LocalValidity :
    LeafFacts leaf3838Box leaf3838Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3838Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358722559/34357294080) }) = true
      norm_num [leaf3838Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3838CertificateValid :
    WideCertificateValid leaf3838Box leaf3838Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk81ValidityFacts chi68ValidityFacts
    leaf3838LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3838CoverageChecked :
    coverageCheck (innerAD leaf3838Box) leaf3838InnerLog = true := by
  rfl'

private theorem leaf3838InnerLogValid :
    leaf3838InnerLog.Valid 8 (innerAD leaf3838Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf3838CoverageChecked

private noncomputable def leaf3838InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814715/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3838InputLogOnePlusV_eq :
    leaf3838InputLogOnePlusV = outerEnclosure 24
      (leaf3838Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3838RoundedFacts : LeafRoundedFacts 8
    leaf3838Certificate.logOnePlusV leaf3838InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3838InputLogOnePlusV_eq }

private noncomputable def leaf3838Inputs : Inputs :=
  inputsOfCaches globalInput sk81RoundedInputs
    chi68InputQChi innerPair243Input
    leaf3838InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3838LowerChecked :
    lowerCheck 24 leaf3838Box leaf3838Inputs = true := by
  rfl'

private theorem leaf3838CoversExact : CoversExact 8
    leaf3838Box leaf3838Certificate leaf3838InnerLog leaf3838Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk81RoundedFacts chi68RoundedFacts
    innerPair243RoundedFacts leaf3838RoundedFacts (by rfl)

private theorem leaf3838FlatSound : Sound leaf3838Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3838CertificateValid
    leaf3838InnerLogValid leaf3838CoversExact leaf3838LowerChecked

private noncomputable def leaf3839Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (77/32), kHi := (39/16), chiLo := (15/32), chiHi := (31/64) }

private noncomputable def leaf3839Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217945/134217728) }, vSqrt := { lower := (65531/65536), upper := (34358722559/34357262336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (285563665/268435456) }, upper := { exponent := 1, mantissa := (2233/2048) } }, logOuter := sk82LogOuterCertificate, logK := sk82LogKCertificate, logChi := chi68LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68715984895/68714524672) } }, logDArg := sk82LogDArgCertificate }

private noncomputable def leaf3839InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf3839LocalValidity :
    LeafFacts leaf3839Box leaf3839Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3839Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358722559/34357262336) }) = true
      norm_num [leaf3839Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3839CertificateValid :
    WideCertificateValid leaf3839Box leaf3839Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk82ValidityFacts chi68ValidityFacts
    leaf3839LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3839CoverageChecked :
    coverageCheck (innerAD leaf3839Box) leaf3839InnerLog = true := by
  rfl'

private theorem leaf3839InnerLogValid :
    leaf3839InnerLog.Valid 8 (innerAD leaf3839Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf3839CoverageChecked

private noncomputable def leaf3839InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629437/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3839InputLogOnePlusV_eq :
    leaf3839InputLogOnePlusV = outerEnclosure 24
      (leaf3839Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3839RoundedFacts : LeafRoundedFacts 8
    leaf3839Certificate.logOnePlusV leaf3839InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3839InputLogOnePlusV_eq }

private noncomputable def leaf3839Inputs : Inputs :=
  inputsOfCaches globalInput sk82RoundedInputs
    chi68InputQChi innerPair249Input
    leaf3839InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3839LowerChecked :
    lowerCheck 24 leaf3839Box leaf3839Inputs = true := by
  rfl'

private theorem leaf3839CoversExact : CoversExact 8
    leaf3839Box leaf3839Certificate leaf3839InnerLog leaf3839Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk82RoundedFacts chi68RoundedFacts
    innerPair249RoundedFacts leaf3839RoundedFacts (by rfl)

private theorem leaf3839FlatSound : Sound leaf3839Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3839CertificateValid
    leaf3839InnerLogValid leaf3839CoversExact leaf3839LowerChecked

private noncomputable def leaf3840Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (77/32), chiLo := (31/64), chiHi := (1/2) }

private noncomputable def leaf3840Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217945/134217728) }, vSqrt := { lower := (65531/65536), upper := (34358722559/34357215232) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (288578137/268435456) }, upper := { exponent := 1, mantissa := (141/128) } }, logOuter := sk81LogOuterCertificate, logK := sk81LogKCertificate, logChi := chi69LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68715937791/68714430464) } }, logDArg := sk81LogDArgCertificate }

private noncomputable def leaf3840InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf3840LocalValidity :
    LeafFacts leaf3840Box leaf3840Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3840Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358722559/34357215232) }) = true
      norm_num [leaf3840Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3840CertificateValid :
    WideCertificateValid leaf3840Box leaf3840Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk81ValidityFacts chi69ValidityFacts
    leaf3840LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3840CoverageChecked :
    coverageCheck (innerAD leaf3840Box) leaf3840InnerLog = true := by
  rfl'

private theorem leaf3840InnerLogValid :
    leaf3840InnerLog.Valid 8 (innerAD leaf3840Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf3840CoverageChecked

private noncomputable def leaf3840InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629449/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3840InputLogOnePlusV_eq :
    leaf3840InputLogOnePlusV = outerEnclosure 24
      (leaf3840Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3840RoundedFacts : LeafRoundedFacts 8
    leaf3840Certificate.logOnePlusV leaf3840InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3840InputLogOnePlusV_eq }

private noncomputable def leaf3840Inputs : Inputs :=
  inputsOfCaches globalInput sk81RoundedInputs
    chi69InputQChi innerPair250Input
    leaf3840InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3840LowerChecked :
    lowerCheck 24 leaf3840Box leaf3840Inputs = true := by
  rfl'

private theorem leaf3840CoversExact : CoversExact 8
    leaf3840Box leaf3840Certificate leaf3840InnerLog leaf3840Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk81RoundedFacts chi69RoundedFacts
    innerPair250RoundedFacts leaf3840RoundedFacts (by rfl)

private theorem leaf3840FlatSound : Sound leaf3840Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3840CertificateValid
    leaf3840InnerLogValid leaf3840CoversExact leaf3840LowerChecked

private noncomputable def leaf3841Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (77/32), kHi := (39/16), chiLo := (31/64), chiHi := (1/2) }

private noncomputable def leaf3841Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217947/134217728) }, vSqrt := { lower := (65531/65536), upper := (34358722559/34357182464) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (290609627/268435456) }, upper := { exponent := 1, mantissa := (71/64) } }, logOuter := sk82LogOuterCertificate, logK := sk82LogKCertificate, logChi := chi69LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68715905023/68714364928) } }, logDArg := sk82LogDArgCertificate }

private noncomputable def leaf3841InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf3841LocalValidity :
    LeafFacts leaf3841Box leaf3841Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3841Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358722559/34357182464) }) = true
      norm_num [leaf3841Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3841CertificateValid :
    WideCertificateValid leaf3841Box leaf3841Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk82ValidityFacts chi69ValidityFacts
    leaf3841LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3841CoverageChecked :
    coverageCheck (innerAD leaf3841Box) leaf3841InnerLog = true := by
  rfl'

private theorem leaf3841InnerLogValid :
    leaf3841InnerLog.Valid 8 (innerAD leaf3841Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf3841CoverageChecked

private noncomputable def leaf3841InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629457/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3841InputLogOnePlusV_eq :
    leaf3841InputLogOnePlusV = outerEnclosure 24
      (leaf3841Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3841RoundedFacts : LeafRoundedFacts 8
    leaf3841Certificate.logOnePlusV leaf3841InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3841InputLogOnePlusV_eq }

private noncomputable def leaf3841Inputs : Inputs :=
  inputsOfCaches globalInput sk82RoundedInputs
    chi69InputQChi innerPair250Input
    leaf3841InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3841LowerChecked :
    lowerCheck 24 leaf3841Box leaf3841Inputs = true := by
  rfl'

private theorem leaf3841CoversExact : CoversExact 8
    leaf3841Box leaf3841Certificate leaf3841InnerLog leaf3841Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk82RoundedFacts chi69RoundedFacts
    innerPair250RoundedFacts leaf3841RoundedFacts (by rfl)

private theorem leaf3841FlatSound : Sound leaf3841Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3841CertificateValid
    leaf3841InnerLogValid leaf3841CoversExact leaf3841LowerChecked

private noncomputable def leaf3842Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (79/32), chiLo := (15/32), chiHi := (31/64) }

private noncomputable def leaf3842Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217947/134217728) }, vSqrt := { lower := (65531/65536), upper := (34358722559/34357230592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (287529623/268435456) }, upper := { exponent := 1, mantissa := (4497/4096) } }, logOuter := sk83LogOuterCertificate, logK := sk83LogKCertificate, logChi := chi68LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68715953151/68714461184) } }, logDArg := sk83LogDArgCertificate }

private noncomputable def leaf3842InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf3842LocalValidity :
    LeafFacts leaf3842Box leaf3842Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3842Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358722559/34357230592) }) = true
      norm_num [leaf3842Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3842CertificateValid :
    WideCertificateValid leaf3842Box leaf3842Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk83ValidityFacts chi68ValidityFacts
    leaf3842LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3842CoverageChecked :
    coverageCheck (innerAD leaf3842Box) leaf3842InnerLog = true := by
  rfl'

private theorem leaf3842InnerLogValid :
    leaf3842InnerLog.Valid 8 (innerAD leaf3842Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf3842CoverageChecked

private noncomputable def leaf3842InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629445/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3842InputLogOnePlusV_eq :
    leaf3842InputLogOnePlusV = outerEnclosure 24
      (leaf3842Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3842RoundedFacts : LeafRoundedFacts 8
    leaf3842Certificate.logOnePlusV leaf3842InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3842InputLogOnePlusV_eq }

private noncomputable def leaf3842Inputs : Inputs :=
  inputsOfCaches globalInput sk83RoundedInputs
    chi68InputQChi innerPair250Input
    leaf3842InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3842LowerChecked :
    lowerCheck 24 leaf3842Box leaf3842Inputs = true := by
  rfl'

private theorem leaf3842CoversExact : CoversExact 8
    leaf3842Box leaf3842Certificate leaf3842InnerLog leaf3842Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk83RoundedFacts chi68RoundedFacts
    innerPair250RoundedFacts leaf3842RoundedFacts (by rfl)

private theorem leaf3842FlatSound : Sound leaf3842Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3842CertificateValid
    leaf3842InnerLogValid leaf3842CoversExact leaf3842LowerChecked

private noncomputable def leaf3843Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (79/32), kHi := (5/2), chiLo := (15/32), chiHi := (31/64) }

private noncomputable def leaf3843Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217949/134217728) }, vSqrt := { lower := (32765/32768), upper := (4908388937/4908171264) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (289495581/268435456) }, upper := { exponent := 1, mantissa := (283/256) } }, logOuter := sk84LogOuterCertificate, logK := sk84LogKCertificate, logChi := chi68LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (9816560201/9816342528) } }, logDArg := sk84LogDArgCertificate }

private noncomputable def leaf3843InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf3843LocalValidity :
    LeafFacts leaf3843Box leaf3843Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3843Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4908388937/4908171264) }) = true
      norm_num [leaf3843Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3843CertificateValid :
    WideCertificateValid leaf3843Box leaf3843Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk84ValidityFacts chi68ValidityFacts
    leaf3843LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3843CoverageChecked :
    coverageCheck (innerAD leaf3843Box) leaf3843InnerLog = true := by
  rfl'

private theorem leaf3843InnerLogValid :
    leaf3843InnerLog.Valid 8 (innerAD leaf3843Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf3843CoverageChecked

private noncomputable def leaf3843InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629453/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3843InputLogOnePlusV_eq :
    leaf3843InputLogOnePlusV = outerEnclosure 24
      (leaf3843Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3843RoundedFacts : LeafRoundedFacts 8
    leaf3843Certificate.logOnePlusV leaf3843InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3843InputLogOnePlusV_eq }

private noncomputable def leaf3843Inputs : Inputs :=
  inputsOfCaches globalInput sk84RoundedInputs
    chi68InputQChi innerPair250Input
    leaf3843InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3843LowerChecked :
    lowerCheck 24 leaf3843Box leaf3843Inputs = true := by
  rfl'

private theorem leaf3843CoversExact : CoversExact 8
    leaf3843Box leaf3843Certificate leaf3843InnerLog leaf3843Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk84RoundedFacts chi68RoundedFacts
    innerPair250RoundedFacts leaf3843RoundedFacts (by rfl)

private theorem leaf3843FlatSound : Sound leaf3843Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3843CertificateValid
    leaf3843InnerLogValid leaf3843CoversExact leaf3843LowerChecked

private noncomputable def leaf3844Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (79/32), chiLo := (31/64), chiHi := (1/2) }

private noncomputable def leaf3844Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217949/134217728) }, vSqrt := { lower := (65531/65536), upper := (34358722559/34357149696) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (292641117/268435456) }, upper := { exponent := 1, mantissa := (143/128) } }, logOuter := sk83LogOuterCertificate, logK := sk83LogKCertificate, logChi := chi69LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68715872255/68714299392) } }, logDArg := sk83LogDArgCertificate }

private noncomputable def leaf3844InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf3844LocalValidity :
    LeafFacts leaf3844Box leaf3844Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3844Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358722559/34357149696) }) = true
      norm_num [leaf3844Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3844CertificateValid :
    WideCertificateValid leaf3844Box leaf3844Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk83ValidityFacts chi69ValidityFacts
    leaf3844LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3844CoverageChecked :
    coverageCheck (innerAD leaf3844Box) leaf3844InnerLog = true := by
  rfl'

private theorem leaf3844InnerLogValid :
    leaf3844InnerLog.Valid 8 (innerAD leaf3844Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf3844CoverageChecked

private noncomputable def leaf3844InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629465/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3844InputLogOnePlusV_eq :
    leaf3844InputLogOnePlusV = outerEnclosure 24
      (leaf3844Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3844RoundedFacts : LeafRoundedFacts 8
    leaf3844Certificate.logOnePlusV leaf3844InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3844InputLogOnePlusV_eq }

private noncomputable def leaf3844Inputs : Inputs :=
  inputsOfCaches globalInput sk83RoundedInputs
    chi69InputQChi innerPair250Input
    leaf3844InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3844LowerChecked :
    lowerCheck 24 leaf3844Box leaf3844Inputs = true := by
  rfl'

private theorem leaf3844CoversExact : CoversExact 8
    leaf3844Box leaf3844Certificate leaf3844InnerLog leaf3844Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk83RoundedFacts chi69RoundedFacts
    innerPair250RoundedFacts leaf3844RoundedFacts (by rfl)

private theorem leaf3844FlatSound : Sound leaf3844Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3844CertificateValid
    leaf3844InnerLogValid leaf3844CoversExact leaf3844LowerChecked

private noncomputable def leaf3845Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (79/32), kHi := (5/2), chiLo := (31/64), chiHi := (1/2) }

private noncomputable def leaf3845Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217951/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357116928) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (294672607/268435456) }, upper := { exponent := 1, mantissa := (9/8) } }, logOuter := sk84LogOuterCertificate, logK := sk84LogKCertificate, logChi := chi69LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715839487/68714233856) } }, logDArg := sk84LogDArgCertificate }

private noncomputable def leaf3845InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf3845LocalValidity :
    LeafFacts leaf3845Box leaf3845Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3845Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357116928) }) = true
      norm_num [leaf3845Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3845CertificateValid :
    WideCertificateValid leaf3845Box leaf3845Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk84ValidityFacts chi69ValidityFacts
    leaf3845LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3845CoverageChecked :
    coverageCheck (innerAD leaf3845Box) leaf3845InnerLog = true := by
  rfl'

private theorem leaf3845InnerLogValid :
    leaf3845InnerLog.Valid 8 (innerAD leaf3845Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf3845CoverageChecked

private noncomputable def leaf3845InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629473/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3845InputLogOnePlusV_eq :
    leaf3845InputLogOnePlusV = outerEnclosure 24
      (leaf3845Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3845RoundedFacts : LeafRoundedFacts 8
    leaf3845Certificate.logOnePlusV leaf3845InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3845InputLogOnePlusV_eq }

private noncomputable def leaf3845Inputs : Inputs :=
  inputsOfCaches globalInput sk84RoundedInputs
    chi69InputQChi innerPair256Input
    leaf3845InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3845LowerChecked :
    lowerCheck 24 leaf3845Box leaf3845Inputs = true := by
  rfl'

private theorem leaf3845CoversExact : CoversExact 8
    leaf3845Box leaf3845Certificate leaf3845InnerLog leaf3845Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk84RoundedFacts chi69RoundedFacts
    innerPair256RoundedFacts leaf3845RoundedFacts (by rfl)

private theorem leaf3845FlatSound : Sound leaf3845Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3845CertificateValid
    leaf3845InnerLogValid leaf3845CoversExact leaf3845LowerChecked

private noncomputable def component78Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (3/8), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component78Node0_sound : Sound component78Node0Box :=
  sound_of_literal_split component78Node0Box leaf3783Box leaf3784Box
    .k (73/32) (by rfl) (by rfl)
    leaf3783FlatSound leaf3784FlatSound

private noncomputable def component78Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (25/64), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component78Node1_sound : Sound component78Node1Box :=
  sound_of_literal_split component78Node1Box leaf3785Box leaf3786Box
    .k (73/32) (by rfl) (by rfl)
    leaf3785FlatSound leaf3786FlatSound

private noncomputable def component78Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (3/8), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component78Node2_sound : Sound component78Node2Box :=
  sound_of_literal_split component78Node2Box component78Node0Box component78Node1Box
    .chi (25/64) (by rfl) (by rfl)
    component78Node0_sound component78Node1_sound

private noncomputable def component78Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (3/8), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component78Node3_sound : Sound component78Node3Box :=
  sound_of_literal_split component78Node3Box leaf3787Box leaf3788Box
    .k (75/32) (by rfl) (by rfl)
    leaf3787FlatSound leaf3788FlatSound

private noncomputable def component78Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (25/64), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component78Node4_sound : Sound component78Node4Box :=
  sound_of_literal_split component78Node4Box leaf3789Box leaf3790Box
    .k (75/32) (by rfl) (by rfl)
    leaf3789FlatSound leaf3790FlatSound

private noncomputable def component78Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (3/8), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component78Node5_sound : Sound component78Node5Box :=
  sound_of_literal_split component78Node5Box component78Node3Box component78Node4Box
    .chi (25/64) (by rfl) (by rfl)
    component78Node3_sound component78Node4_sound

private noncomputable def component78Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (3/8), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component78Node6_sound : Sound component78Node6Box :=
  sound_of_literal_split component78Node6Box component78Node2Box component78Node5Box
    .k (37/16) (by rfl) (by rfl)
    component78Node2_sound component78Node5_sound

private noncomputable def component78Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (13/32), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component78Node7_sound : Sound component78Node7Box :=
  sound_of_literal_split component78Node7Box leaf3791Box leaf3792Box
    .k (73/32) (by rfl) (by rfl)
    leaf3791FlatSound leaf3792FlatSound

private noncomputable def component78Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (27/64), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component78Node8_sound : Sound component78Node8Box :=
  sound_of_literal_split component78Node8Box leaf3793Box leaf3794Box
    .k (73/32) (by rfl) (by rfl)
    leaf3793FlatSound leaf3794FlatSound

private noncomputable def component78Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (13/32), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component78Node9_sound : Sound component78Node9Box :=
  sound_of_literal_split component78Node9Box component78Node7Box component78Node8Box
    .chi (27/64) (by rfl) (by rfl)
    component78Node7_sound component78Node8_sound

private noncomputable def component78Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (13/32), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component78Node10_sound : Sound component78Node10Box :=
  sound_of_literal_split component78Node10Box leaf3795Box leaf3796Box
    .k (75/32) (by rfl) (by rfl)
    leaf3795FlatSound leaf3796FlatSound

private noncomputable def component78Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (27/64), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component78Node11_sound : Sound component78Node11Box :=
  sound_of_literal_split component78Node11Box leaf3797Box leaf3798Box
    .k (75/32) (by rfl) (by rfl)
    leaf3797FlatSound leaf3798FlatSound

private noncomputable def component78Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (13/32), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component78Node12_sound : Sound component78Node12Box :=
  sound_of_literal_split component78Node12Box component78Node10Box component78Node11Box
    .chi (27/64) (by rfl) (by rfl)
    component78Node10_sound component78Node11_sound

private noncomputable def component78Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (13/32), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component78Node13_sound : Sound component78Node13Box :=
  sound_of_literal_split component78Node13Box component78Node9Box component78Node12Box
    .k (37/16) (by rfl) (by rfl)
    component78Node9_sound component78Node12_sound

private noncomputable def component78Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (3/8), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component78Node14_sound : Sound component78Node14Box :=
  sound_of_literal_split component78Node14Box component78Node6Box component78Node13Box
    .chi (13/32) (by rfl) (by rfl)
    component78Node6_sound component78Node13_sound

private noncomputable def component78Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (3/8), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component78Node15_sound : Sound component78Node15Box :=
  sound_of_literal_split component78Node15Box leaf3799Box leaf3800Box
    .k (77/32) (by rfl) (by rfl)
    leaf3799FlatSound leaf3800FlatSound

private noncomputable def component78Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (25/64), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component78Node16_sound : Sound component78Node16Box :=
  sound_of_literal_split component78Node16Box leaf3801Box leaf3802Box
    .k (77/32) (by rfl) (by rfl)
    leaf3801FlatSound leaf3802FlatSound

private noncomputable def component78Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (3/8), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component78Node17_sound : Sound component78Node17Box :=
  sound_of_literal_split component78Node17Box component78Node15Box component78Node16Box
    .chi (25/64) (by rfl) (by rfl)
    component78Node15_sound component78Node16_sound

private noncomputable def component78Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (3/8), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component78Node18_sound : Sound component78Node18Box :=
  sound_of_literal_split component78Node18Box leaf3803Box leaf3804Box
    .k (79/32) (by rfl) (by rfl)
    leaf3803FlatSound leaf3804FlatSound

private noncomputable def component78Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (25/64), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component78Node19_sound : Sound component78Node19Box :=
  sound_of_literal_split component78Node19Box leaf3805Box leaf3806Box
    .k (79/32) (by rfl) (by rfl)
    leaf3805FlatSound leaf3806FlatSound

private noncomputable def component78Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (3/8), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component78Node20_sound : Sound component78Node20Box :=
  sound_of_literal_split component78Node20Box component78Node18Box component78Node19Box
    .chi (25/64) (by rfl) (by rfl)
    component78Node18_sound component78Node19_sound

private noncomputable def component78Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (3/8), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component78Node21_sound : Sound component78Node21Box :=
  sound_of_literal_split component78Node21Box component78Node17Box component78Node20Box
    .k (39/16) (by rfl) (by rfl)
    component78Node17_sound component78Node20_sound

private noncomputable def component78Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (13/32), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component78Node22_sound : Sound component78Node22Box :=
  sound_of_literal_split component78Node22Box leaf3807Box leaf3808Box
    .k (77/32) (by rfl) (by rfl)
    leaf3807FlatSound leaf3808FlatSound

private noncomputable def component78Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (27/64), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component78Node23_sound : Sound component78Node23Box :=
  sound_of_literal_split component78Node23Box leaf3809Box leaf3810Box
    .k (77/32) (by rfl) (by rfl)
    leaf3809FlatSound leaf3810FlatSound

private noncomputable def component78Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (13/32), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component78Node24_sound : Sound component78Node24Box :=
  sound_of_literal_split component78Node24Box component78Node22Box component78Node23Box
    .chi (27/64) (by rfl) (by rfl)
    component78Node22_sound component78Node23_sound

private noncomputable def component78Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (13/32), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component78Node25_sound : Sound component78Node25Box :=
  sound_of_literal_split component78Node25Box leaf3811Box leaf3812Box
    .k (79/32) (by rfl) (by rfl)
    leaf3811FlatSound leaf3812FlatSound

private noncomputable def component78Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (27/64), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component78Node26_sound : Sound component78Node26Box :=
  sound_of_literal_split component78Node26Box leaf3813Box leaf3814Box
    .k (79/32) (by rfl) (by rfl)
    leaf3813FlatSound leaf3814FlatSound

private noncomputable def component78Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (13/32), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component78Node27_sound : Sound component78Node27Box :=
  sound_of_literal_split component78Node27Box component78Node25Box component78Node26Box
    .chi (27/64) (by rfl) (by rfl)
    component78Node25_sound component78Node26_sound

private noncomputable def component78Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (13/32), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component78Node28_sound : Sound component78Node28Box :=
  sound_of_literal_split component78Node28Box component78Node24Box component78Node27Box
    .k (39/16) (by rfl) (by rfl)
    component78Node24_sound component78Node27_sound

private noncomputable def component78Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (3/8), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component78Node29_sound : Sound component78Node29Box :=
  sound_of_literal_split component78Node29Box component78Node21Box component78Node28Box
    .chi (13/32) (by rfl) (by rfl)
    component78Node21_sound component78Node28_sound

private noncomputable def component78Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (5/2), chiLo := (3/8), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component78Node30_sound : Sound component78Node30Box :=
  sound_of_literal_split component78Node30Box component78Node14Box component78Node29Box
    .k (19/8) (by rfl) (by rfl)
    component78Node14_sound component78Node29_sound

private noncomputable def component78Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (7/16), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component78Node31_sound : Sound component78Node31Box :=
  sound_of_literal_split component78Node31Box leaf3815Box leaf3816Box
    .k (73/32) (by rfl) (by rfl)
    leaf3815FlatSound leaf3816FlatSound

private noncomputable def component78Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (29/64), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component78Node32_sound : Sound component78Node32Box :=
  sound_of_literal_split component78Node32Box leaf3817Box leaf3818Box
    .k (73/32) (by rfl) (by rfl)
    leaf3817FlatSound leaf3818FlatSound

private noncomputable def component78Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (7/16), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component78Node33_sound : Sound component78Node33Box :=
  sound_of_literal_split component78Node33Box component78Node31Box component78Node32Box
    .chi (29/64) (by rfl) (by rfl)
    component78Node31_sound component78Node32_sound

private noncomputable def component78Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (7/16), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component78Node34_sound : Sound component78Node34Box :=
  sound_of_literal_split component78Node34Box leaf3819Box leaf3820Box
    .k (75/32) (by rfl) (by rfl)
    leaf3819FlatSound leaf3820FlatSound

private noncomputable def component78Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (29/64), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component78Node35_sound : Sound component78Node35Box :=
  sound_of_literal_split component78Node35Box leaf3821Box leaf3822Box
    .k (75/32) (by rfl) (by rfl)
    leaf3821FlatSound leaf3822FlatSound

private noncomputable def component78Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (7/16), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component78Node36_sound : Sound component78Node36Box :=
  sound_of_literal_split component78Node36Box component78Node34Box component78Node35Box
    .chi (29/64) (by rfl) (by rfl)
    component78Node34_sound component78Node35_sound

private noncomputable def component78Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (7/16), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component78Node37_sound : Sound component78Node37Box :=
  sound_of_literal_split component78Node37Box component78Node33Box component78Node36Box
    .k (37/16) (by rfl) (by rfl)
    component78Node33_sound component78Node36_sound

private noncomputable def component78Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (15/32), chiHi := (31/64) }

set_option maxRecDepth 1000000 in
private theorem component78Node38_sound : Sound component78Node38Box :=
  sound_of_literal_split component78Node38Box leaf3823Box leaf3824Box
    .k (73/32) (by rfl) (by rfl)
    leaf3823FlatSound leaf3824FlatSound

private noncomputable def component78Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (15/32), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component78Node39_sound : Sound component78Node39Box :=
  sound_of_literal_split component78Node39Box component78Node38Box leaf3825Box
    .chi (31/64) (by rfl) (by rfl)
    component78Node38_sound leaf3825FlatSound

private noncomputable def component78Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (15/32), chiHi := (31/64) }

set_option maxRecDepth 1000000 in
private theorem component78Node40_sound : Sound component78Node40Box :=
  sound_of_literal_split component78Node40Box leaf3826Box leaf3827Box
    .k (75/32) (by rfl) (by rfl)
    leaf3826FlatSound leaf3827FlatSound

private noncomputable def component78Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (31/64), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component78Node41_sound : Sound component78Node41Box :=
  sound_of_literal_split component78Node41Box leaf3828Box leaf3829Box
    .k (75/32) (by rfl) (by rfl)
    leaf3828FlatSound leaf3829FlatSound

private noncomputable def component78Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (15/32), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component78Node42_sound : Sound component78Node42Box :=
  sound_of_literal_split component78Node42Box component78Node40Box component78Node41Box
    .chi (31/64) (by rfl) (by rfl)
    component78Node40_sound component78Node41_sound

private noncomputable def component78Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (15/32), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component78Node43_sound : Sound component78Node43Box :=
  sound_of_literal_split component78Node43Box component78Node39Box component78Node42Box
    .k (37/16) (by rfl) (by rfl)
    component78Node39_sound component78Node42_sound

private noncomputable def component78Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (7/16), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component78Node44_sound : Sound component78Node44Box :=
  sound_of_literal_split component78Node44Box component78Node37Box component78Node43Box
    .chi (15/32) (by rfl) (by rfl)
    component78Node37_sound component78Node43_sound

private noncomputable def component78Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (7/16), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component78Node45_sound : Sound component78Node45Box :=
  sound_of_literal_split component78Node45Box leaf3830Box leaf3831Box
    .k (77/32) (by rfl) (by rfl)
    leaf3830FlatSound leaf3831FlatSound

private noncomputable def component78Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (29/64), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component78Node46_sound : Sound component78Node46Box :=
  sound_of_literal_split component78Node46Box leaf3832Box leaf3833Box
    .k (77/32) (by rfl) (by rfl)
    leaf3832FlatSound leaf3833FlatSound

private noncomputable def component78Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (7/16), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component78Node47_sound : Sound component78Node47Box :=
  sound_of_literal_split component78Node47Box component78Node45Box component78Node46Box
    .chi (29/64) (by rfl) (by rfl)
    component78Node45_sound component78Node46_sound

private noncomputable def component78Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (7/16), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component78Node48_sound : Sound component78Node48Box :=
  sound_of_literal_split component78Node48Box leaf3834Box leaf3835Box
    .k (79/32) (by rfl) (by rfl)
    leaf3834FlatSound leaf3835FlatSound

private noncomputable def component78Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (29/64), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component78Node49_sound : Sound component78Node49Box :=
  sound_of_literal_split component78Node49Box leaf3836Box leaf3837Box
    .k (79/32) (by rfl) (by rfl)
    leaf3836FlatSound leaf3837FlatSound

private noncomputable def component78Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (7/16), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component78Node50_sound : Sound component78Node50Box :=
  sound_of_literal_split component78Node50Box component78Node48Box component78Node49Box
    .chi (29/64) (by rfl) (by rfl)
    component78Node48_sound component78Node49_sound

private noncomputable def component78Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (7/16), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component78Node51_sound : Sound component78Node51Box :=
  sound_of_literal_split component78Node51Box component78Node47Box component78Node50Box
    .k (39/16) (by rfl) (by rfl)
    component78Node47_sound component78Node50_sound

private noncomputable def component78Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (15/32), chiHi := (31/64) }

set_option maxRecDepth 1000000 in
private theorem component78Node52_sound : Sound component78Node52Box :=
  sound_of_literal_split component78Node52Box leaf3838Box leaf3839Box
    .k (77/32) (by rfl) (by rfl)
    leaf3838FlatSound leaf3839FlatSound

private noncomputable def component78Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (31/64), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component78Node53_sound : Sound component78Node53Box :=
  sound_of_literal_split component78Node53Box leaf3840Box leaf3841Box
    .k (77/32) (by rfl) (by rfl)
    leaf3840FlatSound leaf3841FlatSound

private noncomputable def component78Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (15/32), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component78Node54_sound : Sound component78Node54Box :=
  sound_of_literal_split component78Node54Box component78Node52Box component78Node53Box
    .chi (31/64) (by rfl) (by rfl)
    component78Node52_sound component78Node53_sound

private noncomputable def component78Node55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (15/32), chiHi := (31/64) }

set_option maxRecDepth 1000000 in
private theorem component78Node55_sound : Sound component78Node55Box :=
  sound_of_literal_split component78Node55Box leaf3842Box leaf3843Box
    .k (79/32) (by rfl) (by rfl)
    leaf3842FlatSound leaf3843FlatSound

private noncomputable def component78Node56Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (31/64), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component78Node56_sound : Sound component78Node56Box :=
  sound_of_literal_split component78Node56Box leaf3844Box leaf3845Box
    .k (79/32) (by rfl) (by rfl)
    leaf3844FlatSound leaf3845FlatSound

private noncomputable def component78Node57Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (15/32), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component78Node57_sound : Sound component78Node57Box :=
  sound_of_literal_split component78Node57Box component78Node55Box component78Node56Box
    .chi (31/64) (by rfl) (by rfl)
    component78Node55_sound component78Node56_sound

private noncomputable def component78Node58Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (15/32), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component78Node58_sound : Sound component78Node58Box :=
  sound_of_literal_split component78Node58Box component78Node54Box component78Node57Box
    .k (39/16) (by rfl) (by rfl)
    component78Node54_sound component78Node57_sound

private noncomputable def component78Node59Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (7/16), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component78Node59_sound : Sound component78Node59Box :=
  sound_of_literal_split component78Node59Box component78Node51Box component78Node58Box
    .chi (15/32) (by rfl) (by rfl)
    component78Node51_sound component78Node58_sound

private noncomputable def component78Node60Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (5/2), chiLo := (7/16), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component78Node60_sound : Sound component78Node60Box :=
  sound_of_literal_split component78Node60Box component78Node44Box component78Node59Box
    .k (19/8) (by rfl) (by rfl)
    component78Node44_sound component78Node59_sound

noncomputable def component78Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (5/2), chiLo := (3/8), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
theorem component78_sound : Sound component78Box :=
  sound_of_literal_split component78Box component78Node30Box component78Node60Box
    .chi (7/16) (by rfl) (by rfl)
    component78Node30_sound component78Node60_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
