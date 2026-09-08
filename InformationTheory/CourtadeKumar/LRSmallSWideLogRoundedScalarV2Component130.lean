import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch7
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch11
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch12
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch5
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

private noncomputable def leaf6482Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (3/4), chiHi := (25/32) }

private noncomputable def leaf6482Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554563/33554432) }, vSqrt := { lower := (32765/32768), upper := (2863142229/2862961664) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (96432255/67108864) }, upper := { exponent := 1, mantissa := (1537/1024) } }, logOuter := sk89LogOuterCertificate, logK := sk89LogKCertificate, logChi := chi88LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (5726103893/5725923328) } }, logDArg := sk89LogDArgCertificate }

private noncomputable def leaf6482InnerLog : WideLogData :=
  innerPair782Data

set_option maxRecDepth 1000000 in
private theorem leaf6482LocalValidity :
    LeafFacts leaf6482Box leaf6482Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6482Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (2863142229/2862961664) }) = true
      norm_num [leaf6482Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6482CertificateValid :
    WideCertificateValid leaf6482Box leaf6482Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk89ValidityFacts chi88ValidityFacts
    leaf6482LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6482CoverageChecked :
    coverageCheck (innerAD leaf6482Box) leaf6482InnerLog = true := by
  rfl'

private theorem leaf6482InnerLogValid :
    leaf6482InnerLog.Valid 8 (innerAD leaf6482Box) :=
  wideLogDataValid_of_cachedCheck endpoint490PositiveFacts
    endpoint491PositiveFacts.valid leaf6482CoverageChecked

private noncomputable def leaf6482InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814805/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6482InputLogOnePlusV_eq :
    leaf6482InputLogOnePlusV = outerEnclosure 24
      (leaf6482Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6482RoundedFacts : LeafRoundedFacts 8
    leaf6482Certificate.logOnePlusV leaf6482InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6482InputLogOnePlusV_eq }

private noncomputable def leaf6482Inputs : Inputs :=
  inputsOfCaches globalInput sk89RoundedInputs
    chi88InputQChi innerPair782Input
    leaf6482InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6482LowerChecked :
    lowerCheck 24 leaf6482Box leaf6482Inputs = true := by
  rfl'

private theorem leaf6482CoversExact : CoversExact 8
    leaf6482Box leaf6482Certificate leaf6482InnerLog leaf6482Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk89RoundedFacts chi88RoundedFacts
    innerPair782RoundedFacts leaf6482RoundedFacts (by rfl)

private theorem leaf6482FlatSound : Sound leaf6482Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6482CertificateValid
    leaf6482InnerLogValid leaf6482CoversExact leaf6482LowerChecked

private noncomputable def leaf6483Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (3/4), chiHi := (25/32) }

private noncomputable def leaf6483Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554565/33554432) }, vSqrt := { lower := (32765/32768), upper := (8589426687/8588859392) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (98005021/67108864) }, upper := { exponent := 1, mantissa := (781/512) } }, logOuter := sk90LogOuterCertificate, logK := sk90LogKCertificate, logChi := chi88LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (17178286079/17177718784) } }, logDArg := sk90LogDArgCertificate }

private noncomputable def leaf6483InnerLog : WideLogData :=
  innerPair374Data

set_option maxRecDepth 1000000 in
private theorem leaf6483LocalValidity :
    LeafFacts leaf6483Box leaf6483Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6483Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8589426687/8588859392) }) = true
      norm_num [leaf6483Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6483CertificateValid :
    WideCertificateValid leaf6483Box leaf6483Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk90ValidityFacts chi88ValidityFacts
    leaf6483LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6483CoverageChecked :
    coverageCheck (innerAD leaf6483Box) leaf6483InnerLog = true := by
  rfl'

private theorem leaf6483InnerLogValid :
    leaf6483InnerLog.Valid 8 (innerAD leaf6483Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint482PositiveFacts.valid leaf6483CoverageChecked

private noncomputable def leaf6483InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629635/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6483InputLogOnePlusV_eq :
    leaf6483InputLogOnePlusV = outerEnclosure 24
      (leaf6483Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6483RoundedFacts : LeafRoundedFacts 8
    leaf6483Certificate.logOnePlusV leaf6483InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6483InputLogOnePlusV_eq }

private noncomputable def leaf6483Inputs : Inputs :=
  inputsOfCaches globalInput sk90RoundedInputs
    chi88InputQChi innerPair374Input
    leaf6483InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6483LowerChecked :
    lowerCheck 24 leaf6483Box leaf6483Inputs = true := by
  rfl'

private theorem leaf6483CoversExact : CoversExact 8
    leaf6483Box leaf6483Certificate leaf6483InnerLog leaf6483Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk90RoundedFacts chi88RoundedFacts
    innerPair374RoundedFacts leaf6483RoundedFacts (by rfl)

private theorem leaf6483FlatSound : Sound leaf6483Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6483CertificateValid
    leaf6483InnerLogValid leaf6483CoversExact leaf6483LowerChecked

private noncomputable def leaf6484Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (25/32), chiHi := (13/16) }

private noncomputable def leaf6484Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554565/33554432) }, vSqrt := { lower := (32765/32768), upper := (8589426687/8588843008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (99053533/67108864) }, upper := { exponent := 1, mantissa := (789/512) } }, logOuter := sk89LogOuterCertificate, logK := sk89LogKCertificate, logChi := chi89LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (17178269695/17177686016) } }, logDArg := sk89LogDArgCertificate }

private noncomputable def leaf6484InnerLog : WideLogData :=
  innerPair377Data

set_option maxRecDepth 1000000 in
private theorem leaf6484LocalValidity :
    LeafFacts leaf6484Box leaf6484Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6484Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8589426687/8588843008) }) = true
      norm_num [leaf6484Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6484CertificateValid :
    WideCertificateValid leaf6484Box leaf6484Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk89ValidityFacts chi89ValidityFacts
    leaf6484LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6484CoverageChecked :
    coverageCheck (innerAD leaf6484Box) leaf6484InnerLog = true := by
  rfl'

private theorem leaf6484InnerLogValid :
    leaf6484InnerLog.Valid 8 (innerAD leaf6484Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint483PositiveFacts.valid leaf6484CoverageChecked

private noncomputable def leaf6484InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629651/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6484InputLogOnePlusV_eq :
    leaf6484InputLogOnePlusV = outerEnclosure 24
      (leaf6484Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6484RoundedFacts : LeafRoundedFacts 8
    leaf6484Certificate.logOnePlusV leaf6484InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6484InputLogOnePlusV_eq }

private noncomputable def leaf6484Inputs : Inputs :=
  inputsOfCaches globalInput sk89RoundedInputs
    chi89InputQChi innerPair377Input
    leaf6484InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6484LowerChecked :
    lowerCheck 24 leaf6484Box leaf6484Inputs = true := by
  rfl'

private theorem leaf6484CoversExact : CoversExact 8
    leaf6484Box leaf6484Certificate leaf6484InnerLog leaf6484Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk89RoundedFacts chi89RoundedFacts
    innerPair377RoundedFacts leaf6484RoundedFacts (by rfl)

private theorem leaf6484FlatSound : Sound leaf6484Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6484CertificateValid
    leaf6484InnerLogValid leaf6484CoversExact leaf6484LowerChecked

private noncomputable def leaf6485Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (25/32), chiHi := (13/16) }

private noncomputable def leaf6485Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554567/33554432) }, vSqrt := { lower := (32765/32768), upper := (8589426687/8588816384) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (100691831/67108864) }, upper := { exponent := 1, mantissa := (401/256) } }, logOuter := sk90LogOuterCertificate, logK := sk90LogKCertificate, logChi := chi89LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (17178243071/17177632768) } }, logDArg := sk90LogDArgCertificate }

private noncomputable def leaf6485InnerLog : WideLogData :=
  innerPair383Data

set_option maxRecDepth 1000000 in
private theorem leaf6485LocalValidity :
    LeafFacts leaf6485Box leaf6485Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6485Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8589426687/8588816384) }) = true
      norm_num [leaf6485Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6485CertificateValid :
    WideCertificateValid leaf6485Box leaf6485Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk90ValidityFacts chi89ValidityFacts
    leaf6485LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6485CoverageChecked :
    coverageCheck (innerAD leaf6485Box) leaf6485InnerLog = true := by
  rfl'

private theorem leaf6485InnerLogValid :
    leaf6485InnerLog.Valid 8 (innerAD leaf6485Box) :=
  wideLogDataValid_of_cachedCheck endpoint99PositiveFacts
    endpoint484PositiveFacts.valid leaf6485CoverageChecked

private noncomputable def leaf6485InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629677/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6485InputLogOnePlusV_eq :
    leaf6485InputLogOnePlusV = outerEnclosure 24
      (leaf6485Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6485RoundedFacts : LeafRoundedFacts 8
    leaf6485Certificate.logOnePlusV leaf6485InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6485InputLogOnePlusV_eq }

private noncomputable def leaf6485Inputs : Inputs :=
  inputsOfCaches globalInput sk90RoundedInputs
    chi89InputQChi innerPair383Input
    leaf6485InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6485LowerChecked :
    lowerCheck 24 leaf6485Box leaf6485Inputs = true := by
  rfl'

private theorem leaf6485CoversExact : CoversExact 8
    leaf6485Box leaf6485Certificate leaf6485InnerLog leaf6485Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk90RoundedFacts chi89RoundedFacts
    innerPair383RoundedFacts leaf6485RoundedFacts (by rfl)

private theorem leaf6485FlatSound : Sound leaf6485Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6485CertificateValid
    leaf6485InnerLogValid leaf6485CoversExact leaf6485LowerChecked

private noncomputable def leaf6486Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (3/4), chiHi := (25/32) }

private noncomputable def leaf6486Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554567/33554432) }, vSqrt := { lower := (32765/32768), upper := (8589426687/8588833792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (99577787/67108864) }, upper := { exponent := 1, mantissa := (1587/1024) } }, logOuter := sk91LogOuterCertificate, logK := sk91LogKCertificate, logChi := chi88LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (17178260479/17177667584) } }, logDArg := sk91LogDArgCertificate }

private noncomputable def leaf6486InnerLog : WideLogData :=
  innerPair377Data

set_option maxRecDepth 1000000 in
private theorem leaf6486LocalValidity :
    LeafFacts leaf6486Box leaf6486Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6486Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8589426687/8588833792) }) = true
      norm_num [leaf6486Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6486CertificateValid :
    WideCertificateValid leaf6486Box leaf6486Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk91ValidityFacts chi88ValidityFacts
    leaf6486LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6486CoverageChecked :
    coverageCheck (innerAD leaf6486Box) leaf6486InnerLog = true := by
  rfl'

private theorem leaf6486InnerLogValid :
    leaf6486InnerLog.Valid 8 (innerAD leaf6486Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint483PositiveFacts.valid leaf6486CoverageChecked

private noncomputable def leaf6486InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907415/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6486InputLogOnePlusV_eq :
    leaf6486InputLogOnePlusV = outerEnclosure 24
      (leaf6486Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6486RoundedFacts : LeafRoundedFacts 8
    leaf6486Certificate.logOnePlusV leaf6486InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6486InputLogOnePlusV_eq }

private noncomputable def leaf6486Inputs : Inputs :=
  inputsOfCaches globalInput sk91RoundedInputs
    chi88InputQChi innerPair377Input
    leaf6486InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6486LowerChecked :
    lowerCheck 24 leaf6486Box leaf6486Inputs = true := by
  rfl'

private theorem leaf6486CoversExact : CoversExact 8
    leaf6486Box leaf6486Certificate leaf6486InnerLog leaf6486Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk91RoundedFacts chi88RoundedFacts
    innerPair377RoundedFacts leaf6486RoundedFacts (by rfl)

private theorem leaf6486FlatSound : Sound leaf6486Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6486CertificateValid
    leaf6486InnerLogValid leaf6486CoversExact leaf6486LowerChecked

private noncomputable def leaf6487Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (3/4), chiHi := (25/32) }

private noncomputable def leaf6487Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554569/33554432) }, vSqrt := { lower := (32765/32768), upper := (2863142229/2862936064) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (101150553/67108864) }, upper := { exponent := 1, mantissa := (403/256) } }, logOuter := sk92LogOuterCertificate, logK := sk92LogKCertificate, logChi := chi88LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (5726078293/5725872128) } }, logDArg := sk92LogDArgCertificate }

private noncomputable def leaf6487InnerLog : WideLogData :=
  innerPair384Data

set_option maxRecDepth 1000000 in
private theorem leaf6487LocalValidity :
    LeafFacts leaf6487Box leaf6487Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6487Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (2863142229/2862936064) }) = true
      norm_num [leaf6487Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6487CertificateValid :
    WideCertificateValid leaf6487Box leaf6487Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk92ValidityFacts chi88ValidityFacts
    leaf6487LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6487CoverageChecked :
    coverageCheck (innerAD leaf6487Box) leaf6487InnerLog = true := by
  rfl'

private theorem leaf6487InnerLogValid :
    leaf6487InnerLog.Valid 8 (innerAD leaf6487Box) :=
  wideLogDataValid_of_cachedCheck endpoint99PositiveFacts
    endpoint492PositiveFacts.valid leaf6487CoverageChecked

private noncomputable def leaf6487InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629685/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6487InputLogOnePlusV_eq :
    leaf6487InputLogOnePlusV = outerEnclosure 24
      (leaf6487Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6487RoundedFacts : LeafRoundedFacts 8
    leaf6487Certificate.logOnePlusV leaf6487InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6487InputLogOnePlusV_eq }

private noncomputable def leaf6487Inputs : Inputs :=
  inputsOfCaches globalInput sk92RoundedInputs
    chi88InputQChi innerPair384Input
    leaf6487InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6487LowerChecked :
    lowerCheck 24 leaf6487Box leaf6487Inputs = true := by
  rfl'

private theorem leaf6487CoversExact : CoversExact 8
    leaf6487Box leaf6487Certificate leaf6487InnerLog leaf6487Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk92RoundedFacts chi88RoundedFacts
    innerPair384RoundedFacts leaf6487RoundedFacts (by rfl)

private theorem leaf6487FlatSound : Sound leaf6487Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6487CertificateValid
    leaf6487InnerLogValid leaf6487CoversExact leaf6487LowerChecked

private noncomputable def leaf6488Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (25/32), chiHi := (13/16) }

private noncomputable def leaf6488Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554569/33554432) }, vSqrt := { lower := (32765/32768), upper := (2863142229/2862929920) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (102330129/67108864) }, upper := { exponent := 1, mantissa := (815/512) } }, logOuter := sk91LogOuterCertificate, logK := sk91LogKCertificate, logChi := chi89LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (5726072149/5725859840) } }, logDArg := sk91LogDArgCertificate }

private noncomputable def leaf6488InnerLog : WideLogData :=
  innerPair383Data

set_option maxRecDepth 1000000 in
private theorem leaf6488LocalValidity :
    LeafFacts leaf6488Box leaf6488Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6488Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (2863142229/2862929920) }) = true
      norm_num [leaf6488Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6488CertificateValid :
    WideCertificateValid leaf6488Box leaf6488Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk91ValidityFacts chi89ValidityFacts
    leaf6488LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6488CoverageChecked :
    coverageCheck (innerAD leaf6488Box) leaf6488InnerLog = true := by
  rfl'

private theorem leaf6488InnerLogValid :
    leaf6488InnerLog.Valid 8 (innerAD leaf6488Box) :=
  wideLogDataValid_of_cachedCheck endpoint99PositiveFacts
    endpoint484PositiveFacts.valid leaf6488CoverageChecked

private noncomputable def leaf6488InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629703/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6488InputLogOnePlusV_eq :
    leaf6488InputLogOnePlusV = outerEnclosure 24
      (leaf6488Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6488RoundedFacts : LeafRoundedFacts 8
    leaf6488Certificate.logOnePlusV leaf6488InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6488InputLogOnePlusV_eq }

private noncomputable def leaf6488Inputs : Inputs :=
  inputsOfCaches globalInput sk91RoundedInputs
    chi89InputQChi innerPair383Input
    leaf6488InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6488LowerChecked :
    lowerCheck 24 leaf6488Box leaf6488Inputs = true := by
  rfl'

private theorem leaf6488CoversExact : CoversExact 8
    leaf6488Box leaf6488Certificate leaf6488InnerLog leaf6488Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk91RoundedFacts chi89RoundedFacts
    innerPair383RoundedFacts leaf6488RoundedFacts (by rfl)

private theorem leaf6488FlatSound : Sound leaf6488Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6488CertificateValid
    leaf6488InnerLogValid leaf6488CoversExact leaf6488LowerChecked

private noncomputable def leaf6489Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (25/32), chiHi := (13/16) }

private noncomputable def leaf6489Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554571/33554432) }, vSqrt := { lower := (32765/32768), upper := (8589426687/8588763136) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (103968427/67108864) }, upper := { exponent := 1, mantissa := (207/128) } }, logOuter := sk92LogOuterCertificate, logK := sk92LogKCertificate, logChi := chi89LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (17178189823/17177526272) } }, logDArg := sk92LogDArgCertificate }

private noncomputable def leaf6489InnerLog : WideLogData :=
  innerPair745Data

set_option maxRecDepth 1000000 in
private theorem leaf6489LocalValidity :
    LeafFacts leaf6489Box leaf6489Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6489Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8589426687/8588763136) }) = true
      norm_num [leaf6489Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6489CertificateValid :
    WideCertificateValid leaf6489Box leaf6489Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk92ValidityFacts chi89ValidityFacts
    leaf6489LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6489CoverageChecked :
    coverageCheck (innerAD leaf6489Box) leaf6489InnerLog = true := by
  rfl'

private theorem leaf6489InnerLogValid :
    leaf6489InnerLog.Valid 8 (innerAD leaf6489Box) :=
  wideLogDataValid_of_cachedCheck endpoint482PositiveFacts
    endpoint485PositiveFacts.valid leaf6489CoverageChecked

private noncomputable def leaf6489InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629729/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6489InputLogOnePlusV_eq :
    leaf6489InputLogOnePlusV = outerEnclosure 24
      (leaf6489Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6489RoundedFacts : LeafRoundedFacts 8
    leaf6489Certificate.logOnePlusV leaf6489InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6489InputLogOnePlusV_eq }

private noncomputable def leaf6489Inputs : Inputs :=
  inputsOfCaches globalInput sk92RoundedInputs
    chi89InputQChi innerPair745Input
    leaf6489InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6489LowerChecked :
    lowerCheck 24 leaf6489Box leaf6489Inputs = true := by
  rfl'

private theorem leaf6489CoversExact : CoversExact 8
    leaf6489Box leaf6489Certificate leaf6489InnerLog leaf6489Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk92RoundedFacts chi89RoundedFacts
    innerPair745RoundedFacts leaf6489RoundedFacts (by rfl)

private theorem leaf6489FlatSound : Sound leaf6489Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6489CertificateValid
    leaf6489InnerLogValid leaf6489CoversExact leaf6489LowerChecked

private noncomputable def leaf6490Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (13/16), chiHi := (27/32) }

private noncomputable def leaf6490Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554567/33554432) }, vSqrt := { lower := (32765/32768), upper := (8589426687/8588801024) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (101674811/67108864) }, upper := { exponent := 1, mantissa := (1619/1024) } }, logOuter := sk89LogOuterCertificate, logK := sk89LogKCertificate, logChi := chi90LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (17178227711/17177602048) } }, logDArg := sk89LogDArgCertificate }

private noncomputable def leaf6490InnerLog : WideLogData :=
  innerPair383Data

set_option maxRecDepth 1000000 in
private theorem leaf6490LocalValidity :
    LeafFacts leaf6490Box leaf6490Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6490Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8589426687/8588801024) }) = true
      norm_num [leaf6490Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6490CertificateValid :
    WideCertificateValid leaf6490Box leaf6490Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk89ValidityFacts chi90ValidityFacts
    leaf6490LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6490CoverageChecked :
    coverageCheck (innerAD leaf6490Box) leaf6490InnerLog = true := by
  rfl'

private theorem leaf6490InnerLogValid :
    leaf6490InnerLog.Valid 8 (innerAD leaf6490Box) :=
  wideLogDataValid_of_cachedCheck endpoint99PositiveFacts
    endpoint484PositiveFacts.valid leaf6490CoverageChecked

private noncomputable def leaf6490InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907423/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6490InputLogOnePlusV_eq :
    leaf6490InputLogOnePlusV = outerEnclosure 24
      (leaf6490Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6490RoundedFacts : LeafRoundedFacts 8
    leaf6490Certificate.logOnePlusV leaf6490InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6490InputLogOnePlusV_eq }

private noncomputable def leaf6490Inputs : Inputs :=
  inputsOfCaches globalInput sk89RoundedInputs
    chi90InputQChi innerPair383Input
    leaf6490InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6490LowerChecked :
    lowerCheck 24 leaf6490Box leaf6490Inputs = true := by
  rfl'

private theorem leaf6490CoversExact : CoversExact 8
    leaf6490Box leaf6490Certificate leaf6490InnerLog leaf6490Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk89RoundedFacts chi90RoundedFacts
    innerPair383RoundedFacts leaf6490RoundedFacts (by rfl)

private theorem leaf6490FlatSound : Sound leaf6490Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6490CertificateValid
    leaf6490InnerLogValid leaf6490CoversExact leaf6490LowerChecked

private noncomputable def leaf6491Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (13/16), chiHi := (27/32) }

private noncomputable def leaf6491Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554569/33554432) }, vSqrt := { lower := (32765/32768), upper := (8589426687/8588773376) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (103378641/67108864) }, upper := { exponent := 1, mantissa := (823/512) } }, logOuter := sk90LogOuterCertificate, logK := sk90LogKCertificate, logChi := chi90LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (17178200063/17177546752) } }, logDArg := sk90LogDArgCertificate }

private noncomputable def leaf6491InnerLog : WideLogData :=
  innerPair745Data

set_option maxRecDepth 1000000 in
private theorem leaf6491LocalValidity :
    LeafFacts leaf6491Box leaf6491Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6491Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8589426687/8588773376) }) = true
      norm_num [leaf6491Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6491CertificateValid :
    WideCertificateValid leaf6491Box leaf6491Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk90ValidityFacts chi90ValidityFacts
    leaf6491LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6491CoverageChecked :
    coverageCheck (innerAD leaf6491Box) leaf6491InnerLog = true := by
  rfl'

private theorem leaf6491InnerLogValid :
    leaf6491InnerLog.Valid 8 (innerAD leaf6491Box) :=
  wideLogDataValid_of_cachedCheck endpoint482PositiveFacts
    endpoint485PositiveFacts.valid leaf6491CoverageChecked

private noncomputable def leaf6491InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629719/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6491InputLogOnePlusV_eq :
    leaf6491InputLogOnePlusV = outerEnclosure 24
      (leaf6491Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6491RoundedFacts : LeafRoundedFacts 8
    leaf6491Certificate.logOnePlusV leaf6491InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6491InputLogOnePlusV_eq }

private noncomputable def leaf6491Inputs : Inputs :=
  inputsOfCaches globalInput sk90RoundedInputs
    chi90InputQChi innerPair745Input
    leaf6491InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6491LowerChecked :
    lowerCheck 24 leaf6491Box leaf6491Inputs = true := by
  rfl'

private theorem leaf6491CoversExact : CoversExact 8
    leaf6491Box leaf6491Certificate leaf6491InnerLog leaf6491Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk90RoundedFacts chi90RoundedFacts
    innerPair745RoundedFacts leaf6491RoundedFacts (by rfl)

private theorem leaf6491FlatSound : Sound leaf6491Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6491CertificateValid
    leaf6491InnerLogValid leaf6491CoversExact leaf6491LowerChecked

private noncomputable def leaf6492Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (27/32), chiHi := (7/8) }

private noncomputable def leaf6492Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554569/33554432) }, vSqrt := { lower := (32765/32768), upper := (954380743/954306560) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (104296089/67108864) }, upper := { exponent := 1, mantissa := (415/256) } }, logOuter := sk89LogOuterCertificate, logK := sk89LogKCertificate, logChi := chi91LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (1908687303/1908613120) } }, logDArg := sk89LogDArgCertificate }

private noncomputable def leaf6492InnerLog : WideLogData :=
  innerPair745Data

set_option maxRecDepth 1000000 in
private theorem leaf6492LocalValidity :
    LeafFacts leaf6492Box leaf6492Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6492Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (954380743/954306560) }) = true
      norm_num [leaf6492Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6492CertificateValid :
    WideCertificateValid leaf6492Box leaf6492Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk89ValidityFacts chi91ValidityFacts
    leaf6492LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6492CoverageChecked :
    coverageCheck (innerAD leaf6492Box) leaf6492InnerLog = true := by
  rfl'

private theorem leaf6492InnerLogValid :
    leaf6492InnerLog.Valid 8 (innerAD leaf6492Box) :=
  wideLogDataValid_of_cachedCheck endpoint482PositiveFacts
    endpoint485PositiveFacts.valid leaf6492CoverageChecked

private noncomputable def leaf6492InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629733/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6492InputLogOnePlusV_eq :
    leaf6492InputLogOnePlusV = outerEnclosure 24
      (leaf6492Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6492RoundedFacts : LeafRoundedFacts 8
    leaf6492Certificate.logOnePlusV leaf6492InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6492InputLogOnePlusV_eq }

private noncomputable def leaf6492Inputs : Inputs :=
  inputsOfCaches globalInput sk89RoundedInputs
    chi91InputQChi innerPair745Input
    leaf6492InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6492LowerChecked :
    lowerCheck 24 leaf6492Box leaf6492Inputs = true := by
  rfl'

private theorem leaf6492CoversExact : CoversExact 8
    leaf6492Box leaf6492Certificate leaf6492InnerLog leaf6492Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk89RoundedFacts chi91RoundedFacts
    innerPair745RoundedFacts leaf6492RoundedFacts (by rfl)

private theorem leaf6492FlatSound : Sound leaf6492Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6492CertificateValid
    leaf6492InnerLogValid leaf6492CoversExact leaf6492LowerChecked

private noncomputable def leaf6493Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (27/32), chiHi := (7/8) }

private noncomputable def leaf6493Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554571/33554432) }, vSqrt := { lower := (32765/32768), upper := (8589426687/8588730368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (106065451/67108864) }, upper := { exponent := 1, mantissa := (211/128) } }, logOuter := sk90LogOuterCertificate, logK := sk90LogKCertificate, logChi := chi91LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (17178157055/17177460736) } }, logDArg := sk90LogDArgCertificate }

private noncomputable def leaf6493InnerLog : WideLogData :=
  innerPair750Data

set_option maxRecDepth 1000000 in
private theorem leaf6493LocalValidity :
    LeafFacts leaf6493Box leaf6493Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6493Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8589426687/8588730368) }) = true
      norm_num [leaf6493Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6493CertificateValid :
    WideCertificateValid leaf6493Box leaf6493Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk90ValidityFacts chi91ValidityFacts
    leaf6493LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6493CoverageChecked :
    coverageCheck (innerAD leaf6493Box) leaf6493InnerLog = true := by
  rfl'

private theorem leaf6493InnerLogValid :
    leaf6493InnerLog.Valid 8 (innerAD leaf6493Box) :=
  wideLogDataValid_of_cachedCheck endpoint483PositiveFacts
    endpoint486PositiveFacts.valid leaf6493CoverageChecked

private noncomputable def leaf6493InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629761/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6493InputLogOnePlusV_eq :
    leaf6493InputLogOnePlusV = outerEnclosure 24
      (leaf6493Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6493RoundedFacts : LeafRoundedFacts 8
    leaf6493Certificate.logOnePlusV leaf6493InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6493InputLogOnePlusV_eq }

private noncomputable def leaf6493Inputs : Inputs :=
  inputsOfCaches globalInput sk90RoundedInputs
    chi91InputQChi innerPair750Input
    leaf6493InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6493LowerChecked :
    lowerCheck 24 leaf6493Box leaf6493Inputs = true := by
  rfl'

private theorem leaf6493CoversExact : CoversExact 8
    leaf6493Box leaf6493Certificate leaf6493InnerLog leaf6493Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk90RoundedFacts chi91RoundedFacts
    innerPair750RoundedFacts leaf6493RoundedFacts (by rfl)

private theorem leaf6493FlatSound : Sound leaf6493Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6493CertificateValid
    leaf6493InnerLogValid leaf6493CoversExact leaf6493LowerChecked

private noncomputable def leaf6494Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (13/16), chiHi := (27/32) }

private noncomputable def leaf6494Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554571/33554432) }, vSqrt := { lower := (32765/32768), upper := (8589426687/8588745728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (105082471/67108864) }, upper := { exponent := 1, mantissa := (1673/1024) } }, logOuter := sk91LogOuterCertificate, logK := sk91LogKCertificate, logChi := chi90LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (17178172415/17177491456) } }, logDArg := sk91LogDArgCertificate }

private noncomputable def leaf6494InnerLog : WideLogData :=
  innerPair750Data

set_option maxRecDepth 1000000 in
private theorem leaf6494LocalValidity :
    LeafFacts leaf6494Box leaf6494Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6494Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8589426687/8588745728) }) = true
      norm_num [leaf6494Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6494CertificateValid :
    WideCertificateValid leaf6494Box leaf6494Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk91ValidityFacts chi90ValidityFacts
    leaf6494LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6494CoverageChecked :
    coverageCheck (innerAD leaf6494Box) leaf6494InnerLog = true := by
  rfl'

private theorem leaf6494InnerLogValid :
    leaf6494InnerLog.Valid 8 (innerAD leaf6494Box) :=
  wideLogDataValid_of_cachedCheck endpoint483PositiveFacts
    endpoint486PositiveFacts.valid leaf6494CoverageChecked

private noncomputable def leaf6494InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814873/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6494InputLogOnePlusV_eq :
    leaf6494InputLogOnePlusV = outerEnclosure 24
      (leaf6494Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6494RoundedFacts : LeafRoundedFacts 8
    leaf6494Certificate.logOnePlusV leaf6494InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6494InputLogOnePlusV_eq }

private noncomputable def leaf6494Inputs : Inputs :=
  inputsOfCaches globalInput sk91RoundedInputs
    chi90InputQChi innerPair750Input
    leaf6494InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6494LowerChecked :
    lowerCheck 24 leaf6494Box leaf6494Inputs = true := by
  rfl'

private theorem leaf6494CoversExact : CoversExact 8
    leaf6494Box leaf6494Certificate leaf6494InnerLog leaf6494Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk91RoundedFacts chi90RoundedFacts
    innerPair750RoundedFacts leaf6494RoundedFacts (by rfl)

private theorem leaf6494FlatSound : Sound leaf6494Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6494CertificateValid
    leaf6494InnerLogValid leaf6494CoversExact leaf6494LowerChecked

private noncomputable def leaf6495Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (13/16), chiHi := (27/32) }

private noncomputable def leaf6495Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554573/33554432) }, vSqrt := { lower := (32765/32768), upper := (8589426687/8588718080) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (106786301/67108864) }, upper := { exponent := 1, mantissa := (425/256) } }, logOuter := sk92LogOuterCertificate, logK := sk92LogKCertificate, logChi := chi90LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (17178144767/17177436160) } }, logDArg := sk92LogDArgCertificate }

private noncomputable def leaf6495InnerLog : WideLogData :=
  innerPair751Data

set_option maxRecDepth 1000000 in
private theorem leaf6495LocalValidity :
    LeafFacts leaf6495Box leaf6495Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6495Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8589426687/8588718080) }) = true
      norm_num [leaf6495Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6495CertificateValid :
    WideCertificateValid leaf6495Box leaf6495Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk92ValidityFacts chi90ValidityFacts
    leaf6495LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6495CoverageChecked :
    coverageCheck (innerAD leaf6495Box) leaf6495InnerLog = true := by
  rfl'

private theorem leaf6495InnerLogValid :
    leaf6495InnerLog.Valid 8 (innerAD leaf6495Box) :=
  wideLogDataValid_of_cachedCheck endpoint483PositiveFacts
    endpoint487PositiveFacts.valid leaf6495CoverageChecked

private noncomputable def leaf6495InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629773/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6495InputLogOnePlusV_eq :
    leaf6495InputLogOnePlusV = outerEnclosure 24
      (leaf6495Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6495RoundedFacts : LeafRoundedFacts 8
    leaf6495Certificate.logOnePlusV leaf6495InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6495InputLogOnePlusV_eq }

private noncomputable def leaf6495Inputs : Inputs :=
  inputsOfCaches globalInput sk92RoundedInputs
    chi90InputQChi innerPair751Input
    leaf6495InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6495LowerChecked :
    lowerCheck 24 leaf6495Box leaf6495Inputs = true := by
  rfl'

private theorem leaf6495CoversExact : CoversExact 8
    leaf6495Box leaf6495Certificate leaf6495InnerLog leaf6495Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk92RoundedFacts chi90RoundedFacts
    innerPair751RoundedFacts leaf6495RoundedFacts (by rfl)

private theorem leaf6495FlatSound : Sound leaf6495Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6495CertificateValid
    leaf6495InnerLogValid leaf6495CoversExact leaf6495LowerChecked

private noncomputable def leaf6496Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (27/32), chiHi := (7/8) }

private noncomputable def leaf6496Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554573/33554432) }, vSqrt := { lower := (32765/32768), upper := (8589426687/8588701696) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (107834813/67108864) }, upper := { exponent := 1, mantissa := (429/256) } }, logOuter := sk91LogOuterCertificate, logK := sk91LogKCertificate, logChi := chi91LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (17178128383/17177403392) } }, logDArg := sk91LogDArgCertificate }

private noncomputable def leaf6496InnerLog : WideLogData :=
  innerPair756Data

set_option maxRecDepth 1000000 in
private theorem leaf6496LocalValidity :
    LeafFacts leaf6496Box leaf6496Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6496Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8589426687/8588701696) }) = true
      norm_num [leaf6496Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6496CertificateValid :
    WideCertificateValid leaf6496Box leaf6496Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk91ValidityFacts chi91ValidityFacts
    leaf6496LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6496CoverageChecked :
    coverageCheck (innerAD leaf6496Box) leaf6496InnerLog = true := by
  rfl'

private theorem leaf6496InnerLogValid :
    leaf6496InnerLog.Valid 8 (innerAD leaf6496Box) :=
  wideLogDataValid_of_cachedCheck endpoint484PositiveFacts
    endpoint487PositiveFacts.valid leaf6496CoverageChecked

private noncomputable def leaf6496InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629789/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6496InputLogOnePlusV_eq :
    leaf6496InputLogOnePlusV = outerEnclosure 24
      (leaf6496Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6496RoundedFacts : LeafRoundedFacts 8
    leaf6496Certificate.logOnePlusV leaf6496InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6496InputLogOnePlusV_eq }

private noncomputable def leaf6496Inputs : Inputs :=
  inputsOfCaches globalInput sk91RoundedInputs
    chi91InputQChi innerPair756Input
    leaf6496InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6496LowerChecked :
    lowerCheck 24 leaf6496Box leaf6496Inputs = true := by
  rfl'

private theorem leaf6496CoversExact : CoversExact 8
    leaf6496Box leaf6496Certificate leaf6496InnerLog leaf6496Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk91RoundedFacts chi91RoundedFacts
    innerPair756RoundedFacts leaf6496RoundedFacts (by rfl)

private theorem leaf6496FlatSound : Sound leaf6496Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6496CertificateValid
    leaf6496InnerLogValid leaf6496CoversExact leaf6496LowerChecked

private noncomputable def leaf6497Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (27/32), chiHi := (7/8) }

private noncomputable def leaf6497Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554575/33554432) }, vSqrt := { lower := (32765/32768), upper := (2863142229/2862891008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (109604175/67108864) }, upper := { exponent := 1, mantissa := (109/64) } }, logOuter := sk92LogOuterCertificate, logK := sk92LogKCertificate, logChi := chi91LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (5726033237/5725782016) } }, logDArg := sk92LogDArgCertificate }

private noncomputable def leaf6497InnerLog : WideLogData :=
  innerPair762Data

set_option maxRecDepth 1000000 in
private theorem leaf6497LocalValidity :
    LeafFacts leaf6497Box leaf6497Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6497Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (2863142229/2862891008) }) = true
      norm_num [leaf6497Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6497CertificateValid :
    WideCertificateValid leaf6497Box leaf6497Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk92ValidityFacts chi91ValidityFacts
    leaf6497LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6497CoverageChecked :
    coverageCheck (innerAD leaf6497Box) leaf6497InnerLog = true := by
  rfl'

private theorem leaf6497InnerLogValid :
    leaf6497InnerLog.Valid 8 (innerAD leaf6497Box) :=
  wideLogDataValid_of_cachedCheck endpoint485PositiveFacts
    endpoint488PositiveFacts.valid leaf6497CoverageChecked

private noncomputable def leaf6497InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629817/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6497InputLogOnePlusV_eq :
    leaf6497InputLogOnePlusV = outerEnclosure 24
      (leaf6497Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6497RoundedFacts : LeafRoundedFacts 8
    leaf6497Certificate.logOnePlusV leaf6497InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6497InputLogOnePlusV_eq }

private noncomputable def leaf6497Inputs : Inputs :=
  inputsOfCaches globalInput sk92RoundedInputs
    chi91InputQChi innerPair762Input
    leaf6497InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6497LowerChecked :
    lowerCheck 24 leaf6497Box leaf6497Inputs = true := by
  rfl'

private theorem leaf6497CoversExact : CoversExact 8
    leaf6497Box leaf6497Certificate leaf6497InnerLog leaf6497Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk92RoundedFacts chi91RoundedFacts
    innerPair762RoundedFacts leaf6497RoundedFacts (by rfl)

private theorem leaf6497FlatSound : Sound leaf6497Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6497CertificateValid
    leaf6497InnerLogValid leaf6497CoversExact leaf6497LowerChecked

private noncomputable def leaf6498Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (3/4), chiHi := (25/32) }

private noncomputable def leaf6498Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554571/33554432) }, vSqrt := { lower := (32765/32768), upper := (8589426687/8588782592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (102723319/67108864) }, upper := { exponent := 1, mantissa := (1637/1024) } }, logOuter := sk95LogOuterCertificate, logK := sk95LogKCertificate, logChi := chi88LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (17178209279/17177565184) } }, logDArg := sk95LogDArgCertificate }

private noncomputable def leaf6498InnerLog : WideLogData :=
  innerPair786Data

set_option maxRecDepth 1000000 in
private theorem leaf6498LocalValidity :
    LeafFacts leaf6498Box leaf6498Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6498Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8589426687/8588782592) }) = true
      norm_num [leaf6498Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6498CertificateValid :
    WideCertificateValid leaf6498Box leaf6498Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk95ValidityFacts chi88ValidityFacts
    leaf6498LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6498CoverageChecked :
    coverageCheck (innerAD leaf6498Box) leaf6498InnerLog = true := by
  rfl'

private theorem leaf6498InnerLogValid :
    leaf6498InnerLog.Valid 8 (innerAD leaf6498Box) :=
  wideLogDataValid_of_cachedCheck endpoint493PositiveFacts
    endpoint494PositiveFacts.valid leaf6498CoverageChecked

private noncomputable def leaf6498InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814855/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6498InputLogOnePlusV_eq :
    leaf6498InputLogOnePlusV = outerEnclosure 24
      (leaf6498Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6498RoundedFacts : LeafRoundedFacts 8
    leaf6498Certificate.logOnePlusV leaf6498InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6498InputLogOnePlusV_eq }

private noncomputable def leaf6498Inputs : Inputs :=
  inputsOfCaches globalInput sk95RoundedInputs
    chi88InputQChi innerPair786Input
    leaf6498InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6498LowerChecked :
    lowerCheck 24 leaf6498Box leaf6498Inputs = true := by
  rfl'

private theorem leaf6498CoversExact : CoversExact 8
    leaf6498Box leaf6498Certificate leaf6498InnerLog leaf6498Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk95RoundedFacts chi88RoundedFacts
    innerPair786RoundedFacts leaf6498RoundedFacts (by rfl)

private theorem leaf6498FlatSound : Sound leaf6498Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6498CertificateValid
    leaf6498InnerLogValid leaf6498CoversExact leaf6498LowerChecked

private noncomputable def leaf6499Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (3/4), chiHi := (49/64) }

private noncomputable def leaf6499Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109053/67108864) }, vSqrt := { lower := (32765/32768), upper := (2863142229/2862926848) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (208625029/134217728) }, upper := { exponent := 1, mantissa := (1639/1024) } }, logOuter := sk96LogOuterCertificate, logK := sk96LogKCertificate, logChi := chi345LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (5726069077/5725853696) } }, logDArg := sk96LogDArgCertificate }

private noncomputable def leaf6499InnerLog : WideLogData :=
  innerPair745Data

set_option maxRecDepth 1000000 in
private theorem leaf6499LocalValidity :
    LeafFacts leaf6499Box leaf6499Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6499Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (2863142229/2862926848) }) = true
      norm_num [leaf6499Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6499CertificateValid :
    WideCertificateValid leaf6499Box leaf6499Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk96ValidityFacts chi345ValidityFacts
    leaf6499LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6499CoverageChecked :
    coverageCheck (innerAD leaf6499Box) leaf6499InnerLog = true := by
  rfl'

private theorem leaf6499InnerLogValid :
    leaf6499InnerLog.Valid 8 (innerAD leaf6499Box) :=
  wideLogDataValid_of_cachedCheck endpoint482PositiveFacts
    endpoint485PositiveFacts.valid leaf6499CoverageChecked

private noncomputable def leaf6499InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (726857/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf6499InputLogOnePlusV_eq :
    leaf6499InputLogOnePlusV = outerEnclosure 24
      (leaf6499Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6499RoundedFacts : LeafRoundedFacts 8
    leaf6499Certificate.logOnePlusV leaf6499InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6499InputLogOnePlusV_eq }

private noncomputable def leaf6499Inputs : Inputs :=
  inputsOfCaches globalInput sk96RoundedInputs
    chi345InputQChi innerPair745Input
    leaf6499InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6499LowerChecked :
    lowerCheck 24 leaf6499Box leaf6499Inputs = true := by
  rfl'

private theorem leaf6499CoversExact : CoversExact 8
    leaf6499Box leaf6499Certificate leaf6499InnerLog leaf6499Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk96RoundedFacts chi345RoundedFacts
    innerPair745RoundedFacts leaf6499RoundedFacts (by rfl)

private theorem leaf6499FlatSound : Sound leaf6499Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6499CertificateValid
    leaf6499InnerLogValid leaf6499CoversExact leaf6499LowerChecked

private noncomputable def leaf6500Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (49/64), chiHi := (25/32) }

private noncomputable def leaf6500Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109055/67108864) }, vSqrt := { lower := (32765/32768), upper := (8589426687/8588756992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (211573967/134217728) }, upper := { exponent := 1, mantissa := (831/512) } }, logOuter := sk96LogOuterCertificate, logK := sk96LogKCertificate, logChi := chi346LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (17178183679/17177513984) } }, logDArg := sk96LogDArgCertificate }

private noncomputable def leaf6500InnerLog : WideLogData :=
  innerPair749Data

set_option maxRecDepth 1000000 in
private theorem leaf6500LocalValidity :
    LeafFacts leaf6500Box leaf6500Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6500Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8589426687/8588756992) }) = true
      norm_num [leaf6500Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6500CertificateValid :
    WideCertificateValid leaf6500Box leaf6500Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk96ValidityFacts chi346ValidityFacts
    leaf6500LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6500CoverageChecked :
    coverageCheck (innerAD leaf6500Box) leaf6500InnerLog = true := by
  rfl'

private theorem leaf6500InnerLogValid :
    leaf6500InnerLog.Valid 8 (innerAD leaf6500Box) :=
  wideLogDataValid_of_cachedCheck endpoint483PositiveFacts
    endpoint485PositiveFacts.valid leaf6500CoverageChecked

private noncomputable def leaf6500InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629735/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6500InputLogOnePlusV_eq :
    leaf6500InputLogOnePlusV = outerEnclosure 24
      (leaf6500Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6500RoundedFacts : LeafRoundedFacts 8
    leaf6500Certificate.logOnePlusV leaf6500InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6500InputLogOnePlusV_eq }

private noncomputable def leaf6500Inputs : Inputs :=
  inputsOfCaches globalInput sk96RoundedInputs
    chi346InputQChi innerPair749Input
    leaf6500InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6500LowerChecked :
    lowerCheck 24 leaf6500Box leaf6500Inputs = true := by
  rfl'

private theorem leaf6500CoversExact : CoversExact 8
    leaf6500Box leaf6500Certificate leaf6500InnerLog leaf6500Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk96RoundedFacts chi346RoundedFacts
    innerPair749RoundedFacts leaf6500RoundedFacts (by rfl)

private theorem leaf6500FlatSound : Sound leaf6500Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6500CertificateValid
    leaf6500InnerLogValid leaf6500CoversExact leaf6500LowerChecked

private noncomputable def leaf6501Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (25/32), chiHi := (13/16) }

private noncomputable def leaf6501Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554573/33554432) }, vSqrt := { lower := (32765/32768), upper := (8589426687/8588736512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (105606725/67108864) }, upper := { exponent := 1, mantissa := (841/512) } }, logOuter := sk95LogOuterCertificate, logK := sk95LogKCertificate, logChi := chi89LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (17178163199/17177473024) } }, logDArg := sk95LogDArgCertificate }

private noncomputable def leaf6501InnerLog : WideLogData :=
  innerPair750Data

set_option maxRecDepth 1000000 in
private theorem leaf6501LocalValidity :
    LeafFacts leaf6501Box leaf6501Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6501Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8589426687/8588736512) }) = true
      norm_num [leaf6501Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6501CertificateValid :
    WideCertificateValid leaf6501Box leaf6501Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk95ValidityFacts chi89ValidityFacts
    leaf6501LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6501CoverageChecked :
    coverageCheck (innerAD leaf6501Box) leaf6501InnerLog = true := by
  rfl'

private theorem leaf6501InnerLogValid :
    leaf6501InnerLog.Valid 8 (innerAD leaf6501Box) :=
  wideLogDataValid_of_cachedCheck endpoint483PositiveFacts
    endpoint486PositiveFacts.valid leaf6501CoverageChecked

private noncomputable def leaf6501InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629755/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6501InputLogOnePlusV_eq :
    leaf6501InputLogOnePlusV = outerEnclosure 24
      (leaf6501Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6501RoundedFacts : LeafRoundedFacts 8
    leaf6501Certificate.logOnePlusV leaf6501InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6501InputLogOnePlusV_eq }

private noncomputable def leaf6501Inputs : Inputs :=
  inputsOfCaches globalInput sk95RoundedInputs
    chi89InputQChi innerPair750Input
    leaf6501InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6501LowerChecked :
    lowerCheck 24 leaf6501Box leaf6501Inputs = true := by
  rfl'

private theorem leaf6501CoversExact : CoversExact 8
    leaf6501Box leaf6501Certificate leaf6501InnerLog leaf6501Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk95RoundedFacts chi89RoundedFacts
    innerPair750RoundedFacts leaf6501RoundedFacts (by rfl)

private theorem leaf6501FlatSound : Sound leaf6501Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6501CertificateValid
    leaf6501InnerLogValid leaf6501CoversExact leaf6501LowerChecked

private noncomputable def leaf6502Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (25/32), chiHi := (13/16) }

private noncomputable def leaf6502Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554575/33554432) }, vSqrt := { lower := (32765/32768), upper := (2863142229/2862903296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (107245023/67108864) }, upper := { exponent := 1, mantissa := (427/256) } }, logOuter := sk96LogOuterCertificate, logK := sk96LogKCertificate, logChi := chi89LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (5726045525/5725806592) } }, logDArg := sk96LogDArgCertificate }

private noncomputable def leaf6502InnerLog : WideLogData :=
  innerPair758Data

set_option maxRecDepth 1000000 in
private theorem leaf6502LocalValidity :
    LeafFacts leaf6502Box leaf6502Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6502Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (2863142229/2862903296) }) = true
      norm_num [leaf6502Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6502CertificateValid :
    WideCertificateValid leaf6502Box leaf6502Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk96ValidityFacts chi89ValidityFacts
    leaf6502LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6502CoverageChecked :
    coverageCheck (innerAD leaf6502Box) leaf6502InnerLog = true := by
  rfl'

private theorem leaf6502InnerLogValid :
    leaf6502InnerLog.Valid 8 (innerAD leaf6502Box) :=
  wideLogDataValid_of_cachedCheck endpoint484PositiveFacts
    endpoint495PositiveFacts.valid leaf6502CoverageChecked

private noncomputable def leaf6502InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629781/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6502InputLogOnePlusV_eq :
    leaf6502InputLogOnePlusV = outerEnclosure 24
      (leaf6502Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6502RoundedFacts : LeafRoundedFacts 8
    leaf6502Certificate.logOnePlusV leaf6502InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6502InputLogOnePlusV_eq }

private noncomputable def leaf6502Inputs : Inputs :=
  inputsOfCaches globalInput sk96RoundedInputs
    chi89InputQChi innerPair758Input
    leaf6502InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6502LowerChecked :
    lowerCheck 24 leaf6502Box leaf6502Inputs = true := by
  rfl'

private theorem leaf6502CoversExact : CoversExact 8
    leaf6502Box leaf6502Certificate leaf6502InnerLog leaf6502Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk96RoundedFacts chi89RoundedFacts
    innerPair758RoundedFacts leaf6502RoundedFacts (by rfl)

private theorem leaf6502FlatSound : Sound leaf6502Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6502CertificateValid
    leaf6502InnerLogValid leaf6502CoversExact leaf6502LowerChecked

private noncomputable def leaf6503Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (3/4), chiHi := (49/64) }

private noncomputable def leaf6503Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109055/67108864) }, vSqrt := { lower := (32765/32768), upper := (8589426687/8588755456) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (211770563/134217728) }, upper := { exponent := 1, mantissa := (3327/2048) } }, logOuter := sk97LogOuterCertificate, logK := sk97LogKCertificate, logChi := chi345LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (17178182143/17177510912) } }, logDArg := sk97LogDArgCertificate }

private noncomputable def leaf6503InnerLog : WideLogData :=
  innerPair749Data

set_option maxRecDepth 1000000 in
private theorem leaf6503LocalValidity :
    LeafFacts leaf6503Box leaf6503Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6503Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8589426687/8588755456) }) = true
      norm_num [leaf6503Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6503CertificateValid :
    WideCertificateValid leaf6503Box leaf6503Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk97ValidityFacts chi345ValidityFacts
    leaf6503LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6503CoverageChecked :
    coverageCheck (innerAD leaf6503Box) leaf6503InnerLog = true := by
  rfl'

private theorem leaf6503InnerLogValid :
    leaf6503InnerLog.Valid 8 (innerAD leaf6503Box) :=
  wideLogDataValid_of_cachedCheck endpoint483PositiveFacts
    endpoint485PositiveFacts.valid leaf6503CoverageChecked

private noncomputable def leaf6503InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453717/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf6503InputLogOnePlusV_eq :
    leaf6503InputLogOnePlusV = outerEnclosure 24
      (leaf6503Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6503RoundedFacts : LeafRoundedFacts 8
    leaf6503Certificate.logOnePlusV leaf6503InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6503InputLogOnePlusV_eq }

private noncomputable def leaf6503Inputs : Inputs :=
  inputsOfCaches globalInput sk97RoundedInputs
    chi345InputQChi innerPair749Input
    leaf6503InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6503LowerChecked :
    lowerCheck 24 leaf6503Box leaf6503Inputs = true := by
  rfl'

private theorem leaf6503CoversExact : CoversExact 8
    leaf6503Box leaf6503Certificate leaf6503InnerLog leaf6503Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk97RoundedFacts chi345RoundedFacts
    innerPair749RoundedFacts leaf6503RoundedFacts (by rfl)

private theorem leaf6503FlatSound : Sound leaf6503Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6503CertificateValid
    leaf6503InnerLogValid leaf6503CoversExact leaf6503LowerChecked

private noncomputable def leaf6504Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (49/64), chiHi := (25/32) }

private noncomputable def leaf6504Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109057/67108864) }, vSqrt := { lower := (32765/32768), upper := (954380743/954303488) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (214785033/134217728) }, upper := { exponent := 1, mantissa := (1687/1024) } }, logOuter := sk97LogOuterCertificate, logK := sk97LogKCertificate, logChi := chi346LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (1908684231/1908606976) } }, logDArg := sk97LogDArgCertificate }

private noncomputable def leaf6504InnerLog : WideLogData :=
  innerPair755Data

set_option maxRecDepth 1000000 in
private theorem leaf6504LocalValidity :
    LeafFacts leaf6504Box leaf6504Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6504Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (954380743/954303488) }) = true
      norm_num [leaf6504Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6504CertificateValid :
    WideCertificateValid leaf6504Box leaf6504Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk97ValidityFacts chi346ValidityFacts
    leaf6504LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6504CoverageChecked :
    coverageCheck (innerAD leaf6504Box) leaf6504InnerLog = true := by
  rfl'

private theorem leaf6504InnerLogValid :
    leaf6504InnerLog.Valid 8 (innerAD leaf6504Box) :=
  wideLogDataValid_of_cachedCheck endpoint484PositiveFacts
    endpoint486PositiveFacts.valid leaf6504CoverageChecked

private noncomputable def leaf6504InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (181715/262144) }

set_option maxRecDepth 1000000 in
private theorem leaf6504InputLogOnePlusV_eq :
    leaf6504InputLogOnePlusV = outerEnclosure 24
      (leaf6504Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6504RoundedFacts : LeafRoundedFacts 8
    leaf6504Certificate.logOnePlusV leaf6504InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6504InputLogOnePlusV_eq }

private noncomputable def leaf6504Inputs : Inputs :=
  inputsOfCaches globalInput sk97RoundedInputs
    chi346InputQChi innerPair755Input
    leaf6504InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6504LowerChecked :
    lowerCheck 24 leaf6504Box leaf6504Inputs = true := by
  rfl'

private theorem leaf6504CoversExact : CoversExact 8
    leaf6504Box leaf6504Certificate leaf6504InnerLog leaf6504Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk97RoundedFacts chi346RoundedFacts
    innerPair755RoundedFacts leaf6504RoundedFacts (by rfl)

private theorem leaf6504FlatSound : Sound leaf6504Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6504CertificateValid
    leaf6504InnerLogValid leaf6504CoversExact leaf6504LowerChecked

private noncomputable def leaf6505Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (3/4), chiHi := (49/64) }

private noncomputable def leaf6505Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109057/67108864) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588730368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (214916097/134217728) }, upper := { exponent := 1, mantissa := (211/128) } }, logOuter := sk98LogOuterCertificate, logK := sk98LogKCertificate, logChi := chi345LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178157055/17177460736) } }, logDArg := sk98LogDArgCertificate }

private noncomputable def leaf6505InnerLog : WideLogData :=
  innerPair755Data

set_option maxRecDepth 1000000 in
private theorem leaf6505LocalValidity :
    LeafFacts leaf6505Box leaf6505Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6505Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588730368) }) = true
      norm_num [leaf6505Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6505CertificateValid :
    WideCertificateValid leaf6505Box leaf6505Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk98ValidityFacts chi345ValidityFacts
    leaf6505LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6505CoverageChecked :
    coverageCheck (innerAD leaf6505Box) leaf6505InnerLog = true := by
  rfl'

private theorem leaf6505InnerLogValid :
    leaf6505InnerLog.Valid 8 (innerAD leaf6505Box) :=
  wideLogDataValid_of_cachedCheck endpoint484PositiveFacts
    endpoint486PositiveFacts.valid leaf6505CoverageChecked

private noncomputable def leaf6505InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629761/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6505InputLogOnePlusV_eq :
    leaf6505InputLogOnePlusV = outerEnclosure 24
      (leaf6505Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6505RoundedFacts : LeafRoundedFacts 8
    leaf6505Certificate.logOnePlusV leaf6505InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6505InputLogOnePlusV_eq }

private noncomputable def leaf6505Inputs : Inputs :=
  inputsOfCaches globalInput sk98RoundedInputs
    chi345InputQChi innerPair755Input
    leaf6505InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6505LowerChecked :
    lowerCheck 24 leaf6505Box leaf6505Inputs = true := by
  rfl'

private theorem leaf6505CoversExact : CoversExact 8
    leaf6505Box leaf6505Certificate leaf6505InnerLog leaf6505Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk98RoundedFacts chi345RoundedFacts
    innerPair755RoundedFacts leaf6505RoundedFacts (by rfl)

private theorem leaf6505FlatSound : Sound leaf6505Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6505CertificateValid
    leaf6505InnerLogValid leaf6505CoversExact leaf6505LowerChecked

private noncomputable def leaf6506Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (49/64), chiHi := (25/32) }

private noncomputable def leaf6506Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109059/67108864) }, vSqrt := { lower := (65529/65536), upper := (199754109/199737344) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (217996099/134217728) }, upper := { exponent := 1, mantissa := (107/64) } }, logOuter := sk98LogOuterCertificate, logK := sk98LogKCertificate, logChi := chi346LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (399491453/399474688) } }, logDArg := sk98LogDArgCertificate }

private noncomputable def leaf6506InnerLog : WideLogData :=
  innerPair756Data

set_option maxRecDepth 1000000 in
private theorem leaf6506LocalValidity :
    LeafFacts leaf6506Box leaf6506Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6506Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (199754109/199737344) }) = true
      norm_num [leaf6506Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6506CertificateValid :
    WideCertificateValid leaf6506Box leaf6506Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk98ValidityFacts chi346ValidityFacts
    leaf6506LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6506CoverageChecked :
    coverageCheck (innerAD leaf6506Box) leaf6506InnerLog = true := by
  rfl'

private theorem leaf6506InnerLogValid :
    leaf6506InnerLog.Valid 8 (innerAD leaf6506Box) :=
  wideLogDataValid_of_cachedCheck endpoint484PositiveFacts
    endpoint487PositiveFacts.valid leaf6506CoverageChecked

private noncomputable def leaf6506InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629785/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6506InputLogOnePlusV_eq :
    leaf6506InputLogOnePlusV = outerEnclosure 24
      (leaf6506Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6506RoundedFacts : LeafRoundedFacts 8
    leaf6506Certificate.logOnePlusV leaf6506InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6506InputLogOnePlusV_eq }

private noncomputable def leaf6506Inputs : Inputs :=
  inputsOfCaches globalInput sk98RoundedInputs
    chi346InputQChi innerPair756Input
    leaf6506InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6506LowerChecked :
    lowerCheck 24 leaf6506Box leaf6506Inputs = true := by
  rfl'

private theorem leaf6506CoversExact : CoversExact 8
    leaf6506Box leaf6506Certificate leaf6506InnerLog leaf6506Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk98RoundedFacts chi346RoundedFacts
    innerPair756RoundedFacts leaf6506RoundedFacts (by rfl)

private theorem leaf6506FlatSound : Sound leaf6506Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6506CertificateValid
    leaf6506InnerLogValid leaf6506CoversExact leaf6506LowerChecked

private noncomputable def leaf6507Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (25/32), chiHi := (13/16) }

private noncomputable def leaf6507Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554577/33554432) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588683264) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (108883321/67108864) }, upper := { exponent := 1, mantissa := (867/512) } }, logOuter := sk97LogOuterCertificate, logK := sk97LogKCertificate, logChi := chi89LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178109951/17177366528) } }, logDArg := sk97LogDArgCertificate }

private noncomputable def leaf6507InnerLog : WideLogData :=
  innerPair789Data

set_option maxRecDepth 1000000 in
private theorem leaf6507LocalValidity :
    LeafFacts leaf6507Box leaf6507Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6507Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588683264) }) = true
      norm_num [leaf6507Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6507CertificateValid :
    WideCertificateValid leaf6507Box leaf6507Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk97ValidityFacts chi89ValidityFacts
    leaf6507LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6507CoverageChecked :
    coverageCheck (innerAD leaf6507Box) leaf6507InnerLog = true := by
  rfl'

private theorem leaf6507InnerLogValid :
    leaf6507InnerLog.Valid 8 (innerAD leaf6507Box) :=
  wideLogDataValid_of_cachedCheck endpoint496PositiveFacts
    endpoint497PositiveFacts.valid leaf6507CoverageChecked

private noncomputable def leaf6507InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629807/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6507InputLogOnePlusV_eq :
    leaf6507InputLogOnePlusV = outerEnclosure 24
      (leaf6507Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6507RoundedFacts : LeafRoundedFacts 8
    leaf6507Certificate.logOnePlusV leaf6507InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6507InputLogOnePlusV_eq }

private noncomputable def leaf6507Inputs : Inputs :=
  inputsOfCaches globalInput sk97RoundedInputs
    chi89InputQChi innerPair789Input
    leaf6507InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6507LowerChecked :
    lowerCheck 24 leaf6507Box leaf6507Inputs = true := by
  rfl'

private theorem leaf6507CoversExact : CoversExact 8
    leaf6507Box leaf6507Certificate leaf6507InnerLog leaf6507Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk97RoundedFacts chi89RoundedFacts
    innerPair789RoundedFacts leaf6507RoundedFacts (by rfl)

private theorem leaf6507FlatSound : Sound leaf6507Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6507CertificateValid
    leaf6507InnerLogValid leaf6507CoversExact leaf6507LowerChecked

private noncomputable def leaf6508Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (25/32), chiHi := (13/16) }

private noncomputable def leaf6508Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554579/33554432) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588656640) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (110521619/67108864) }, upper := { exponent := 1, mantissa := (55/32) } }, logOuter := sk98LogOuterCertificate, logK := sk98LogKCertificate, logChi := chi89LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178083327/17177313280) } }, logDArg := sk98LogDArgCertificate }

private noncomputable def leaf6508InnerLog : WideLogData :=
  innerPair762Data

set_option maxRecDepth 1000000 in
private theorem leaf6508LocalValidity :
    LeafFacts leaf6508Box leaf6508Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6508Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588656640) }) = true
      norm_num [leaf6508Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6508CertificateValid :
    WideCertificateValid leaf6508Box leaf6508Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk98ValidityFacts chi89ValidityFacts
    leaf6508LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6508CoverageChecked :
    coverageCheck (innerAD leaf6508Box) leaf6508InnerLog = true := by
  rfl'

private theorem leaf6508InnerLogValid :
    leaf6508InnerLog.Valid 8 (innerAD leaf6508Box) :=
  wideLogDataValid_of_cachedCheck endpoint485PositiveFacts
    endpoint488PositiveFacts.valid leaf6508CoverageChecked

private noncomputable def leaf6508InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629833/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6508InputLogOnePlusV_eq :
    leaf6508InputLogOnePlusV = outerEnclosure 24
      (leaf6508Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6508RoundedFacts : LeafRoundedFacts 8
    leaf6508Certificate.logOnePlusV leaf6508InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6508InputLogOnePlusV_eq }

private noncomputable def leaf6508Inputs : Inputs :=
  inputsOfCaches globalInput sk98RoundedInputs
    chi89InputQChi innerPair762Input
    leaf6508InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6508LowerChecked :
    lowerCheck 24 leaf6508Box leaf6508Inputs = true := by
  rfl'

private theorem leaf6508CoversExact : CoversExact 8
    leaf6508Box leaf6508Certificate leaf6508InnerLog leaf6508Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk98RoundedFacts chi89RoundedFacts
    innerPair762RoundedFacts leaf6508RoundedFacts (by rfl)

private theorem leaf6508FlatSound : Sound leaf6508Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6508CertificateValid
    leaf6508InnerLogValid leaf6508CoversExact leaf6508LowerChecked

private noncomputable def leaf6509Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (13/16), chiHi := (27/32) }

private noncomputable def leaf6509Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554575/33554432) }, vSqrt := { lower := (32765/32768), upper := (8589426687/8588690432) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (108490131/67108864) }, upper := { exponent := 1, mantissa := (1727/1024) } }, logOuter := sk95LogOuterCertificate, logK := sk95LogKCertificate, logChi := chi90LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (17178117119/17177380864) } }, logDArg := sk95LogDArgCertificate }

private noncomputable def leaf6509InnerLog : WideLogData :=
  innerPair756Data

set_option maxRecDepth 1000000 in
private theorem leaf6509LocalValidity :
    LeafFacts leaf6509Box leaf6509Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6509Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8589426687/8588690432) }) = true
      norm_num [leaf6509Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6509CertificateValid :
    WideCertificateValid leaf6509Box leaf6509Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk95ValidityFacts chi90ValidityFacts
    leaf6509LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6509CoverageChecked :
    coverageCheck (innerAD leaf6509Box) leaf6509InnerLog = true := by
  rfl'

private theorem leaf6509InnerLogValid :
    leaf6509InnerLog.Valid 8 (innerAD leaf6509Box) :=
  wideLogDataValid_of_cachedCheck endpoint484PositiveFacts
    endpoint487PositiveFacts.valid leaf6509CoverageChecked

private noncomputable def leaf6509InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453725/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf6509InputLogOnePlusV_eq :
    leaf6509InputLogOnePlusV = outerEnclosure 24
      (leaf6509Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6509RoundedFacts : LeafRoundedFacts 8
    leaf6509Certificate.logOnePlusV leaf6509InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6509InputLogOnePlusV_eq }

private noncomputable def leaf6509Inputs : Inputs :=
  inputsOfCaches globalInput sk95RoundedInputs
    chi90InputQChi innerPair756Input
    leaf6509InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6509LowerChecked :
    lowerCheck 24 leaf6509Box leaf6509Inputs = true := by
  rfl'

private theorem leaf6509CoversExact : CoversExact 8
    leaf6509Box leaf6509Certificate leaf6509InnerLog leaf6509Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk95RoundedFacts chi90RoundedFacts
    innerPair756RoundedFacts leaf6509RoundedFacts (by rfl)

private theorem leaf6509FlatSound : Sound leaf6509Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6509CertificateValid
    leaf6509InnerLogValid leaf6509CoversExact leaf6509LowerChecked

private noncomputable def leaf6510Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (13/16), chiHi := (27/32) }

private noncomputable def leaf6510Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554577/33554432) }, vSqrt := { lower := (32765/32768), upper := (8589426687/8588662784) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (110193961/67108864) }, upper := { exponent := 1, mantissa := (877/512) } }, logOuter := sk96LogOuterCertificate, logK := sk96LogKCertificate, logChi := chi90LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (17178089471/17177325568) } }, logDArg := sk96LogDArgCertificate }

private noncomputable def leaf6510InnerLog : WideLogData :=
  innerPair762Data

set_option maxRecDepth 1000000 in
private theorem leaf6510LocalValidity :
    LeafFacts leaf6510Box leaf6510Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6510Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8589426687/8588662784) }) = true
      norm_num [leaf6510Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6510CertificateValid :
    WideCertificateValid leaf6510Box leaf6510Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk96ValidityFacts chi90ValidityFacts
    leaf6510LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6510CoverageChecked :
    coverageCheck (innerAD leaf6510Box) leaf6510InnerLog = true := by
  rfl'

private theorem leaf6510InnerLogValid :
    leaf6510InnerLog.Valid 8 (innerAD leaf6510Box) :=
  wideLogDataValid_of_cachedCheck endpoint485PositiveFacts
    endpoint488PositiveFacts.valid leaf6510CoverageChecked

private noncomputable def leaf6510InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629827/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6510InputLogOnePlusV_eq :
    leaf6510InputLogOnePlusV = outerEnclosure 24
      (leaf6510Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6510RoundedFacts : LeafRoundedFacts 8
    leaf6510Certificate.logOnePlusV leaf6510InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6510InputLogOnePlusV_eq }

private noncomputable def leaf6510Inputs : Inputs :=
  inputsOfCaches globalInput sk96RoundedInputs
    chi90InputQChi innerPair762Input
    leaf6510InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6510LowerChecked :
    lowerCheck 24 leaf6510Box leaf6510Inputs = true := by
  rfl'

private theorem leaf6510CoversExact : CoversExact 8
    leaf6510Box leaf6510Certificate leaf6510InnerLog leaf6510Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk96RoundedFacts chi90RoundedFacts
    innerPair762RoundedFacts leaf6510RoundedFacts (by rfl)

private theorem leaf6510FlatSound : Sound leaf6510Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6510CertificateValid
    leaf6510InnerLogValid leaf6510CoversExact leaf6510LowerChecked

private noncomputable def leaf6511Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (27/32), chiHi := (7/8) }

private noncomputable def leaf6511Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554577/33554432) }, vSqrt := { lower := (32765/32768), upper := (8589426687/8588644352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (111373537/67108864) }, upper := { exponent := 1, mantissa := (443/256) } }, logOuter := sk95LogOuterCertificate, logK := sk95LogKCertificate, logChi := chi91LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (17178071039/17177288704) } }, logDArg := sk95LogDArgCertificate }

private noncomputable def leaf6511InnerLog : WideLogData :=
  innerPair766Data

set_option maxRecDepth 1000000 in
private theorem leaf6511LocalValidity :
    LeafFacts leaf6511Box leaf6511Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6511Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8589426687/8588644352) }) = true
      norm_num [leaf6511Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6511CertificateValid :
    WideCertificateValid leaf6511Box leaf6511Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk95ValidityFacts chi91ValidityFacts
    leaf6511LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6511CoverageChecked :
    coverageCheck (innerAD leaf6511Box) leaf6511InnerLog = true := by
  rfl'

private theorem leaf6511InnerLogValid :
    leaf6511InnerLog.Valid 8 (innerAD leaf6511Box) :=
  wideLogDataValid_of_cachedCheck endpoint486PositiveFacts
    endpoint489PositiveFacts.valid leaf6511CoverageChecked

private noncomputable def leaf6511InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629845/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6511InputLogOnePlusV_eq :
    leaf6511InputLogOnePlusV = outerEnclosure 24
      (leaf6511Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6511RoundedFacts : LeafRoundedFacts 8
    leaf6511Certificate.logOnePlusV leaf6511InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6511InputLogOnePlusV_eq }

private noncomputable def leaf6511Inputs : Inputs :=
  inputsOfCaches globalInput sk95RoundedInputs
    chi91InputQChi innerPair766Input
    leaf6511InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6511LowerChecked :
    lowerCheck 24 leaf6511Box leaf6511Inputs = true := by
  rfl'

private theorem leaf6511CoversExact : CoversExact 8
    leaf6511Box leaf6511Certificate leaf6511InnerLog leaf6511Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk95RoundedFacts chi91RoundedFacts
    innerPair766RoundedFacts leaf6511RoundedFacts (by rfl)

private theorem leaf6511FlatSound : Sound leaf6511Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6511CertificateValid
    leaf6511InnerLogValid leaf6511CoversExact leaf6511LowerChecked

private noncomputable def leaf6512Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (27/32), chiHi := (7/8) }

private noncomputable def leaf6512Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (33554579/33554432) }, vSqrt := { lower := (32765/32768), upper := (34357182459/34354462720) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (113142899/67108864) }, upper := { exponent := 1, mantissa := (225/128) } }, logOuter := sk96LogOuterCertificate, logK := sk96LogKCertificate, logChi := chi91LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68711645179/68708925440) } }, logDArg := sk96LogDArgCertificate }

private noncomputable def leaf6512InnerLog : WideLogData :=
  innerPair768Data

set_option maxRecDepth 1000000 in
private theorem leaf6512LocalValidity :
    LeafFacts leaf6512Box leaf6512Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6512Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34357182459/34354462720) }) = true
      norm_num [leaf6512Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6512CertificateValid :
    WideCertificateValid leaf6512Box leaf6512Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk96ValidityFacts chi91ValidityFacts
    leaf6512LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6512CoverageChecked :
    coverageCheck (innerAD leaf6512Box) leaf6512InnerLog = true := by
  rfl'

private theorem leaf6512InnerLogValid :
    leaf6512InnerLog.Valid 8 (innerAD leaf6512Box) :=
  wideLogDataValid_of_cachedCheck endpoint486PositiveFacts
    endpoint498PositiveFacts.valid leaf6512CoverageChecked

private noncomputable def leaf6512InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629745/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6512InputLogOnePlusV_eq :
    leaf6512InputLogOnePlusV = outerEnclosure 24
      (leaf6512Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6512RoundedFacts : LeafRoundedFacts 8
    leaf6512Certificate.logOnePlusV leaf6512InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6512InputLogOnePlusV_eq }

private noncomputable def leaf6512Inputs : Inputs :=
  inputsOfCaches globalInput sk96RoundedInputs
    chi91InputQChi innerPair768Input
    leaf6512InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6512LowerChecked :
    lowerCheck 24 leaf6512Box leaf6512Inputs = true := by
  rfl'

private theorem leaf6512CoversExact : CoversExact 8
    leaf6512Box leaf6512Certificate leaf6512InnerLog leaf6512Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk96RoundedFacts chi91RoundedFacts
    innerPair768RoundedFacts leaf6512RoundedFacts (by rfl)

private theorem leaf6512FlatSound : Sound leaf6512Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6512CertificateValid
    leaf6512InnerLogValid leaf6512CoversExact leaf6512LowerChecked

private noncomputable def leaf6513Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (13/16), chiHi := (27/32) }

private noncomputable def leaf6513Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (33554579/33554432) }, vSqrt := { lower := (65529/65536), upper := (34357182459/34354540544) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (111897791/67108864) }, upper := { exponent := 1, mantissa := (1781/1024) } }, logOuter := sk97LogOuterCertificate, logK := sk97LogKCertificate, logChi := chi90LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68711723003/68709081088) } }, logDArg := sk97LogDArgCertificate }

private noncomputable def leaf6513InnerLog : WideLogData :=
  innerPair766Data

set_option maxRecDepth 1000000 in
private theorem leaf6513LocalValidity :
    LeafFacts leaf6513Box leaf6513Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6513Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34357182459/34354540544) }) = true
      norm_num [leaf6513Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6513CertificateValid :
    WideCertificateValid leaf6513Box leaf6513Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk97ValidityFacts chi90ValidityFacts
    leaf6513LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6513CoverageChecked :
    coverageCheck (innerAD leaf6513Box) leaf6513InnerLog = true := by
  rfl'

private theorem leaf6513InnerLogValid :
    leaf6513InnerLog.Valid 8 (innerAD leaf6513Box) :=
  wideLogDataValid_of_cachedCheck endpoint486PositiveFacts
    endpoint489PositiveFacts.valid leaf6513CoverageChecked

private noncomputable def leaf6513InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814863/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6513InputLogOnePlusV_eq :
    leaf6513InputLogOnePlusV = outerEnclosure 24
      (leaf6513Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6513RoundedFacts : LeafRoundedFacts 8
    leaf6513Certificate.logOnePlusV leaf6513InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6513InputLogOnePlusV_eq }

private noncomputable def leaf6513Inputs : Inputs :=
  inputsOfCaches globalInput sk97RoundedInputs
    chi90InputQChi innerPair766Input
    leaf6513InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6513LowerChecked :
    lowerCheck 24 leaf6513Box leaf6513Inputs = true := by
  rfl'

private theorem leaf6513CoversExact : CoversExact 8
    leaf6513Box leaf6513Certificate leaf6513InnerLog leaf6513Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk97RoundedFacts chi90RoundedFacts
    innerPair766RoundedFacts leaf6513RoundedFacts (by rfl)

private theorem leaf6513FlatSound : Sound leaf6513Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6513CertificateValid
    leaf6513InnerLogValid leaf6513CoversExact leaf6513LowerChecked

private noncomputable def leaf6514Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (13/16), chiHi := (27/32) }

private noncomputable def leaf6514Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (33554581/33554432) }, vSqrt := { lower := (65529/65536), upper := (34357182459/34354429952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (113601621/67108864) }, upper := { exponent := 1, mantissa := (113/64) } }, logOuter := sk98LogOuterCertificate, logK := sk98LogKCertificate, logChi := chi90LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68711612411/68708859904) } }, logDArg := sk98LogDArgCertificate }

private noncomputable def leaf6514InnerLog : WideLogData :=
  innerPair772Data

set_option maxRecDepth 1000000 in
private theorem leaf6514LocalValidity :
    LeafFacts leaf6514Box leaf6514Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6514Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34357182459/34354429952) }) = true
      norm_num [leaf6514Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6514CertificateValid :
    WideCertificateValid leaf6514Box leaf6514Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk98ValidityFacts chi90ValidityFacts
    leaf6514LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6514CoverageChecked :
    coverageCheck (innerAD leaf6514Box) leaf6514InnerLog = true := by
  rfl'

private theorem leaf6514InnerLogValid :
    leaf6514InnerLog.Valid 8 (innerAD leaf6514Box) :=
  wideLogDataValid_of_cachedCheck endpoint487PositiveFacts
    endpoint499PositiveFacts.valid leaf6514CoverageChecked

private noncomputable def leaf6514InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629753/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6514InputLogOnePlusV_eq :
    leaf6514InputLogOnePlusV = outerEnclosure 24
      (leaf6514Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6514RoundedFacts : LeafRoundedFacts 8
    leaf6514Certificate.logOnePlusV leaf6514InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6514InputLogOnePlusV_eq }

private noncomputable def leaf6514Inputs : Inputs :=
  inputsOfCaches globalInput sk98RoundedInputs
    chi90InputQChi innerPair772Input
    leaf6514InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6514LowerChecked :
    lowerCheck 24 leaf6514Box leaf6514Inputs = true := by
  rfl'

private theorem leaf6514CoversExact : CoversExact 8
    leaf6514Box leaf6514Certificate leaf6514InnerLog leaf6514Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk98RoundedFacts chi90RoundedFacts
    innerPair772RoundedFacts leaf6514RoundedFacts (by rfl)

private theorem leaf6514FlatSound : Sound leaf6514Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6514CertificateValid
    leaf6514InnerLogValid leaf6514CoversExact leaf6514LowerChecked

private noncomputable def leaf6515Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (27/32), chiHi := (7/8) }

private noncomputable def leaf6515Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (33554581/33554432) }, vSqrt := { lower := (65529/65536), upper := (11452394153/11451449344) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (114912261/67108864) }, upper := { exponent := 1, mantissa := (457/256) } }, logOuter := sk97LogOuterCertificate, logK := sk97LogKCertificate, logChi := chi91LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (22903843497/22902898688) } }, logDArg := sk97LogDArgCertificate }

private noncomputable def leaf6515InnerLog : WideLogData :=
  innerPair773Data

set_option maxRecDepth 1000000 in
private theorem leaf6515LocalValidity :
    LeafFacts leaf6515Box leaf6515Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6515Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (11452394153/11451449344) }) = true
      norm_num [leaf6515Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6515CertificateValid :
    WideCertificateValid leaf6515Box leaf6515Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk97ValidityFacts chi91ValidityFacts
    leaf6515LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6515CoverageChecked :
    coverageCheck (innerAD leaf6515Box) leaf6515InnerLog = true := by
  rfl'

private theorem leaf6515InnerLogValid :
    leaf6515InnerLog.Valid 8 (innerAD leaf6515Box) :=
  wideLogDataValid_of_cachedCheck endpoint487PositiveFacts
    endpoint500PositiveFacts.valid leaf6515CoverageChecked

private noncomputable def leaf6515InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629773/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6515InputLogOnePlusV_eq :
    leaf6515InputLogOnePlusV = outerEnclosure 24
      (leaf6515Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6515RoundedFacts : LeafRoundedFacts 8
    leaf6515Certificate.logOnePlusV leaf6515InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6515InputLogOnePlusV_eq }

private noncomputable def leaf6515Inputs : Inputs :=
  inputsOfCaches globalInput sk97RoundedInputs
    chi91InputQChi innerPair773Input
    leaf6515InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6515LowerChecked :
    lowerCheck 24 leaf6515Box leaf6515Inputs = true := by
  rfl'

private theorem leaf6515CoversExact : CoversExact 8
    leaf6515Box leaf6515Certificate leaf6515InnerLog leaf6515Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk97RoundedFacts chi91RoundedFacts
    innerPair773RoundedFacts leaf6515RoundedFacts (by rfl)

private theorem leaf6515FlatSound : Sound leaf6515Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6515CertificateValid
    leaf6515InnerLogValid leaf6515CoversExact leaf6515LowerChecked

private noncomputable def leaf6516Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (27/32), chiHi := (7/8) }

private noncomputable def leaf6516Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (33554583/33554432) }, vSqrt := { lower := (65529/65536), upper := (34357182459/34354233344) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (116681623/67108864) }, upper := { exponent := 1, mantissa := (29/16) } }, logOuter := sk98LogOuterCertificate, logK := sk98LogKCertificate, logChi := chi91LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68711415803/68708466688) } }, logDArg := sk98LogDArgCertificate }

private noncomputable def leaf6516InnerLog : WideLogData :=
  innerPair776Data

set_option maxRecDepth 1000000 in
private theorem leaf6516LocalValidity :
    LeafFacts leaf6516Box leaf6516Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6516Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34357182459/34354233344) }) = true
      norm_num [leaf6516Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6516CertificateValid :
    WideCertificateValid leaf6516Box leaf6516Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk98ValidityFacts chi91ValidityFacts
    leaf6516LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6516CoverageChecked :
    coverageCheck (innerAD leaf6516Box) leaf6516InnerLog = true := by
  rfl'

private theorem leaf6516InnerLogValid :
    leaf6516InnerLog.Valid 8 (innerAD leaf6516Box) :=
  wideLogDataValid_of_cachedCheck endpoint488PositiveFacts
    endpoint500PositiveFacts.valid leaf6516CoverageChecked

private noncomputable def leaf6516InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629801/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6516InputLogOnePlusV_eq :
    leaf6516InputLogOnePlusV = outerEnclosure 24
      (leaf6516Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6516RoundedFacts : LeafRoundedFacts 8
    leaf6516Certificate.logOnePlusV leaf6516InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6516InputLogOnePlusV_eq }

private noncomputable def leaf6516Inputs : Inputs :=
  inputsOfCaches globalInput sk98RoundedInputs
    chi91InputQChi innerPair776Input
    leaf6516InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6516LowerChecked :
    lowerCheck 24 leaf6516Box leaf6516Inputs = true := by
  rfl'

private theorem leaf6516CoversExact : CoversExact 8
    leaf6516Box leaf6516Certificate leaf6516InnerLog leaf6516Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk98RoundedFacts chi91RoundedFacts
    innerPair776RoundedFacts leaf6516RoundedFacts (by rfl)

private theorem leaf6516FlatSound : Sound leaf6516Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6516CertificateValid
    leaf6516InnerLogValid leaf6516CoversExact leaf6516LowerChecked

private noncomputable def component130Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (3/4), chiHi := (25/32) }

set_option maxRecDepth 1000000 in
private theorem component130Node0_sound : Sound component130Node0Box :=
  sound_of_literal_split component130Node0Box leaf6482Box leaf6483Box
    .k (41/16) (by rfl) (by rfl)
    leaf6482FlatSound leaf6483FlatSound

private noncomputable def component130Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (25/32), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component130Node1_sound : Sound component130Node1Box :=
  sound_of_literal_split component130Node1Box leaf6484Box leaf6485Box
    .k (41/16) (by rfl) (by rfl)
    leaf6484FlatSound leaf6485FlatSound

private noncomputable def component130Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (3/4), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component130Node2_sound : Sound component130Node2Box :=
  sound_of_literal_split component130Node2Box component130Node0Box component130Node1Box
    .chi (25/32) (by rfl) (by rfl)
    component130Node0_sound component130Node1_sound

private noncomputable def component130Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (3/4), chiHi := (25/32) }

set_option maxRecDepth 1000000 in
private theorem component130Node3_sound : Sound component130Node3Box :=
  sound_of_literal_split component130Node3Box leaf6486Box leaf6487Box
    .k (43/16) (by rfl) (by rfl)
    leaf6486FlatSound leaf6487FlatSound

private noncomputable def component130Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (25/32), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component130Node4_sound : Sound component130Node4Box :=
  sound_of_literal_split component130Node4Box leaf6488Box leaf6489Box
    .k (43/16) (by rfl) (by rfl)
    leaf6488FlatSound leaf6489FlatSound

private noncomputable def component130Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (3/4), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component130Node5_sound : Sound component130Node5Box :=
  sound_of_literal_split component130Node5Box component130Node3Box component130Node4Box
    .chi (25/32) (by rfl) (by rfl)
    component130Node3_sound component130Node4_sound

private noncomputable def component130Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (11/4), chiLo := (3/4), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component130Node6_sound : Sound component130Node6Box :=
  sound_of_literal_split component130Node6Box component130Node2Box component130Node5Box
    .k (21/8) (by rfl) (by rfl)
    component130Node2_sound component130Node5_sound

private noncomputable def component130Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (13/16), chiHi := (27/32) }

set_option maxRecDepth 1000000 in
private theorem component130Node7_sound : Sound component130Node7Box :=
  sound_of_literal_split component130Node7Box leaf6490Box leaf6491Box
    .k (41/16) (by rfl) (by rfl)
    leaf6490FlatSound leaf6491FlatSound

private noncomputable def component130Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (27/32), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component130Node8_sound : Sound component130Node8Box :=
  sound_of_literal_split component130Node8Box leaf6492Box leaf6493Box
    .k (41/16) (by rfl) (by rfl)
    leaf6492FlatSound leaf6493FlatSound

private noncomputable def component130Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (13/16), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component130Node9_sound : Sound component130Node9Box :=
  sound_of_literal_split component130Node9Box component130Node7Box component130Node8Box
    .chi (27/32) (by rfl) (by rfl)
    component130Node7_sound component130Node8_sound

private noncomputable def component130Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (13/16), chiHi := (27/32) }

set_option maxRecDepth 1000000 in
private theorem component130Node10_sound : Sound component130Node10Box :=
  sound_of_literal_split component130Node10Box leaf6494Box leaf6495Box
    .k (43/16) (by rfl) (by rfl)
    leaf6494FlatSound leaf6495FlatSound

private noncomputable def component130Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (27/32), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component130Node11_sound : Sound component130Node11Box :=
  sound_of_literal_split component130Node11Box leaf6496Box leaf6497Box
    .k (43/16) (by rfl) (by rfl)
    leaf6496FlatSound leaf6497FlatSound

private noncomputable def component130Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (13/16), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component130Node12_sound : Sound component130Node12Box :=
  sound_of_literal_split component130Node12Box component130Node10Box component130Node11Box
    .chi (27/32) (by rfl) (by rfl)
    component130Node10_sound component130Node11_sound

private noncomputable def component130Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (11/4), chiLo := (13/16), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component130Node13_sound : Sound component130Node13Box :=
  sound_of_literal_split component130Node13Box component130Node9Box component130Node12Box
    .k (21/8) (by rfl) (by rfl)
    component130Node9_sound component130Node12_sound

private noncomputable def component130Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (11/4), chiLo := (3/4), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component130Node14_sound : Sound component130Node14Box :=
  sound_of_literal_split component130Node14Box component130Node6Box component130Node13Box
    .chi (13/16) (by rfl) (by rfl)
    component130Node6_sound component130Node13_sound

private noncomputable def component130Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (3/4), chiHi := (25/32) }

set_option maxRecDepth 1000000 in
private theorem component130Node15_sound : Sound component130Node15Box :=
  sound_of_literal_split component130Node15Box leaf6499Box leaf6500Box
    .chi (49/64) (by rfl) (by rfl)
    leaf6499FlatSound leaf6500FlatSound

private noncomputable def component130Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (3/4), chiHi := (25/32) }

set_option maxRecDepth 1000000 in
private theorem component130Node16_sound : Sound component130Node16Box :=
  sound_of_literal_split component130Node16Box leaf6498Box component130Node15Box
    .k (45/16) (by rfl) (by rfl)
    leaf6498FlatSound component130Node15_sound

private noncomputable def component130Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (25/32), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component130Node17_sound : Sound component130Node17Box :=
  sound_of_literal_split component130Node17Box leaf6501Box leaf6502Box
    .k (45/16) (by rfl) (by rfl)
    leaf6501FlatSound leaf6502FlatSound

private noncomputable def component130Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (3/4), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component130Node18_sound : Sound component130Node18Box :=
  sound_of_literal_split component130Node18Box component130Node16Box component130Node17Box
    .chi (25/32) (by rfl) (by rfl)
    component130Node16_sound component130Node17_sound

private noncomputable def component130Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (3/4), chiHi := (25/32) }

set_option maxRecDepth 1000000 in
private theorem component130Node19_sound : Sound component130Node19Box :=
  sound_of_literal_split component130Node19Box leaf6503Box leaf6504Box
    .chi (49/64) (by rfl) (by rfl)
    leaf6503FlatSound leaf6504FlatSound

private noncomputable def component130Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (3/4), chiHi := (25/32) }

set_option maxRecDepth 1000000 in
private theorem component130Node20_sound : Sound component130Node20Box :=
  sound_of_literal_split component130Node20Box leaf6505Box leaf6506Box
    .chi (49/64) (by rfl) (by rfl)
    leaf6505FlatSound leaf6506FlatSound

private noncomputable def component130Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (3/4), chiHi := (25/32) }

set_option maxRecDepth 1000000 in
private theorem component130Node21_sound : Sound component130Node21Box :=
  sound_of_literal_split component130Node21Box component130Node19Box component130Node20Box
    .k (47/16) (by rfl) (by rfl)
    component130Node19_sound component130Node20_sound

private noncomputable def component130Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (25/32), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component130Node22_sound : Sound component130Node22Box :=
  sound_of_literal_split component130Node22Box leaf6507Box leaf6508Box
    .k (47/16) (by rfl) (by rfl)
    leaf6507FlatSound leaf6508FlatSound

private noncomputable def component130Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (3/4), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component130Node23_sound : Sound component130Node23Box :=
  sound_of_literal_split component130Node23Box component130Node21Box component130Node22Box
    .chi (25/32) (by rfl) (by rfl)
    component130Node21_sound component130Node22_sound

private noncomputable def component130Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (3), chiLo := (3/4), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component130Node24_sound : Sound component130Node24Box :=
  sound_of_literal_split component130Node24Box component130Node18Box component130Node23Box
    .k (23/8) (by rfl) (by rfl)
    component130Node18_sound component130Node23_sound

private noncomputable def component130Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (13/16), chiHi := (27/32) }

set_option maxRecDepth 1000000 in
private theorem component130Node25_sound : Sound component130Node25Box :=
  sound_of_literal_split component130Node25Box leaf6509Box leaf6510Box
    .k (45/16) (by rfl) (by rfl)
    leaf6509FlatSound leaf6510FlatSound

private noncomputable def component130Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (27/32), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component130Node26_sound : Sound component130Node26Box :=
  sound_of_literal_split component130Node26Box leaf6511Box leaf6512Box
    .k (45/16) (by rfl) (by rfl)
    leaf6511FlatSound leaf6512FlatSound

private noncomputable def component130Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (13/16), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component130Node27_sound : Sound component130Node27Box :=
  sound_of_literal_split component130Node27Box component130Node25Box component130Node26Box
    .chi (27/32) (by rfl) (by rfl)
    component130Node25_sound component130Node26_sound

private noncomputable def component130Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (13/16), chiHi := (27/32) }

set_option maxRecDepth 1000000 in
private theorem component130Node28_sound : Sound component130Node28Box :=
  sound_of_literal_split component130Node28Box leaf6513Box leaf6514Box
    .k (47/16) (by rfl) (by rfl)
    leaf6513FlatSound leaf6514FlatSound

private noncomputable def component130Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (27/32), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component130Node29_sound : Sound component130Node29Box :=
  sound_of_literal_split component130Node29Box leaf6515Box leaf6516Box
    .k (47/16) (by rfl) (by rfl)
    leaf6515FlatSound leaf6516FlatSound

private noncomputable def component130Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (13/16), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component130Node30_sound : Sound component130Node30Box :=
  sound_of_literal_split component130Node30Box component130Node28Box component130Node29Box
    .chi (27/32) (by rfl) (by rfl)
    component130Node28_sound component130Node29_sound

private noncomputable def component130Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (3), chiLo := (13/16), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component130Node31_sound : Sound component130Node31Box :=
  sound_of_literal_split component130Node31Box component130Node27Box component130Node30Box
    .k (23/8) (by rfl) (by rfl)
    component130Node27_sound component130Node30_sound

private noncomputable def component130Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (3), chiLo := (3/4), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component130Node32_sound : Sound component130Node32Box :=
  sound_of_literal_split component130Node32Box component130Node24Box component130Node31Box
    .chi (13/16) (by rfl) (by rfl)
    component130Node24_sound component130Node31_sound

noncomputable def component130Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (3), chiLo := (3/4), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
theorem component130_sound : Sound component130Box :=
  sound_of_literal_split component130Box component130Node14Box component130Node32Box
    .k (11/4) (by rfl) (by rfl)
    component130Node14_sound component130Node32_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
