import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch6
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheSKBatch3

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

private noncomputable def leaf2882Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (241/64), chiLo := (5/32), chiHi := (41/256) }

private noncomputable def leaf2882Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742387/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486778880) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1702815695/1073741824) }, upper := { exponent := 0, mantissa := (26265/16384) } }, logOuter := sk225LogOuterCertificate, logK := sk225LogKCertificate, logChi := chi183LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54974163251/54973557760) } }, logDArg := sk225LogDArgCertificate }

private noncomputable def leaf2882InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2882LocalValidity :
    LeafFacts leaf2882Box leaf2882Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2882Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486778880) }) = true
      norm_num [leaf2882Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2882CertificateValid :
    WideCertificateValid leaf2882Box leaf2882Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk225ValidityFacts chi183ValidityFacts
    leaf2882LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2882CoverageChecked :
    coverageCheck (innerAD leaf2882Box) leaf2882InnerLog = true := by
  rfl'

private theorem leaf2882InnerLogValid :
    leaf2882InnerLog.Valid 8 (innerAD leaf2882Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2882CoverageChecked

private noncomputable def leaf2882InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814633/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2882InputLogOnePlusV_eq :
    leaf2882InputLogOnePlusV = outerEnclosure 24
      (leaf2882Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2882RoundedFacts : LeafRoundedFacts 8
    leaf2882Certificate.logOnePlusV leaf2882InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2882InputLogOnePlusV_eq }

private noncomputable def leaf2882Inputs : Inputs :=
  inputsOfCaches globalInput sk225RoundedInputs
    chi183InputQChi innerPair50Input
    leaf2882InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2882LowerChecked :
    lowerCheck 24 leaf2882Box leaf2882Inputs = true := by
  rfl'

private theorem leaf2882CoversExact : CoversExact 8
    leaf2882Box leaf2882Certificate leaf2882InnerLog leaf2882Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk225RoundedFacts chi183RoundedFacts
    innerPair50RoundedFacts leaf2882RoundedFacts (by rfl)

private theorem leaf2882FlatSound : Sound leaf2882Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2882CertificateValid
    leaf2882InnerLogValid leaf2882CoversExact leaf2882LowerChecked

private noncomputable def leaf2883Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (241/64), kHi := (121/32), chiLo := (5/32), chiHi := (41/256) }

private noncomputable def leaf2883Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742389/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45811291136) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1705436973/1073741824) }, upper := { exponent := 0, mantissa := (13153/8192) } }, logOuter := sk226LogOuterCertificate, logK := sk226LogKCertificate, logChi := chi183LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623598421/91622582272) } }, logDArg := sk226LogDArgCertificate }

private noncomputable def leaf2883InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2883LocalValidity :
    LeafFacts leaf2883Box leaf2883Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2883Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45811291136) }) = true
      norm_num [leaf2883Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2883CertificateValid :
    WideCertificateValid leaf2883Box leaf2883Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk226ValidityFacts chi183ValidityFacts
    leaf2883LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2883CoverageChecked :
    coverageCheck (innerAD leaf2883Box) leaf2883InnerLog = true := by
  rfl'

private theorem leaf2883InnerLogValid :
    leaf2883InnerLog.Valid 8 (innerAD leaf2883Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2883CoverageChecked

private noncomputable def leaf2883InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629267/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2883InputLogOnePlusV_eq :
    leaf2883InputLogOnePlusV = outerEnclosure 24
      (leaf2883Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2883RoundedFacts : LeafRoundedFacts 8
    leaf2883Certificate.logOnePlusV leaf2883InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2883InputLogOnePlusV_eq }

private noncomputable def leaf2883Inputs : Inputs :=
  inputsOfCaches globalInput sk226RoundedInputs
    chi183InputQChi innerPair50Input
    leaf2883InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2883LowerChecked :
    lowerCheck 24 leaf2883Box leaf2883Inputs = true := by
  rfl'

private theorem leaf2883CoversExact : CoversExact 8
    leaf2883Box leaf2883Certificate leaf2883InnerLog leaf2883Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk226RoundedFacts chi183RoundedFacts
    innerPair50RoundedFacts leaf2883RoundedFacts (by rfl)

private theorem leaf2883FlatSound : Sound leaf2883Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2883CertificateValid
    leaf2883InnerLogValid leaf2883CoversExact leaf2883LowerChecked

private noncomputable def leaf2884Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (241/64), chiLo := (41/256), chiHi := (21/128) }

private noncomputable def leaf2884Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742389/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433771008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1718543373/1073741824) }, upper := { exponent := 0, mantissa := (13253/8192) } }, logOuter := sk225LogOuterCertificate, logK := sk225LogKCertificate, logChi := chi184LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870692863/274867542016) } }, logDArg := sk225LogDArgCertificate }

private noncomputable def leaf2884InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2884LocalValidity :
    LeafFacts leaf2884Box leaf2884Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2884Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433771008) }) = true
      norm_num [leaf2884Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2884CertificateValid :
    WideCertificateValid leaf2884Box leaf2884Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk225ValidityFacts chi184ValidityFacts
    leaf2884LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2884CoverageChecked :
    coverageCheck (innerAD leaf2884Box) leaf2884InnerLog = true := by
  rfl'

private theorem leaf2884InnerLogValid :
    leaf2884InnerLog.Valid 8 (innerAD leaf2884Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2884CoverageChecked

private noncomputable def leaf2884InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629273/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2884InputLogOnePlusV_eq :
    leaf2884InputLogOnePlusV = outerEnclosure 24
      (leaf2884Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2884RoundedFacts : LeafRoundedFacts 8
    leaf2884Certificate.logOnePlusV leaf2884InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2884InputLogOnePlusV_eq }

private noncomputable def leaf2884Inputs : Inputs :=
  inputsOfCaches globalInput sk225RoundedInputs
    chi184InputQChi innerPair50Input
    leaf2884InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2884LowerChecked :
    lowerCheck 24 leaf2884Box leaf2884Inputs = true := by
  rfl'

private theorem leaf2884CoversExact : CoversExact 8
    leaf2884Box leaf2884Certificate leaf2884InnerLog leaf2884Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk225RoundedFacts chi184RoundedFacts
    innerPair50RoundedFacts leaf2884RoundedFacts (by rfl)

private theorem leaf2884FlatSound : Sound leaf2884Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2884CertificateValid
    leaf2884InnerLogValid leaf2884CoversExact leaf2884LowerChecked

private noncomputable def leaf2885Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (241/64), kHi := (121/32), chiLo := (41/256), chiHi := (21/128) }

private noncomputable def leaf2885Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742391/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433749504) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1721230183/1073741824) }, upper := { exponent := 0, mantissa := (6637/4096) } }, logOuter := sk226LogOuterCertificate, logK := sk226LogKCertificate, logChi := chi184LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870671359/274867499008) } }, logDArg := sk226LogDArgCertificate }

private noncomputable def leaf2885InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2885LocalValidity :
    LeafFacts leaf2885Box leaf2885Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2885Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433749504) }) = true
      norm_num [leaf2885Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2885CertificateValid :
    WideCertificateValid leaf2885Box leaf2885Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk226ValidityFacts chi184ValidityFacts
    leaf2885LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2885CoverageChecked :
    coverageCheck (innerAD leaf2885Box) leaf2885InnerLog = true := by
  rfl'

private theorem leaf2885InnerLogValid :
    leaf2885InnerLog.Valid 8 (innerAD leaf2885Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2885CoverageChecked

private noncomputable def leaf2885InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814637/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2885InputLogOnePlusV_eq :
    leaf2885InputLogOnePlusV = outerEnclosure 24
      (leaf2885Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2885RoundedFacts : LeafRoundedFacts 8
    leaf2885Certificate.logOnePlusV leaf2885InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2885InputLogOnePlusV_eq }

private noncomputable def leaf2885Inputs : Inputs :=
  inputsOfCaches globalInput sk226RoundedInputs
    chi184InputQChi innerPair50Input
    leaf2885InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2885LowerChecked :
    lowerCheck 24 leaf2885Box leaf2885Inputs = true := by
  rfl'

private theorem leaf2885CoversExact : CoversExact 8
    leaf2885Box leaf2885Certificate leaf2885InnerLog leaf2885Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk226RoundedFacts chi184RoundedFacts
    innerPair50RoundedFacts leaf2885RoundedFacts (by rfl)

private theorem leaf2885FlatSound : Sound leaf2885Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2885CertificateValid
    leaf2885InnerLogValid leaf2885CoversExact leaf2885LowerChecked

private noncomputable def leaf2886Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (243/64), chiLo := (5/32), chiHi := (41/256) }

private noncomputable def leaf2886Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742391/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433852416) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1708058251/1073741824) }, upper := { exponent := 0, mantissa := (26347/16384) } }, logOuter := sk227LogOuterCertificate, logK := sk227LogKCertificate, logChi := chi183LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870774271/274867704832) } }, logDArg := sk227LogDArgCertificate }

private noncomputable def leaf2886InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2886LocalValidity :
    LeafFacts leaf2886Box leaf2886Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2886Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433852416) }) = true
      norm_num [leaf2886Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2886CertificateValid :
    WideCertificateValid leaf2886Box leaf2886Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk227ValidityFacts chi183ValidityFacts
    leaf2886LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2886CoverageChecked :
    coverageCheck (innerAD leaf2886Box) leaf2886InnerLog = true := by
  rfl'

private theorem leaf2886InnerLogValid :
    leaf2886InnerLog.Valid 8 (innerAD leaf2886Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2886CoverageChecked

private noncomputable def leaf2886InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907317/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2886InputLogOnePlusV_eq :
    leaf2886InputLogOnePlusV = outerEnclosure 24
      (leaf2886Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2886RoundedFacts : LeafRoundedFacts 8
    leaf2886Certificate.logOnePlusV leaf2886InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2886InputLogOnePlusV_eq }

private noncomputable def leaf2886Inputs : Inputs :=
  inputsOfCaches globalInput sk227RoundedInputs
    chi183InputQChi innerPair50Input
    leaf2886InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2886LowerChecked :
    lowerCheck 24 leaf2886Box leaf2886Inputs = true := by
  rfl'

private theorem leaf2886CoversExact : CoversExact 8
    leaf2886Box leaf2886Certificate leaf2886InnerLog leaf2886Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk227RoundedFacts chi183RoundedFacts
    innerPair50RoundedFacts leaf2886RoundedFacts (by rfl)

private theorem leaf2886FlatSound : Sound leaf2886Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2886CertificateValid
    leaf2886InnerLogValid leaf2886CoversExact leaf2886LowerChecked

private noncomputable def leaf2887Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (243/64), kHi := (61/16), chiLo := (5/32), chiHi := (41/256) }

private noncomputable def leaf2887Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742393/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433831424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1710679529/1073741824) }, upper := { exponent := 0, mantissa := (6597/4096) } }, logOuter := sk228LogOuterCertificate, logK := sk228LogKCertificate, logChi := chi183LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870753279/274867662848) } }, logDArg := sk228LogDArgCertificate }

private noncomputable def leaf2887InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2887LocalValidity :
    LeafFacts leaf2887Box leaf2887Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2887Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433831424) }) = true
      norm_num [leaf2887Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2887CertificateValid :
    WideCertificateValid leaf2887Box leaf2887Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk228ValidityFacts chi183ValidityFacts
    leaf2887LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2887CoverageChecked :
    coverageCheck (innerAD leaf2887Box) leaf2887InnerLog = true := by
  rfl'

private theorem leaf2887InnerLogValid :
    leaf2887InnerLog.Valid 8 (innerAD leaf2887Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2887CoverageChecked

private noncomputable def leaf2887InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629269/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2887InputLogOnePlusV_eq :
    leaf2887InputLogOnePlusV = outerEnclosure 24
      (leaf2887Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2887RoundedFacts : LeafRoundedFacts 8
    leaf2887Certificate.logOnePlusV leaf2887InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2887InputLogOnePlusV_eq }

private noncomputable def leaf2887Inputs : Inputs :=
  inputsOfCaches globalInput sk228RoundedInputs
    chi183InputQChi innerPair50Input
    leaf2887InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2887LowerChecked :
    lowerCheck 24 leaf2887Box leaf2887Inputs = true := by
  rfl'

private theorem leaf2887CoversExact : CoversExact 8
    leaf2887Box leaf2887Certificate leaf2887InnerLog leaf2887Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk228RoundedFacts chi183RoundedFacts
    innerPair50RoundedFacts leaf2887RoundedFacts (by rfl)

private theorem leaf2887FlatSound : Sound leaf2887Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2887CertificateValid
    leaf2887InnerLogValid leaf2887CoversExact leaf2887LowerChecked

private noncomputable def leaf2888Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (243/64), chiLo := (41/256), chiHi := (21/128) }

private noncomputable def leaf2888Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742393/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486745600) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1723916993/1073741824) }, upper := { exponent := 0, mantissa := (13295/8192) } }, logOuter := sk227LogOuterCertificate, logK := sk227LogKCertificate, logChi := chi184LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54974129971/54973491200) } }, logDArg := sk227LogDArgCertificate }

private noncomputable def leaf2888InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2888LocalValidity :
    LeafFacts leaf2888Box leaf2888Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2888Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486745600) }) = true
      norm_num [leaf2888Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2888CertificateValid :
    WideCertificateValid leaf2888Box leaf2888Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk227ValidityFacts chi184ValidityFacts
    leaf2888LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2888CoverageChecked :
    coverageCheck (innerAD leaf2888Box) leaf2888InnerLog = true := by
  rfl'

private theorem leaf2888InnerLogValid :
    leaf2888InnerLog.Valid 8 (innerAD leaf2888Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2888CoverageChecked

private noncomputable def leaf2888InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907319/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2888InputLogOnePlusV_eq :
    leaf2888InputLogOnePlusV = outerEnclosure 24
      (leaf2888Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2888RoundedFacts : LeafRoundedFacts 8
    leaf2888Certificate.logOnePlusV leaf2888InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2888InputLogOnePlusV_eq }

private noncomputable def leaf2888Inputs : Inputs :=
  inputsOfCaches globalInput sk227RoundedInputs
    chi184InputQChi innerPair50Input
    leaf2888InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2888LowerChecked :
    lowerCheck 24 leaf2888Box leaf2888Inputs = true := by
  rfl'

private theorem leaf2888CoversExact : CoversExact 8
    leaf2888Box leaf2888Certificate leaf2888InnerLog leaf2888Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk227RoundedFacts chi184RoundedFacts
    innerPair50RoundedFacts leaf2888RoundedFacts (by rfl)

private theorem leaf2888FlatSound : Sound leaf2888Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2888CertificateValid
    leaf2888InnerLogValid leaf2888CoversExact leaf2888LowerChecked

private noncomputable def leaf2889Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (243/64), kHi := (61/16), chiLo := (41/256), chiHi := (21/128) }

private noncomputable def leaf2889Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742395/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433706496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1726603803/1073741824) }, upper := { exponent := 0, mantissa := (3329/2048) } }, logOuter := sk228LogOuterCertificate, logK := sk228LogKCertificate, logChi := chi184LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870628351/274867412992) } }, logDArg := sk228LogDArgCertificate }

private noncomputable def leaf2889InnerLog : WideLogData :=
  innerPair157Data

set_option maxRecDepth 1000000 in
private theorem leaf2889LocalValidity :
    LeafFacts leaf2889Box leaf2889Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2889Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433706496) }) = true
      norm_num [leaf2889Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2889CertificateValid :
    WideCertificateValid leaf2889Box leaf2889Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk228ValidityFacts chi184ValidityFacts
    leaf2889LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2889CoverageChecked :
    coverageCheck (innerAD leaf2889Box) leaf2889InnerLog = true := by
  rfl'

private theorem leaf2889InnerLogValid :
    leaf2889InnerLog.Valid 8 (innerAD leaf2889Box) :=
  wideLogDataValid_of_cachedCheck endpoint44PositiveFacts
    endpoint45PositiveFacts.valid leaf2889CoverageChecked

private noncomputable def leaf2889InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629277/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2889InputLogOnePlusV_eq :
    leaf2889InputLogOnePlusV = outerEnclosure 24
      (leaf2889Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2889RoundedFacts : LeafRoundedFacts 8
    leaf2889Certificate.logOnePlusV leaf2889InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2889InputLogOnePlusV_eq }

private noncomputable def leaf2889Inputs : Inputs :=
  inputsOfCaches globalInput sk228RoundedInputs
    chi184InputQChi innerPair157Input
    leaf2889InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2889LowerChecked :
    lowerCheck 24 leaf2889Box leaf2889Inputs = true := by
  rfl'

private theorem leaf2889CoversExact : CoversExact 8
    leaf2889Box leaf2889Certificate leaf2889InnerLog leaf2889Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk228RoundedFacts chi184RoundedFacts
    innerPair157RoundedFacts leaf2889RoundedFacts (by rfl)

private theorem leaf2889FlatSound : Sound leaf2889Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2889CertificateValid
    leaf2889InnerLogValid leaf2889CoversExact leaf2889LowerChecked

private noncomputable def leaf2890Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (241/64), chiLo := (21/128), chiHi := (43/256) }

private noncomputable def leaf2890Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742391/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45811215872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1734271051/1073741824) }, upper := { exponent := 0, mantissa := (26747/16384) } }, logOuter := sk225LogOuterCertificate, logK := sk225LogKCertificate, logChi := chi185LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623523157/91622431744) } }, logDArg := sk225LogDArgCertificate }

private noncomputable def leaf2890InnerLog : WideLogData :=
  innerPair166Data

set_option maxRecDepth 1000000 in
private theorem leaf2890LocalValidity :
    LeafFacts leaf2890Box leaf2890Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2890Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45811215872) }) = true
      norm_num [leaf2890Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2890CertificateValid :
    WideCertificateValid leaf2890Box leaf2890Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk225ValidityFacts chi185ValidityFacts
    leaf2890LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2890CoverageChecked :
    coverageCheck (innerAD leaf2890Box) leaf2890InnerLog = true := by
  rfl'

private theorem leaf2890InnerLogValid :
    leaf2890InnerLog.Valid 8 (innerAD leaf2890Box) :=
  wideLogDataValid_of_cachedCheck endpoint46PositiveFacts
    endpoint45PositiveFacts.valid leaf2890CoverageChecked

private noncomputable def leaf2890InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629281/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2890InputLogOnePlusV_eq :
    leaf2890InputLogOnePlusV = outerEnclosure 24
      (leaf2890Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2890RoundedFacts : LeafRoundedFacts 8
    leaf2890Certificate.logOnePlusV leaf2890InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2890InputLogOnePlusV_eq }

private noncomputable def leaf2890Inputs : Inputs :=
  inputsOfCaches globalInput sk225RoundedInputs
    chi185InputQChi innerPair166Input
    leaf2890InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2890LowerChecked :
    lowerCheck 24 leaf2890Box leaf2890Inputs = true := by
  rfl'

private theorem leaf2890CoversExact : CoversExact 8
    leaf2890Box leaf2890Certificate leaf2890InnerLog leaf2890Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk225RoundedFacts chi185RoundedFacts
    innerPair166RoundedFacts leaf2890RoundedFacts (by rfl)

private theorem leaf2890FlatSound : Sound leaf2890Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2890CertificateValid
    leaf2890InnerLogValid leaf2890CoversExact leaf2890LowerChecked

private noncomputable def leaf2891Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (241/64), kHi := (121/32), chiLo := (21/128), chiHi := (43/256) }

private noncomputable def leaf2891Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742393/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486725120) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1737023393/1073741824) }, upper := { exponent := 0, mantissa := (13395/8192) } }, logOuter := sk226LogOuterCertificate, logK := sk226LogKCertificate, logChi := chi185LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54974109491/54973450240) } }, logDArg := sk226LogDArgCertificate }

private noncomputable def leaf2891InnerLog : WideLogData :=
  innerPair166Data

set_option maxRecDepth 1000000 in
private theorem leaf2891LocalValidity :
    LeafFacts leaf2891Box leaf2891Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2891Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486725120) }) = true
      norm_num [leaf2891Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2891CertificateValid :
    WideCertificateValid leaf2891Box leaf2891Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk226ValidityFacts chi185ValidityFacts
    leaf2891LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2891CoverageChecked :
    coverageCheck (innerAD leaf2891Box) leaf2891InnerLog = true := by
  rfl'

private theorem leaf2891InnerLogValid :
    leaf2891InnerLog.Valid 8 (innerAD leaf2891Box) :=
  wideLogDataValid_of_cachedCheck endpoint46PositiveFacts
    endpoint45PositiveFacts.valid leaf2891CoverageChecked

private noncomputable def leaf2891InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814641/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2891InputLogOnePlusV_eq :
    leaf2891InputLogOnePlusV = outerEnclosure 24
      (leaf2891Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2891RoundedFacts : LeafRoundedFacts 8
    leaf2891Certificate.logOnePlusV leaf2891InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2891InputLogOnePlusV_eq }

private noncomputable def leaf2891Inputs : Inputs :=
  inputsOfCaches globalInput sk226RoundedInputs
    chi185InputQChi innerPair166Input
    leaf2891InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2891LowerChecked :
    lowerCheck 24 leaf2891Box leaf2891Inputs = true := by
  rfl'

private theorem leaf2891CoversExact : CoversExact 8
    leaf2891Box leaf2891Certificate leaf2891InnerLog leaf2891Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk226RoundedFacts chi185RoundedFacts
    innerPair166RoundedFacts leaf2891RoundedFacts (by rfl)

private theorem leaf2891FlatSound : Sound leaf2891Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2891CertificateValid
    leaf2891InnerLogValid leaf2891CoversExact leaf2891LowerChecked

private noncomputable def leaf2892Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (241/64), chiLo := (43/256), chiHi := (11/64) }

private noncomputable def leaf2892Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742393/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433524224) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1749998729/1073741824) }, upper := { exponent := 0, mantissa := (6747/4096) } }, logOuter := sk225LogOuterCertificate, logK := sk225LogKCertificate, logChi := chi186LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870446079/274867048448) } }, logDArg := sk225LogDArgCertificate }

private noncomputable def leaf2892InnerLog : WideLogData :=
  innerPair61Data

set_option maxRecDepth 1000000 in
private theorem leaf2892LocalValidity :
    LeafFacts leaf2892Box leaf2892Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2892Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433524224) }) = true
      norm_num [leaf2892Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2892CertificateValid :
    WideCertificateValid leaf2892Box leaf2892Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk225ValidityFacts chi186ValidityFacts
    leaf2892LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2892CoverageChecked :
    coverageCheck (innerAD leaf2892Box) leaf2892InnerLog = true := by
  rfl'

private theorem leaf2892InnerLogValid :
    leaf2892InnerLog.Valid 8 (innerAD leaf2892Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint48PositiveFacts.valid leaf2892CoverageChecked

private noncomputable def leaf2892InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453661/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf2892InputLogOnePlusV_eq :
    leaf2892InputLogOnePlusV = outerEnclosure 24
      (leaf2892Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2892RoundedFacts : LeafRoundedFacts 8
    leaf2892Certificate.logOnePlusV leaf2892InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2892InputLogOnePlusV_eq }

private noncomputable def leaf2892Inputs : Inputs :=
  inputsOfCaches globalInput sk225RoundedInputs
    chi186InputQChi innerPair61Input
    leaf2892InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2892LowerChecked :
    lowerCheck 24 leaf2892Box leaf2892Inputs = true := by
  rfl'

private theorem leaf2892CoversExact : CoversExact 8
    leaf2892Box leaf2892Certificate leaf2892InnerLog leaf2892Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk225RoundedFacts chi186RoundedFacts
    innerPair61RoundedFacts leaf2892RoundedFacts (by rfl)

private theorem leaf2892FlatSound : Sound leaf2892Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2892CertificateValid
    leaf2892InnerLogValid leaf2892CoversExact leaf2892LowerChecked

private noncomputable def leaf2893Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (241/64), kHi := (121/32), chiLo := (43/256), chiHi := (11/64) }

private noncomputable def leaf2893Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742395/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45811167232) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1752816603/1073741824) }, upper := { exponent := 0, mantissa := (3379/2048) } }, logOuter := sk226LogOuterCertificate, logK := sk226LogKCertificate, logChi := chi186LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623474517/91622334464) } }, logDArg := sk226LogDArgCertificate }

private noncomputable def leaf2893InnerLog : WideLogData :=
  innerPair61Data

set_option maxRecDepth 1000000 in
private theorem leaf2893LocalValidity :
    LeafFacts leaf2893Box leaf2893Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2893Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45811167232) }) = true
      norm_num [leaf2893Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2893CertificateValid :
    WideCertificateValid leaf2893Box leaf2893Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk226ValidityFacts chi186ValidityFacts
    leaf2893LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2893CoverageChecked :
    coverageCheck (innerAD leaf2893Box) leaf2893InnerLog = true := by
  rfl'

private theorem leaf2893InnerLogValid :
    leaf2893InnerLog.Valid 8 (innerAD leaf2893Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint48PositiveFacts.valid leaf2893CoverageChecked

private noncomputable def leaf2893InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814645/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2893InputLogOnePlusV_eq :
    leaf2893InputLogOnePlusV = outerEnclosure 24
      (leaf2893Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2893RoundedFacts : LeafRoundedFacts 8
    leaf2893Certificate.logOnePlusV leaf2893InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2893InputLogOnePlusV_eq }

private noncomputable def leaf2893Inputs : Inputs :=
  inputsOfCaches globalInput sk226RoundedInputs
    chi186InputQChi innerPair61Input
    leaf2893InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2893LowerChecked :
    lowerCheck 24 leaf2893Box leaf2893Inputs = true := by
  rfl'

private theorem leaf2893CoversExact : CoversExact 8
    leaf2893Box leaf2893Certificate leaf2893InnerLog leaf2893Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk226RoundedFacts chi186RoundedFacts
    innerPair61RoundedFacts leaf2893RoundedFacts (by rfl)

private theorem leaf2893FlatSound : Sound leaf2893Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2893CertificateValid
    leaf2893InnerLogValid leaf2893CoversExact leaf2893LowerChecked

private noncomputable def leaf2894Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (243/64), chiLo := (21/128), chiHi := (43/256) }

private noncomputable def leaf2894Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742395/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433603584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1739775735/1073741824) }, upper := { exponent := 0, mantissa := (26833/16384) } }, logOuter := sk227LogOuterCertificate, logK := sk227LogKCertificate, logChi := chi185LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870525439/274867207168) } }, logDArg := sk227LogDArgCertificate }

private noncomputable def leaf2894InnerLog : WideLogData :=
  innerPair166Data

set_option maxRecDepth 1000000 in
private theorem leaf2894LocalValidity :
    LeafFacts leaf2894Box leaf2894Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2894Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433603584) }) = true
      norm_num [leaf2894Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2894CertificateValid :
    WideCertificateValid leaf2894Box leaf2894Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk227ValidityFacts chi185ValidityFacts
    leaf2894LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2894CoverageChecked :
    coverageCheck (innerAD leaf2894Box) leaf2894InnerLog = true := by
  rfl'

private theorem leaf2894InnerLogValid :
    leaf2894InnerLog.Valid 8 (innerAD leaf2894Box) :=
  wideLogDataValid_of_cachedCheck endpoint46PositiveFacts
    endpoint45PositiveFacts.valid leaf2894CoverageChecked

private noncomputable def leaf2894InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629283/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2894InputLogOnePlusV_eq :
    leaf2894InputLogOnePlusV = outerEnclosure 24
      (leaf2894Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2894RoundedFacts : LeafRoundedFacts 8
    leaf2894Certificate.logOnePlusV leaf2894InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2894InputLogOnePlusV_eq }

private noncomputable def leaf2894Inputs : Inputs :=
  inputsOfCaches globalInput sk227RoundedInputs
    chi185InputQChi innerPair166Input
    leaf2894InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2894LowerChecked :
    lowerCheck 24 leaf2894Box leaf2894Inputs = true := by
  rfl'

private theorem leaf2894CoversExact : CoversExact 8
    leaf2894Box leaf2894Certificate leaf2894InnerLog leaf2894Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk227RoundedFacts chi185RoundedFacts
    innerPair166RoundedFacts leaf2894RoundedFacts (by rfl)

private theorem leaf2894FlatSound : Sound leaf2894Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2894CertificateValid
    leaf2894InnerLogValid leaf2894CoversExact leaf2894LowerChecked

private noncomputable def leaf2895Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (243/64), kHi := (61/16), chiLo := (21/128), chiHi := (43/256) }

private noncomputable def leaf2895Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742397/1073741824) }, vSqrt := { lower := (8191/8192), upper := (15270769095/15270397952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1742528077/1073741824) }, upper := { exponent := 0, mantissa := (6719/4096) } }, logOuter := sk228LogOuterCertificate, logK := sk228LogKCertificate, logChi := chi185LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (30541167047/30540795904) } }, logDArg := sk228LogDArgCertificate }

private noncomputable def leaf2895InnerLog : WideLogData :=
  innerPair166Data

set_option maxRecDepth 1000000 in
private theorem leaf2895LocalValidity :
    LeafFacts leaf2895Box leaf2895Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2895Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (15270769095/15270397952) }) = true
      norm_num [leaf2895Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2895CertificateValid :
    WideCertificateValid leaf2895Box leaf2895Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk228ValidityFacts chi185ValidityFacts
    leaf2895LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2895CoverageChecked :
    coverageCheck (innerAD leaf2895Box) leaf2895InnerLog = true := by
  rfl'

private theorem leaf2895InnerLogValid :
    leaf2895InnerLog.Valid 8 (innerAD leaf2895Box) :=
  wideLogDataValid_of_cachedCheck endpoint46PositiveFacts
    endpoint45PositiveFacts.valid leaf2895CoverageChecked

private noncomputable def leaf2895InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629285/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2895InputLogOnePlusV_eq :
    leaf2895InputLogOnePlusV = outerEnclosure 24
      (leaf2895Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2895RoundedFacts : LeafRoundedFacts 8
    leaf2895Certificate.logOnePlusV leaf2895InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2895InputLogOnePlusV_eq }

private noncomputable def leaf2895Inputs : Inputs :=
  inputsOfCaches globalInput sk228RoundedInputs
    chi185InputQChi innerPair166Input
    leaf2895InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2895LowerChecked :
    lowerCheck 24 leaf2895Box leaf2895Inputs = true := by
  rfl'

private theorem leaf2895CoversExact : CoversExact 8
    leaf2895Box leaf2895Certificate leaf2895InnerLog leaf2895Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk228RoundedFacts chi185RoundedFacts
    innerPair166RoundedFacts leaf2895RoundedFacts (by rfl)

private theorem leaf2895FlatSound : Sound leaf2895Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2895CertificateValid
    leaf2895InnerLogValid leaf2895CoversExact leaf2895LowerChecked

private noncomputable def leaf2896Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (243/64), chiLo := (43/256), chiHi := (11/64) }

private noncomputable def leaf2896Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742397/1073741824) }, vSqrt := { lower := (8191/8192), upper := (8084524815/8084322304) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1755634477/1073741824) }, upper := { exponent := 0, mantissa := (6769/4096) } }, logOuter := sk227LogOuterCertificate, logK := sk227LogKCertificate, logChi := chi186LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16168847119/16168644608) } }, logDArg := sk227LogDArgCertificate }

private noncomputable def leaf2896InnerLog : WideLogData :=
  innerPair61Data

set_option maxRecDepth 1000000 in
private theorem leaf2896LocalValidity :
    LeafFacts leaf2896Box leaf2896Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2896Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8084524815/8084322304) }) = true
      norm_num [leaf2896Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2896CertificateValid :
    WideCertificateValid leaf2896Box leaf2896Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk227ValidityFacts chi186ValidityFacts
    leaf2896LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2896CoverageChecked :
    coverageCheck (innerAD leaf2896Box) leaf2896InnerLog = true := by
  rfl'

private theorem leaf2896InnerLogValid :
    leaf2896InnerLog.Valid 8 (innerAD leaf2896Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint48PositiveFacts.valid leaf2896CoverageChecked

private noncomputable def leaf2896InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629291/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2896InputLogOnePlusV_eq :
    leaf2896InputLogOnePlusV = outerEnclosure 24
      (leaf2896Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2896RoundedFacts : LeafRoundedFacts 8
    leaf2896Certificate.logOnePlusV leaf2896InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2896InputLogOnePlusV_eq }

private noncomputable def leaf2896Inputs : Inputs :=
  inputsOfCaches globalInput sk227RoundedInputs
    chi186InputQChi innerPair61Input
    leaf2896InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2896LowerChecked :
    lowerCheck 24 leaf2896Box leaf2896Inputs = true := by
  rfl'

private theorem leaf2896CoversExact : CoversExact 8
    leaf2896Box leaf2896Certificate leaf2896InnerLog leaf2896Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk227RoundedFacts chi186RoundedFacts
    innerPair61RoundedFacts leaf2896RoundedFacts (by rfl)

private theorem leaf2896FlatSound : Sound leaf2896Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2896CertificateValid
    leaf2896InnerLogValid leaf2896CoversExact leaf2896LowerChecked

private noncomputable def leaf2897Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (243/64), kHi := (61/16), chiLo := (43/256), chiHi := (11/64) }

private noncomputable def leaf2897Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742399/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486691328) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1758452351/1073741824) }, upper := { exponent := 0, mantissa := (1695/1024) } }, logOuter := sk228LogOuterCertificate, logK := sk228LogKCertificate, logChi := chi186LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54974075699/54973382656) } }, logDArg := sk228LogDArgCertificate }

private noncomputable def leaf2897InnerLog : WideLogData :=
  innerPair61Data

set_option maxRecDepth 1000000 in
private theorem leaf2897LocalValidity :
    LeafFacts leaf2897Box leaf2897Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2897Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486691328) }) = true
      norm_num [leaf2897Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2897CertificateValid :
    WideCertificateValid leaf2897Box leaf2897Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk228ValidityFacts chi186ValidityFacts
    leaf2897LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2897CoverageChecked :
    coverageCheck (innerAD leaf2897Box) leaf2897InnerLog = true := by
  rfl'

private theorem leaf2897InnerLogValid :
    leaf2897InnerLog.Valid 8 (innerAD leaf2897Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint48PositiveFacts.valid leaf2897CoverageChecked

private noncomputable def leaf2897InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907323/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2897InputLogOnePlusV_eq :
    leaf2897InputLogOnePlusV = outerEnclosure 24
      (leaf2897Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2897RoundedFacts : LeafRoundedFacts 8
    leaf2897Certificate.logOnePlusV leaf2897InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2897InputLogOnePlusV_eq }

private noncomputable def leaf2897Inputs : Inputs :=
  inputsOfCaches globalInput sk228RoundedInputs
    chi186InputQChi innerPair61Input
    leaf2897InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2897LowerChecked :
    lowerCheck 24 leaf2897Box leaf2897Inputs = true := by
  rfl'

private theorem leaf2897CoversExact : CoversExact 8
    leaf2897Box leaf2897Certificate leaf2897InnerLog leaf2897Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk228RoundedFacts chi186RoundedFacts
    innerPair61RoundedFacts leaf2897RoundedFacts (by rfl)

private theorem leaf2897FlatSound : Sound leaf2897Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2897CertificateValid
    leaf2897InnerLogValid leaf2897CoversExact leaf2897LowerChecked

private noncomputable def leaf2898Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (245/64), chiLo := (5/32), chiHi := (41/256) }

private noncomputable def leaf2898Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742395/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45811270144) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1713300807/1073741824) }, upper := { exponent := 0, mantissa := (26429/16384) } }, logOuter := sk229LogOuterCertificate, logK := sk229LogKCertificate, logChi := chi183LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623577429/91622540288) } }, logDArg := sk229LogDArgCertificate }

private noncomputable def leaf2898InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2898LocalValidity :
    LeafFacts leaf2898Box leaf2898Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2898Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45811270144) }) = true
      norm_num [leaf2898Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2898CertificateValid :
    WideCertificateValid leaf2898Box leaf2898Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk229ValidityFacts chi183ValidityFacts
    leaf2898LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2898CoverageChecked :
    coverageCheck (innerAD leaf2898Box) leaf2898InnerLog = true := by
  rfl'

private theorem leaf2898InnerLogValid :
    leaf2898InnerLog.Valid 8 (innerAD leaf2898Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2898CoverageChecked

private noncomputable def leaf2898InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629271/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2898InputLogOnePlusV_eq :
    leaf2898InputLogOnePlusV = outerEnclosure 24
      (leaf2898Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2898RoundedFacts : LeafRoundedFacts 8
    leaf2898Certificate.logOnePlusV leaf2898InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2898InputLogOnePlusV_eq }

private noncomputable def leaf2898Inputs : Inputs :=
  inputsOfCaches globalInput sk229RoundedInputs
    chi183InputQChi innerPair50Input
    leaf2898InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2898LowerChecked :
    lowerCheck 24 leaf2898Box leaf2898Inputs = true := by
  rfl'

private theorem leaf2898CoversExact : CoversExact 8
    leaf2898Box leaf2898Certificate leaf2898InnerLog leaf2898Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk229RoundedFacts chi183RoundedFacts
    innerPair50RoundedFacts leaf2898RoundedFacts (by rfl)

private theorem leaf2898FlatSound : Sound leaf2898Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2898CertificateValid
    leaf2898InnerLogValid leaf2898CoversExact leaf2898LowerChecked

private noncomputable def leaf2899Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (245/64), kHi := (123/32), chiLo := (5/32), chiHi := (41/256) }

private noncomputable def leaf2899Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742397/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486757888) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1715922085/1073741824) }, upper := { exponent := 0, mantissa := (13235/8192) } }, logOuter := sk230LogOuterCertificate, logK := sk230LogKCertificate, logChi := chi183LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54974142259/54973515776) } }, logDArg := sk230LogDArgCertificate }

private noncomputable def leaf2899InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2899LocalValidity :
    LeafFacts leaf2899Box leaf2899Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2899Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486757888) }) = true
      norm_num [leaf2899Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2899CertificateValid :
    WideCertificateValid leaf2899Box leaf2899Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk230ValidityFacts chi183ValidityFacts
    leaf2899LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2899CoverageChecked :
    coverageCheck (innerAD leaf2899Box) leaf2899InnerLog = true := by
  rfl'

private theorem leaf2899InnerLogValid :
    leaf2899InnerLog.Valid 8 (innerAD leaf2899Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2899CoverageChecked

private noncomputable def leaf2899InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453659/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf2899InputLogOnePlusV_eq :
    leaf2899InputLogOnePlusV = outerEnclosure 24
      (leaf2899Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2899RoundedFacts : LeafRoundedFacts 8
    leaf2899Certificate.logOnePlusV leaf2899InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2899InputLogOnePlusV_eq }

private noncomputable def leaf2899Inputs : Inputs :=
  inputsOfCaches globalInput sk230RoundedInputs
    chi183InputQChi innerPair50Input
    leaf2899InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2899LowerChecked :
    lowerCheck 24 leaf2899Box leaf2899Inputs = true := by
  rfl'

private theorem leaf2899CoversExact : CoversExact 8
    leaf2899Box leaf2899Certificate leaf2899InnerLog leaf2899Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk230RoundedFacts chi183RoundedFacts
    innerPair50RoundedFacts leaf2899RoundedFacts (by rfl)

private theorem leaf2899FlatSound : Sound leaf2899Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2899CertificateValid
    leaf2899InnerLogValid leaf2899CoversExact leaf2899LowerChecked

private noncomputable def leaf2900Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (245/64), chiLo := (41/256), chiHi := (21/128) }

private noncomputable def leaf2900Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742397/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433684992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1729290613/1073741824) }, upper := { exponent := 0, mantissa := (13337/8192) } }, logOuter := sk229LogOuterCertificate, logK := sk229LogKCertificate, logChi := chi184LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870606847/274867369984) } }, logDArg := sk229LogDArgCertificate }

private noncomputable def leaf2900InnerLog : WideLogData :=
  innerPair166Data

set_option maxRecDepth 1000000 in
private theorem leaf2900LocalValidity :
    LeafFacts leaf2900Box leaf2900Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2900Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433684992) }) = true
      norm_num [leaf2900Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2900CertificateValid :
    WideCertificateValid leaf2900Box leaf2900Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk229ValidityFacts chi184ValidityFacts
    leaf2900LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2900CoverageChecked :
    coverageCheck (innerAD leaf2900Box) leaf2900InnerLog = true := by
  rfl'

private theorem leaf2900InnerLogValid :
    leaf2900InnerLog.Valid 8 (innerAD leaf2900Box) :=
  wideLogDataValid_of_cachedCheck endpoint46PositiveFacts
    endpoint45PositiveFacts.valid leaf2900CoverageChecked

private noncomputable def leaf2900InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814639/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2900InputLogOnePlusV_eq :
    leaf2900InputLogOnePlusV = outerEnclosure 24
      (leaf2900Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2900RoundedFacts : LeafRoundedFacts 8
    leaf2900Certificate.logOnePlusV leaf2900InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2900InputLogOnePlusV_eq }

private noncomputable def leaf2900Inputs : Inputs :=
  inputsOfCaches globalInput sk229RoundedInputs
    chi184InputQChi innerPair166Input
    leaf2900InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2900LowerChecked :
    lowerCheck 24 leaf2900Box leaf2900Inputs = true := by
  rfl'

private theorem leaf2900CoversExact : CoversExact 8
    leaf2900Box leaf2900Certificate leaf2900InnerLog leaf2900Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk229RoundedFacts chi184RoundedFacts
    innerPair166RoundedFacts leaf2900RoundedFacts (by rfl)

private theorem leaf2900FlatSound : Sound leaf2900Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2900CertificateValid
    leaf2900InnerLogValid leaf2900CoversExact leaf2900LowerChecked

private noncomputable def leaf2901Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (245/64), kHi := (123/32), chiLo := (41/256), chiHi := (21/128) }

private noncomputable def leaf2901Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742399/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433663488) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1731977423/1073741824) }, upper := { exponent := 0, mantissa := (6679/4096) } }, logOuter := sk230LogOuterCertificate, logK := sk230LogKCertificate, logChi := chi184LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870585343/274867326976) } }, logDArg := sk230LogDArgCertificate }

private noncomputable def leaf2901InnerLog : WideLogData :=
  innerPair166Data

set_option maxRecDepth 1000000 in
private theorem leaf2901LocalValidity :
    LeafFacts leaf2901Box leaf2901Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2901Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433663488) }) = true
      norm_num [leaf2901Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2901CertificateValid :
    WideCertificateValid leaf2901Box leaf2901Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk230ValidityFacts chi184ValidityFacts
    leaf2901LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2901CoverageChecked :
    coverageCheck (innerAD leaf2901Box) leaf2901InnerLog = true := by
  rfl'

private theorem leaf2901InnerLogValid :
    leaf2901InnerLog.Valid 8 (innerAD leaf2901Box) :=
  wideLogDataValid_of_cachedCheck endpoint46PositiveFacts
    endpoint45PositiveFacts.valid leaf2901CoverageChecked

private noncomputable def leaf2901InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (363415/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf2901InputLogOnePlusV_eq :
    leaf2901InputLogOnePlusV = outerEnclosure 24
      (leaf2901Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2901RoundedFacts : LeafRoundedFacts 8
    leaf2901Certificate.logOnePlusV leaf2901InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2901InputLogOnePlusV_eq }

private noncomputable def leaf2901Inputs : Inputs :=
  inputsOfCaches globalInput sk230RoundedInputs
    chi184InputQChi innerPair166Input
    leaf2901InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2901LowerChecked :
    lowerCheck 24 leaf2901Box leaf2901Inputs = true := by
  rfl'

private theorem leaf2901CoversExact : CoversExact 8
    leaf2901Box leaf2901Certificate leaf2901InnerLog leaf2901Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk230RoundedFacts chi184RoundedFacts
    innerPair166RoundedFacts leaf2901RoundedFacts (by rfl)

private theorem leaf2901FlatSound : Sound leaf2901Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2901CertificateValid
    leaf2901InnerLogValid leaf2901CoversExact leaf2901LowerChecked

private noncomputable def leaf2902Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (247/64), chiLo := (5/32), chiHi := (41/256) }

private noncomputable def leaf2902Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742399/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433768448) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1718543363/1073741824) }, upper := { exponent := 0, mantissa := (26511/16384) } }, logOuter := sk231LogOuterCertificate, logK := sk231LogKCertificate, logChi := chi183LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870690303/274867536896) } }, logDArg := sk231LogDArgCertificate }

private noncomputable def leaf2902InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2902LocalValidity :
    LeafFacts leaf2902Box leaf2902Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2902Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433768448) }) = true
      norm_num [leaf2902Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2902CertificateValid :
    WideCertificateValid leaf2902Box leaf2902Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk231ValidityFacts chi183ValidityFacts
    leaf2902LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2902CoverageChecked :
    coverageCheck (innerAD leaf2902Box) leaf2902InnerLog = true := by
  rfl'

private theorem leaf2902InnerLogValid :
    leaf2902InnerLog.Valid 8 (innerAD leaf2902Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2902CoverageChecked

private noncomputable def leaf2902InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629273/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2902InputLogOnePlusV_eq :
    leaf2902InputLogOnePlusV = outerEnclosure 24
      (leaf2902Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2902RoundedFacts : LeafRoundedFacts 8
    leaf2902Certificate.logOnePlusV leaf2902InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2902InputLogOnePlusV_eq }

private noncomputable def leaf2902Inputs : Inputs :=
  inputsOfCaches globalInput sk231RoundedInputs
    chi183InputQChi innerPair50Input
    leaf2902InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2902LowerChecked :
    lowerCheck 24 leaf2902Box leaf2902Inputs = true := by
  rfl'

private theorem leaf2902CoversExact : CoversExact 8
    leaf2902Box leaf2902Certificate leaf2902InnerLog leaf2902Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk231RoundedFacts chi183RoundedFacts
    innerPair50RoundedFacts leaf2902RoundedFacts (by rfl)

private theorem leaf2902FlatSound : Sound leaf2902Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2902CertificateValid
    leaf2902InnerLogValid leaf2902CoversExact leaf2902LowerChecked

private noncomputable def leaf2903Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (247/64), kHi := (31/8), chiLo := (5/32), chiHi := (41/256) }

private noncomputable def leaf2903Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742401/1073741824) }, vSqrt := { lower := (8191/8192), upper := (15270769095/15270416384) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1721164641/1073741824) }, upper := { exponent := 0, mantissa := (3319/2048) } }, logOuter := sk232LogOuterCertificate, logK := sk232LogKCertificate, logChi := chi183LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (30541185479/30540832768) } }, logDArg := sk232LogDArgCertificate }

private noncomputable def leaf2903InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2903LocalValidity :
    LeafFacts leaf2903Box leaf2903Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2903Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (15270769095/15270416384) }) = true
      norm_num [leaf2903Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2903CertificateValid :
    WideCertificateValid leaf2903Box leaf2903Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk232ValidityFacts chi183ValidityFacts
    leaf2903LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2903CoverageChecked :
    coverageCheck (innerAD leaf2903Box) leaf2903InnerLog = true := by
  rfl'

private theorem leaf2903InnerLogValid :
    leaf2903InnerLog.Valid 8 (innerAD leaf2903Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2903CoverageChecked

private noncomputable def leaf2903InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814637/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2903InputLogOnePlusV_eq :
    leaf2903InputLogOnePlusV = outerEnclosure 24
      (leaf2903Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2903RoundedFacts : LeafRoundedFacts 8
    leaf2903Certificate.logOnePlusV leaf2903InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2903InputLogOnePlusV_eq }

private noncomputable def leaf2903Inputs : Inputs :=
  inputsOfCaches globalInput sk232RoundedInputs
    chi183InputQChi innerPair50Input
    leaf2903InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2903LowerChecked :
    lowerCheck 24 leaf2903Box leaf2903Inputs = true := by
  rfl'

private theorem leaf2903CoversExact : CoversExact 8
    leaf2903Box leaf2903Certificate leaf2903InnerLog leaf2903Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk232RoundedFacts chi183RoundedFacts
    innerPair50RoundedFacts leaf2903RoundedFacts (by rfl)

private theorem leaf2903FlatSound : Sound leaf2903Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2903CertificateValid
    leaf2903InnerLogValid leaf2903CoversExact leaf2903LowerChecked

private noncomputable def leaf2904Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (247/64), chiLo := (41/256), chiHi := (21/128) }

private noncomputable def leaf2904Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742401/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433641984) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1734664233/1073741824) }, upper := { exponent := 0, mantissa := (13379/8192) } }, logOuter := sk231LogOuterCertificate, logK := sk231LogKCertificate, logChi := chi184LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870563839/274867283968) } }, logDArg := sk231LogDArgCertificate }

private noncomputable def leaf2904InnerLog : WideLogData :=
  innerPair166Data

set_option maxRecDepth 1000000 in
private theorem leaf2904LocalValidity :
    LeafFacts leaf2904Box leaf2904Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2904Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433641984) }) = true
      norm_num [leaf2904Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2904CertificateValid :
    WideCertificateValid leaf2904Box leaf2904Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk231ValidityFacts chi184ValidityFacts
    leaf2904LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2904CoverageChecked :
    coverageCheck (innerAD leaf2904Box) leaf2904InnerLog = true := by
  rfl'

private theorem leaf2904InnerLogValid :
    leaf2904InnerLog.Valid 8 (innerAD leaf2904Box) :=
  wideLogDataValid_of_cachedCheck endpoint46PositiveFacts
    endpoint45PositiveFacts.valid leaf2904CoverageChecked

private noncomputable def leaf2904InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629281/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2904InputLogOnePlusV_eq :
    leaf2904InputLogOnePlusV = outerEnclosure 24
      (leaf2904Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2904RoundedFacts : LeafRoundedFacts 8
    leaf2904Certificate.logOnePlusV leaf2904InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2904InputLogOnePlusV_eq }

private noncomputable def leaf2904Inputs : Inputs :=
  inputsOfCaches globalInput sk231RoundedInputs
    chi184InputQChi innerPair166Input
    leaf2904InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2904LowerChecked :
    lowerCheck 24 leaf2904Box leaf2904Inputs = true := by
  rfl'

private theorem leaf2904CoversExact : CoversExact 8
    leaf2904Box leaf2904Certificate leaf2904InnerLog leaf2904Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk231RoundedFacts chi184RoundedFacts
    innerPair166RoundedFacts leaf2904RoundedFacts (by rfl)

private theorem leaf2904FlatSound : Sound leaf2904Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2904CertificateValid
    leaf2904InnerLogValid leaf2904CoversExact leaf2904LowerChecked

private noncomputable def leaf2905Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (247/64), kHi := (31/8), chiLo := (41/256), chiHi := (21/128) }

private noncomputable def leaf2905Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742403/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486724096) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1737351043/1073741824) }, upper := { exponent := 0, mantissa := (1675/1024) } }, logOuter := sk232LogOuterCertificate, logK := sk232LogKCertificate, logChi := chi184LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54974108467/54973448192) } }, logDArg := sk232LogDArgCertificate }

private noncomputable def leaf2905InnerLog : WideLogData :=
  innerPair166Data

set_option maxRecDepth 1000000 in
private theorem leaf2905LocalValidity :
    LeafFacts leaf2905Box leaf2905Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2905Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486724096) }) = true
      norm_num [leaf2905Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2905CertificateValid :
    WideCertificateValid leaf2905Box leaf2905Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk232ValidityFacts chi184ValidityFacts
    leaf2905LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2905CoverageChecked :
    coverageCheck (innerAD leaf2905Box) leaf2905InnerLog = true := by
  rfl'

private theorem leaf2905InnerLogValid :
    leaf2905InnerLog.Valid 8 (innerAD leaf2905Box) :=
  wideLogDataValid_of_cachedCheck endpoint46PositiveFacts
    endpoint45PositiveFacts.valid leaf2905CoverageChecked

private noncomputable def leaf2905InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814641/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2905InputLogOnePlusV_eq :
    leaf2905InputLogOnePlusV = outerEnclosure 24
      (leaf2905Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2905RoundedFacts : LeafRoundedFacts 8
    leaf2905Certificate.logOnePlusV leaf2905InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2905InputLogOnePlusV_eq }

private noncomputable def leaf2905Inputs : Inputs :=
  inputsOfCaches globalInput sk232RoundedInputs
    chi184InputQChi innerPair166Input
    leaf2905InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2905LowerChecked :
    lowerCheck 24 leaf2905Box leaf2905Inputs = true := by
  rfl'

private theorem leaf2905CoversExact : CoversExact 8
    leaf2905Box leaf2905Certificate leaf2905InnerLog leaf2905Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk232RoundedFacts chi184RoundedFacts
    innerPair166RoundedFacts leaf2905RoundedFacts (by rfl)

private theorem leaf2905FlatSound : Sound leaf2905Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2905CertificateValid
    leaf2905InnerLogValid leaf2905CoversExact leaf2905LowerChecked

private noncomputable def leaf2906Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (245/64), chiLo := (21/128), chiHi := (43/256) }

private noncomputable def leaf2906Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742399/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433559552) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1745280419/1073741824) }, upper := { exponent := 0, mantissa := (26919/16384) } }, logOuter := sk229LogOuterCertificate, logK := sk229LogKCertificate, logChi := chi185LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870481407/274867119104) } }, logDArg := sk229LogDArgCertificate }

private noncomputable def leaf2906InnerLog : WideLogData :=
  innerPair61Data

set_option maxRecDepth 1000000 in
private theorem leaf2906LocalValidity :
    LeafFacts leaf2906Box leaf2906Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2906Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433559552) }) = true
      norm_num [leaf2906Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2906CertificateValid :
    WideCertificateValid leaf2906Box leaf2906Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk229ValidityFacts chi185ValidityFacts
    leaf2906LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2906CoverageChecked :
    coverageCheck (innerAD leaf2906Box) leaf2906InnerLog = true := by
  rfl'

private theorem leaf2906InnerLogValid :
    leaf2906InnerLog.Valid 8 (innerAD leaf2906Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint48PositiveFacts.valid leaf2906CoverageChecked

private noncomputable def leaf2906InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814643/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2906InputLogOnePlusV_eq :
    leaf2906InputLogOnePlusV = outerEnclosure 24
      (leaf2906Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2906RoundedFacts : LeafRoundedFacts 8
    leaf2906Certificate.logOnePlusV leaf2906InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2906InputLogOnePlusV_eq }

private noncomputable def leaf2906Inputs : Inputs :=
  inputsOfCaches globalInput sk229RoundedInputs
    chi185InputQChi innerPair61Input
    leaf2906InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2906LowerChecked :
    lowerCheck 24 leaf2906Box leaf2906Inputs = true := by
  rfl'

private theorem leaf2906CoversExact : CoversExact 8
    leaf2906Box leaf2906Certificate leaf2906InnerLog leaf2906Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk229RoundedFacts chi185RoundedFacts
    innerPair61RoundedFacts leaf2906RoundedFacts (by rfl)

private theorem leaf2906FlatSound : Sound leaf2906Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2906CertificateValid
    leaf2906InnerLogValid leaf2906CoversExact leaf2906LowerChecked

private noncomputable def leaf2907Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (245/64), kHi := (123/32), chiLo := (21/128), chiHi := (43/256) }

private noncomputable def leaf2907Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742401/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433537536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1748032761/1073741824) }, upper := { exponent := 0, mantissa := (13481/8192) } }, logOuter := sk230LogOuterCertificate, logK := sk230LogKCertificate, logChi := chi185LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870459391/274867075072) } }, logDArg := sk230LogDArgCertificate }

private noncomputable def leaf2907InnerLog : WideLogData :=
  innerPair61Data

set_option maxRecDepth 1000000 in
private theorem leaf2907LocalValidity :
    LeafFacts leaf2907Box leaf2907Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2907Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433537536) }) = true
      norm_num [leaf2907Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2907CertificateValid :
    WideCertificateValid leaf2907Box leaf2907Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk230ValidityFacts chi185ValidityFacts
    leaf2907LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2907CoverageChecked :
    coverageCheck (innerAD leaf2907Box) leaf2907InnerLog = true := by
  rfl'

private theorem leaf2907InnerLogValid :
    leaf2907InnerLog.Valid 8 (innerAD leaf2907Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint48PositiveFacts.valid leaf2907CoverageChecked

private noncomputable def leaf2907InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629287/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2907InputLogOnePlusV_eq :
    leaf2907InputLogOnePlusV = outerEnclosure 24
      (leaf2907Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2907RoundedFacts : LeafRoundedFacts 8
    leaf2907Certificate.logOnePlusV leaf2907InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2907InputLogOnePlusV_eq }

private noncomputable def leaf2907Inputs : Inputs :=
  inputsOfCaches globalInput sk230RoundedInputs
    chi185InputQChi innerPair61Input
    leaf2907InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2907LowerChecked :
    lowerCheck 24 leaf2907Box leaf2907Inputs = true := by
  rfl'

private theorem leaf2907CoversExact : CoversExact 8
    leaf2907Box leaf2907Certificate leaf2907InnerLog leaf2907Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk230RoundedFacts chi185RoundedFacts
    innerPair61RoundedFacts leaf2907RoundedFacts (by rfl)

private theorem leaf2907FlatSound : Sound leaf2907Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2907CertificateValid
    leaf2907InnerLogValid leaf2907CoversExact leaf2907LowerChecked

private noncomputable def leaf2908Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (245/64), chiLo := (43/256), chiHi := (11/64) }

private noncomputable def leaf2908Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742401/1073741824) }, vSqrt := { lower := (8191/8192), upper := (15270769095/15270381568) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1761270225/1073741824) }, upper := { exponent := 0, mantissa := (6791/4096) } }, logOuter := sk229LogOuterCertificate, logK := sk229LogKCertificate, logChi := chi186LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (30541150663/30540763136) } }, logDArg := sk229LogDArgCertificate }

private noncomputable def leaf2908InnerLog : WideLogData :=
  innerPair62Data

set_option maxRecDepth 1000000 in
private theorem leaf2908LocalValidity :
    LeafFacts leaf2908Box leaf2908Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2908Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (15270769095/15270381568) }) = true
      norm_num [leaf2908Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2908CertificateValid :
    WideCertificateValid leaf2908Box leaf2908Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk229ValidityFacts chi186ValidityFacts
    leaf2908LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2908CoverageChecked :
    coverageCheck (innerAD leaf2908Box) leaf2908InnerLog = true := by
  rfl'

private theorem leaf2908InnerLogValid :
    leaf2908InnerLog.Valid 8 (innerAD leaf2908Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint133PositiveFacts.valid leaf2908CoverageChecked

private noncomputable def leaf2908InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814647/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2908InputLogOnePlusV_eq :
    leaf2908InputLogOnePlusV = outerEnclosure 24
      (leaf2908Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2908RoundedFacts : LeafRoundedFacts 8
    leaf2908Certificate.logOnePlusV leaf2908InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2908InputLogOnePlusV_eq }

private noncomputable def leaf2908Inputs : Inputs :=
  inputsOfCaches globalInput sk229RoundedInputs
    chi186InputQChi innerPair62Input
    leaf2908InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2908LowerChecked :
    lowerCheck 24 leaf2908Box leaf2908Inputs = true := by
  rfl'

private theorem leaf2908CoversExact : CoversExact 8
    leaf2908Box leaf2908Certificate leaf2908InnerLog leaf2908Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk229RoundedFacts chi186RoundedFacts
    innerPair62RoundedFacts leaf2908RoundedFacts (by rfl)

private theorem leaf2908FlatSound : Sound leaf2908Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2908CertificateValid
    leaf2908InnerLogValid leaf2908CoversExact leaf2908LowerChecked

private noncomputable def leaf2909Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (245/64), kHi := (123/32), chiLo := (43/256), chiHi := (11/64) }

private noncomputable def leaf2909Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742403/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433411584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1764088099/1073741824) }, upper := { exponent := 0, mantissa := (3401/2048) } }, logOuter := sk230LogOuterCertificate, logK := sk230LogKCertificate, logChi := chi186LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870333439/274866823168) } }, logDArg := sk230LogDArgCertificate }

private noncomputable def leaf2909InnerLog : WideLogData :=
  innerPair163Data

set_option maxRecDepth 1000000 in
private theorem leaf2909LocalValidity :
    LeafFacts leaf2909Box leaf2909Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2909Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433411584) }) = true
      norm_num [leaf2909Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2909CertificateValid :
    WideCertificateValid leaf2909Box leaf2909Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk230ValidityFacts chi186ValidityFacts
    leaf2909LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2909CoverageChecked :
    coverageCheck (innerAD leaf2909Box) leaf2909InnerLog = true := by
  rfl'

private theorem leaf2909InnerLogValid :
    leaf2909InnerLog.Valid 8 (innerAD leaf2909Box) :=
  wideLogDataValid_of_cachedCheck endpoint45PositiveFacts
    endpoint133PositiveFacts.valid leaf2909CoverageChecked

private noncomputable def leaf2909InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629295/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2909InputLogOnePlusV_eq :
    leaf2909InputLogOnePlusV = outerEnclosure 24
      (leaf2909Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2909RoundedFacts : LeafRoundedFacts 8
    leaf2909Certificate.logOnePlusV leaf2909InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2909InputLogOnePlusV_eq }

private noncomputable def leaf2909Inputs : Inputs :=
  inputsOfCaches globalInput sk230RoundedInputs
    chi186InputQChi innerPair163Input
    leaf2909InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2909LowerChecked :
    lowerCheck 24 leaf2909Box leaf2909Inputs = true := by
  rfl'

private theorem leaf2909CoversExact : CoversExact 8
    leaf2909Box leaf2909Certificate leaf2909InnerLog leaf2909Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk230RoundedFacts chi186RoundedFacts
    innerPair163RoundedFacts leaf2909RoundedFacts (by rfl)

private theorem leaf2909FlatSound : Sound leaf2909Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2909CertificateValid
    leaf2909InnerLogValid leaf2909CoversExact leaf2909LowerChecked

private noncomputable def leaf2910Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (247/64), chiLo := (21/128), chiHi := (43/256) }

private noncomputable def leaf2910Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742403/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9162461457/9162234368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1750785103/1073741824) }, upper := { exponent := 0, mantissa := (27005/16384) } }, logOuter := sk231LogOuterCertificate, logK := sk231LogKCertificate, logChi := chi185LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (18324695825/18324468736) } }, logDArg := sk231LogDArgCertificate }

private noncomputable def leaf2910InnerLog : WideLogData :=
  innerPair61Data

set_option maxRecDepth 1000000 in
private theorem leaf2910LocalValidity :
    LeafFacts leaf2910Box leaf2910Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2910Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9162461457/9162234368) }) = true
      norm_num [leaf2910Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2910CertificateValid :
    WideCertificateValid leaf2910Box leaf2910Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk231ValidityFacts chi185ValidityFacts
    leaf2910LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2910CoverageChecked :
    coverageCheck (innerAD leaf2910Box) leaf2910InnerLog = true := by
  rfl'

private theorem leaf2910InnerLogValid :
    leaf2910InnerLog.Valid 8 (innerAD leaf2910Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint48PositiveFacts.valid leaf2910CoverageChecked

private noncomputable def leaf2910InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629289/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2910InputLogOnePlusV_eq :
    leaf2910InputLogOnePlusV = outerEnclosure 24
      (leaf2910Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2910RoundedFacts : LeafRoundedFacts 8
    leaf2910Certificate.logOnePlusV leaf2910InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2910InputLogOnePlusV_eq }

private noncomputable def leaf2910Inputs : Inputs :=
  inputsOfCaches globalInput sk231RoundedInputs
    chi185InputQChi innerPair61Input
    leaf2910InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2910LowerChecked :
    lowerCheck 24 leaf2910Box leaf2910Inputs = true := by
  rfl'

private theorem leaf2910CoversExact : CoversExact 8
    leaf2910Box leaf2910Certificate leaf2910InnerLog leaf2910Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk231RoundedFacts chi185RoundedFacts
    innerPair61RoundedFacts leaf2910RoundedFacts (by rfl)

private theorem leaf2910FlatSound : Sound leaf2910Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2910CertificateValid
    leaf2910InnerLogValid leaf2910CoversExact leaf2910LowerChecked

private noncomputable def leaf2911Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (247/64), kHi := (31/8), chiLo := (21/128), chiHi := (43/256) }

private noncomputable def leaf2911Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742405/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433493504) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1753537445/1073741824) }, upper := { exponent := 0, mantissa := (3381/2048) } }, logOuter := sk232LogOuterCertificate, logK := sk232LogKCertificate, logChi := chi185LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870415359/274866987008) } }, logDArg := sk232LogDArgCertificate }

private noncomputable def leaf2911InnerLog : WideLogData :=
  innerPair61Data

set_option maxRecDepth 1000000 in
private theorem leaf2911LocalValidity :
    LeafFacts leaf2911Box leaf2911Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2911Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433493504) }) = true
      norm_num [leaf2911Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2911CertificateValid :
    WideCertificateValid leaf2911Box leaf2911Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk232ValidityFacts chi185ValidityFacts
    leaf2911LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2911CoverageChecked :
    coverageCheck (innerAD leaf2911Box) leaf2911InnerLog = true := by
  rfl'

private theorem leaf2911InnerLogValid :
    leaf2911InnerLog.Valid 8 (innerAD leaf2911Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint48PositiveFacts.valid leaf2911CoverageChecked

private noncomputable def leaf2911InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814645/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2911InputLogOnePlusV_eq :
    leaf2911InputLogOnePlusV = outerEnclosure 24
      (leaf2911Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2911RoundedFacts : LeafRoundedFacts 8
    leaf2911Certificate.logOnePlusV leaf2911InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2911InputLogOnePlusV_eq }

private noncomputable def leaf2911Inputs : Inputs :=
  inputsOfCaches globalInput sk232RoundedInputs
    chi185InputQChi innerPair61Input
    leaf2911InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2911LowerChecked :
    lowerCheck 24 leaf2911Box leaf2911Inputs = true := by
  rfl'

private theorem leaf2911CoversExact : CoversExact 8
    leaf2911Box leaf2911Certificate leaf2911InnerLog leaf2911Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk232RoundedFacts chi185RoundedFacts
    innerPair61RoundedFacts leaf2911RoundedFacts (by rfl)

private theorem leaf2911FlatSound : Sound leaf2911Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2911CertificateValid
    leaf2911InnerLogValid leaf2911CoversExact leaf2911LowerChecked

private noncomputable def leaf2912Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (247/64), chiLo := (43/256), chiHi := (11/64) }

private noncomputable def leaf2912Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742405/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433389056) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1766905973/1073741824) }, upper := { exponent := 0, mantissa := (6813/4096) } }, logOuter := sk231LogOuterCertificate, logK := sk231LogKCertificate, logChi := chi186LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870310911/274866778112) } }, logDArg := sk231LogDArgCertificate }

private noncomputable def leaf2912InnerLog : WideLogData :=
  innerPair163Data

set_option maxRecDepth 1000000 in
private theorem leaf2912LocalValidity :
    LeafFacts leaf2912Box leaf2912Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2912Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433389056) }) = true
      norm_num [leaf2912Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2912CertificateValid :
    WideCertificateValid leaf2912Box leaf2912Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk231ValidityFacts chi186ValidityFacts
    leaf2912LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2912CoverageChecked :
    coverageCheck (innerAD leaf2912Box) leaf2912InnerLog = true := by
  rfl'

private theorem leaf2912InnerLogValid :
    leaf2912InnerLog.Valid 8 (innerAD leaf2912Box) :=
  wideLogDataValid_of_cachedCheck endpoint45PositiveFacts
    endpoint133PositiveFacts.valid leaf2912CoverageChecked

private noncomputable def leaf2912InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726831/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf2912InputLogOnePlusV_eq :
    leaf2912InputLogOnePlusV = outerEnclosure 24
      (leaf2912Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2912RoundedFacts : LeafRoundedFacts 8
    leaf2912Certificate.logOnePlusV leaf2912InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2912InputLogOnePlusV_eq }

private noncomputable def leaf2912Inputs : Inputs :=
  inputsOfCaches globalInput sk231RoundedInputs
    chi186InputQChi innerPair163Input
    leaf2912InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2912LowerChecked :
    lowerCheck 24 leaf2912Box leaf2912Inputs = true := by
  rfl'

private theorem leaf2912CoversExact : CoversExact 8
    leaf2912Box leaf2912Certificate leaf2912InnerLog leaf2912Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk231RoundedFacts chi186RoundedFacts
    innerPair163RoundedFacts leaf2912RoundedFacts (by rfl)

private theorem leaf2912FlatSound : Sound leaf2912Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2912CertificateValid
    leaf2912InnerLogValid leaf2912CoversExact leaf2912LowerChecked

private noncomputable def leaf2913Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (247/64), kHi := (31/8), chiLo := (43/256), chiHi := (11/64) }

private noncomputable def leaf2913Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742407/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45811122176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1769723847/1073741824) }, upper := { exponent := 0, mantissa := (853/512) } }, logOuter := sk232LogOuterCertificate, logK := sk232LogKCertificate, logChi := chi186LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623429461/91622244352) } }, logDArg := sk232LogDArgCertificate }

private noncomputable def leaf2913InnerLog : WideLogData :=
  innerPair163Data

set_option maxRecDepth 1000000 in
private theorem leaf2913LocalValidity :
    LeafFacts leaf2913Box leaf2913Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2913Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45811122176) }) = true
      norm_num [leaf2913Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2913CertificateValid :
    WideCertificateValid leaf2913Box leaf2913Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk232ValidityFacts chi186ValidityFacts
    leaf2913LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2913CoverageChecked :
    coverageCheck (innerAD leaf2913Box) leaf2913InnerLog = true := by
  rfl'

private theorem leaf2913InnerLogValid :
    leaf2913InnerLog.Valid 8 (innerAD leaf2913Box) :=
  wideLogDataValid_of_cachedCheck endpoint45PositiveFacts
    endpoint133PositiveFacts.valid leaf2913CoverageChecked

private noncomputable def leaf2913InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814649/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2913InputLogOnePlusV_eq :
    leaf2913InputLogOnePlusV = outerEnclosure 24
      (leaf2913Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2913RoundedFacts : LeafRoundedFacts 8
    leaf2913Certificate.logOnePlusV leaf2913InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2913InputLogOnePlusV_eq }

private noncomputable def leaf2913Inputs : Inputs :=
  inputsOfCaches globalInput sk232RoundedInputs
    chi186InputQChi innerPair163Input
    leaf2913InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2913LowerChecked :
    lowerCheck 24 leaf2913Box leaf2913Inputs = true := by
  rfl'

private theorem leaf2913CoversExact : CoversExact 8
    leaf2913Box leaf2913Certificate leaf2913InnerLog leaf2913Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk232RoundedFacts chi186RoundedFacts
    innerPair163RoundedFacts leaf2913RoundedFacts (by rfl)

private theorem leaf2913FlatSound : Sound leaf2913Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2913CertificateValid
    leaf2913InnerLogValid leaf2913CoversExact leaf2913LowerChecked

private noncomputable def leaf2914Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (241/64), chiLo := (11/64), chiHi := (45/256) }

private noncomputable def leaf2914Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742395/1073741824) }, vSqrt := { lower := (8191/8192), upper := (8084524815/8084317696) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1765726407/1073741824) }, upper := { exponent := 0, mantissa := (27229/16384) } }, logOuter := sk225LogOuterCertificate, logK := sk225LogKCertificate, logChi := chi133LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16168842511/16168635392) } }, logDArg := sk225LogDArgCertificate }

private noncomputable def leaf2914InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2914LocalValidity :
    LeafFacts leaf2914Box leaf2914Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2914Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8084524815/8084317696) }) = true
      norm_num [leaf2914Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2914CertificateValid :
    WideCertificateValid leaf2914Box leaf2914Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk225ValidityFacts chi133ValidityFacts
    leaf2914LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2914CoverageChecked :
    coverageCheck (innerAD leaf2914Box) leaf2914InnerLog = true := by
  rfl'

private theorem leaf2914InnerLogValid :
    leaf2914InnerLog.Valid 8 (innerAD leaf2914Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2914CoverageChecked

private noncomputable def leaf2914InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726831/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf2914InputLogOnePlusV_eq :
    leaf2914InputLogOnePlusV = outerEnclosure 24
      (leaf2914Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2914RoundedFacts : LeafRoundedFacts 8
    leaf2914Certificate.logOnePlusV leaf2914InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2914InputLogOnePlusV_eq }

private noncomputable def leaf2914Inputs : Inputs :=
  inputsOfCaches globalInput sk225RoundedInputs
    chi133InputQChi innerPair56Input
    leaf2914InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2914LowerChecked :
    lowerCheck 24 leaf2914Box leaf2914Inputs = true := by
  rfl'

private theorem leaf2914CoversExact : CoversExact 8
    leaf2914Box leaf2914Certificate leaf2914InnerLog leaf2914Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk225RoundedFacts chi133RoundedFacts
    innerPair56RoundedFacts leaf2914RoundedFacts (by rfl)

private theorem leaf2914FlatSound : Sound leaf2914Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2914CertificateValid
    leaf2914InnerLogValid leaf2914CoversExact leaf2914LowerChecked

private noncomputable def leaf2915Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (241/64), kHi := (121/32), chiLo := (11/64), chiHi := (45/256) }

private noncomputable def leaf2915Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742397/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433377792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1768609813/1073741824) }, upper := { exponent := 0, mantissa := (13637/8192) } }, logOuter := sk226LogOuterCertificate, logK := sk226LogKCertificate, logChi := chi133LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870299647/274866755584) } }, logDArg := sk226LogDArgCertificate }

private noncomputable def leaf2915InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2915LocalValidity :
    LeafFacts leaf2915Box leaf2915Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2915Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433377792) }) = true
      norm_num [leaf2915Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2915CertificateValid :
    WideCertificateValid leaf2915Box leaf2915Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk226ValidityFacts chi133ValidityFacts
    leaf2915LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2915CoverageChecked :
    coverageCheck (innerAD leaf2915Box) leaf2915InnerLog = true := by
  rfl'

private theorem leaf2915InnerLogValid :
    leaf2915InnerLog.Valid 8 (innerAD leaf2915Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2915CoverageChecked

private noncomputable def leaf2915InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629297/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2915InputLogOnePlusV_eq :
    leaf2915InputLogOnePlusV = outerEnclosure 24
      (leaf2915Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2915RoundedFacts : LeafRoundedFacts 8
    leaf2915Certificate.logOnePlusV leaf2915InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2915InputLogOnePlusV_eq }

private noncomputable def leaf2915Inputs : Inputs :=
  inputsOfCaches globalInput sk226RoundedInputs
    chi133InputQChi innerPair56Input
    leaf2915InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2915LowerChecked :
    lowerCheck 24 leaf2915Box leaf2915Inputs = true := by
  rfl'

private theorem leaf2915CoversExact : CoversExact 8
    leaf2915Box leaf2915Certificate leaf2915InnerLog leaf2915Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk226RoundedFacts chi133RoundedFacts
    innerPair56RoundedFacts leaf2915RoundedFacts (by rfl)

private theorem leaf2915FlatSound : Sound leaf2915Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2915CertificateValid
    leaf2915InnerLogValid leaf2915CoversExact leaf2915LowerChecked

private noncomputable def leaf2916Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (241/64), chiLo := (45/256), chiHi := (23/128) }

private noncomputable def leaf2916Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742397/1073741824) }, vSqrt := { lower := (8191/8192), upper := (3054153819/3054072832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1781454085/1073741824) }, upper := { exponent := 0, mantissa := (13735/8192) } }, logOuter := sk225LogOuterCertificate, logK := sk225LogKCertificate, logChi := chi134LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (6108226651/6108145664) } }, logDArg := sk225LogDArgCertificate }

private noncomputable def leaf2916InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2916LocalValidity :
    LeafFacts leaf2916Box leaf2916Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2916Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (3054153819/3054072832) }) = true
      norm_num [leaf2916Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2916CertificateValid :
    WideCertificateValid leaf2916Box leaf2916Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk225ValidityFacts chi134ValidityFacts
    leaf2916LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2916CoverageChecked :
    coverageCheck (innerAD leaf2916Box) leaf2916InnerLog = true := by
  rfl'

private theorem leaf2916InnerLogValid :
    leaf2916InnerLog.Valid 8 (innerAD leaf2916Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2916CoverageChecked

private noncomputable def leaf2916InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629303/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2916InputLogOnePlusV_eq :
    leaf2916InputLogOnePlusV = outerEnclosure 24
      (leaf2916Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2916RoundedFacts : LeafRoundedFacts 8
    leaf2916Certificate.logOnePlusV leaf2916InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2916InputLogOnePlusV_eq }

private noncomputable def leaf2916Inputs : Inputs :=
  inputsOfCaches globalInput sk225RoundedInputs
    chi134InputQChi innerPair56Input
    leaf2916InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2916LowerChecked :
    lowerCheck 24 leaf2916Box leaf2916Inputs = true := by
  rfl'

private theorem leaf2916CoversExact : CoversExact 8
    leaf2916Box leaf2916Certificate leaf2916InnerLog leaf2916Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk225RoundedFacts chi134RoundedFacts
    innerPair56RoundedFacts leaf2916RoundedFacts (by rfl)

private theorem leaf2916FlatSound : Sound leaf2916Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2916CertificateValid
    leaf2916InnerLogValid leaf2916CoversExact leaf2916LowerChecked

private noncomputable def leaf2917Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (241/64), kHi := (121/32), chiLo := (45/256), chiHi := (23/128) }

private noncomputable def leaf2917Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742399/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433253888) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1784403023/1073741824) }, upper := { exponent := 0, mantissa := (6879/4096) } }, logOuter := sk226LogOuterCertificate, logK := sk226LogKCertificate, logChi := chi134LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870175743/274866507776) } }, logDArg := sk226LogDArgCertificate }

private noncomputable def leaf2917InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2917LocalValidity :
    LeafFacts leaf2917Box leaf2917Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2917Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433253888) }) = true
      norm_num [leaf2917Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2917CertificateValid :
    WideCertificateValid leaf2917Box leaf2917Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk226ValidityFacts chi134ValidityFacts
    leaf2917LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2917CoverageChecked :
    coverageCheck (innerAD leaf2917Box) leaf2917InnerLog = true := by
  rfl'

private theorem leaf2917InnerLogValid :
    leaf2917InnerLog.Valid 8 (innerAD leaf2917Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2917CoverageChecked

private noncomputable def leaf2917InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629305/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2917InputLogOnePlusV_eq :
    leaf2917InputLogOnePlusV = outerEnclosure 24
      (leaf2917Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2917RoundedFacts : LeafRoundedFacts 8
    leaf2917Certificate.logOnePlusV leaf2917InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2917InputLogOnePlusV_eq }

private noncomputable def leaf2917Inputs : Inputs :=
  inputsOfCaches globalInput sk226RoundedInputs
    chi134InputQChi innerPair56Input
    leaf2917InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2917LowerChecked :
    lowerCheck 24 leaf2917Box leaf2917Inputs = true := by
  rfl'

private theorem leaf2917CoversExact : CoversExact 8
    leaf2917Box leaf2917Certificate leaf2917InnerLog leaf2917Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk226RoundedFacts chi134RoundedFacts
    innerPair56RoundedFacts leaf2917RoundedFacts (by rfl)

private theorem leaf2917FlatSound : Sound leaf2917Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2917CertificateValid
    leaf2917InnerLogValid leaf2917CoversExact leaf2917LowerChecked

private noncomputable def leaf2918Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (243/64), chiLo := (11/64), chiHi := (45/256) }

private noncomputable def leaf2918Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742399/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433354752) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1771493219/1073741824) }, upper := { exponent := 0, mantissa := (27319/16384) } }, logOuter := sk227LogOuterCertificate, logK := sk227LogKCertificate, logChi := chi133LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870276607/274866709504) } }, logDArg := sk227LogDArgCertificate }

private noncomputable def leaf2918InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2918LocalValidity :
    LeafFacts leaf2918Box leaf2918Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2918Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433354752) }) = true
      norm_num [leaf2918Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2918CertificateValid :
    WideCertificateValid leaf2918Box leaf2918Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk227ValidityFacts chi133ValidityFacts
    leaf2918LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2918CoverageChecked :
    coverageCheck (innerAD leaf2918Box) leaf2918InnerLog = true := by
  rfl'

private theorem leaf2918InnerLogValid :
    leaf2918InnerLog.Valid 8 (innerAD leaf2918Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2918CoverageChecked

private noncomputable def leaf2918InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814649/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2918InputLogOnePlusV_eq :
    leaf2918InputLogOnePlusV = outerEnclosure 24
      (leaf2918Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2918RoundedFacts : LeafRoundedFacts 8
    leaf2918Certificate.logOnePlusV leaf2918InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2918InputLogOnePlusV_eq }

private noncomputable def leaf2918Inputs : Inputs :=
  inputsOfCaches globalInput sk227RoundedInputs
    chi133InputQChi innerPair56Input
    leaf2918InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2918LowerChecked :
    lowerCheck 24 leaf2918Box leaf2918Inputs = true := by
  rfl'

private theorem leaf2918CoversExact : CoversExact 8
    leaf2918Box leaf2918Certificate leaf2918InnerLog leaf2918Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk227RoundedFacts chi133RoundedFacts
    innerPair56RoundedFacts leaf2918RoundedFacts (by rfl)

private theorem leaf2918FlatSound : Sound leaf2918Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2918CertificateValid
    leaf2918InnerLogValid leaf2918CoversExact leaf2918LowerChecked

private noncomputable def leaf2919Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (243/64), kHi := (61/16), chiLo := (11/64), chiHi := (45/256) }

private noncomputable def leaf2919Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742401/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433331712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1774376625/1073741824) }, upper := { exponent := 0, mantissa := (6841/4096) } }, logOuter := sk228LogOuterCertificate, logK := sk228LogKCertificate, logChi := chi133LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870253567/274866663424) } }, logDArg := sk228LogDArgCertificate }

private noncomputable def leaf2919InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2919LocalValidity :
    LeafFacts leaf2919Box leaf2919Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2919Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433331712) }) = true
      norm_num [leaf2919Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2919CertificateValid :
    WideCertificateValid leaf2919Box leaf2919Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk228ValidityFacts chi133ValidityFacts
    leaf2919LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2919CoverageChecked :
    coverageCheck (innerAD leaf2919Box) leaf2919InnerLog = true := by
  rfl'

private theorem leaf2919InnerLogValid :
    leaf2919InnerLog.Valid 8 (innerAD leaf2919Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2919CoverageChecked

private noncomputable def leaf2919InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907325/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2919InputLogOnePlusV_eq :
    leaf2919InputLogOnePlusV = outerEnclosure 24
      (leaf2919Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2919RoundedFacts : LeafRoundedFacts 8
    leaf2919Certificate.logOnePlusV leaf2919InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2919InputLogOnePlusV_eq }

private noncomputable def leaf2919Inputs : Inputs :=
  inputsOfCaches globalInput sk228RoundedInputs
    chi133InputQChi innerPair56Input
    leaf2919InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2919LowerChecked :
    lowerCheck 24 leaf2919Box leaf2919Inputs = true := by
  rfl'

private theorem leaf2919CoversExact : CoversExact 8
    leaf2919Box leaf2919Certificate leaf2919InnerLog leaf2919Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk228RoundedFacts chi133RoundedFacts
    innerPair56RoundedFacts leaf2919RoundedFacts (by rfl)

private theorem leaf2919FlatSound : Sound leaf2919Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2919CertificateValid
    leaf2919InnerLogValid leaf2919CoversExact leaf2919LowerChecked

private noncomputable def leaf2920Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (243/64), chiLo := (45/256), chiHi := (23/128) }

private noncomputable def leaf2920Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742401/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433230336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1787351961/1073741824) }, upper := { exponent := 0, mantissa := (13781/8192) } }, logOuter := sk227LogOuterCertificate, logK := sk227LogKCertificate, logChi := chi134LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870152191/274866460672) } }, logDArg := sk227LogDArgCertificate }

private noncomputable def leaf2920InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2920LocalValidity :
    LeafFacts leaf2920Box leaf2920Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2920Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433230336) }) = true
      norm_num [leaf2920Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2920CertificateValid :
    WideCertificateValid leaf2920Box leaf2920Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk227ValidityFacts chi134ValidityFacts
    leaf2920LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2920CoverageChecked :
    coverageCheck (innerAD leaf2920Box) leaf2920InnerLog = true := by
  rfl'

private theorem leaf2920InnerLogValid :
    leaf2920InnerLog.Valid 8 (innerAD leaf2920Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2920CoverageChecked

private noncomputable def leaf2920InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814653/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2920InputLogOnePlusV_eq :
    leaf2920InputLogOnePlusV = outerEnclosure 24
      (leaf2920Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2920RoundedFacts : LeafRoundedFacts 8
    leaf2920Certificate.logOnePlusV leaf2920InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2920InputLogOnePlusV_eq }

private noncomputable def leaf2920Inputs : Inputs :=
  inputsOfCaches globalInput sk227RoundedInputs
    chi134InputQChi innerPair56Input
    leaf2920InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2920LowerChecked :
    lowerCheck 24 leaf2920Box leaf2920Inputs = true := by
  rfl'

private theorem leaf2920CoversExact : CoversExact 8
    leaf2920Box leaf2920Certificate leaf2920InnerLog leaf2920Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk227RoundedFacts chi134RoundedFacts
    innerPair56RoundedFacts leaf2920RoundedFacts (by rfl)

private theorem leaf2920FlatSound : Sound leaf2920Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2920CertificateValid
    leaf2920InnerLogValid leaf2920CoversExact leaf2920LowerChecked

private noncomputable def leaf2921Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (243/64), kHi := (61/16), chiLo := (45/256), chiHi := (23/128) }

private noncomputable def leaf2921Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742403/1073741824) }, vSqrt := { lower := (8191/8192), upper := (1065402495/1065373696) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1790300899/1073741824) }, upper := { exponent := 0, mantissa := (3451/2048) } }, logOuter := sk228LogOuterCertificate, logK := sk228LogKCertificate, logChi := chi134LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (2130776191/2130747392) } }, logDArg := sk228LogDArgCertificate }

private noncomputable def leaf2921InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2921LocalValidity :
    LeafFacts leaf2921Box leaf2921Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2921Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (1065402495/1065373696) }) = true
      norm_num [leaf2921Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2921CertificateValid :
    WideCertificateValid leaf2921Box leaf2921Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk228ValidityFacts chi134ValidityFacts
    leaf2921LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2921CoverageChecked :
    coverageCheck (innerAD leaf2921Box) leaf2921InnerLog = true := by
  rfl'

private theorem leaf2921InnerLogValid :
    leaf2921InnerLog.Valid 8 (innerAD leaf2921Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2921CoverageChecked

private noncomputable def leaf2921InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907327/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2921InputLogOnePlusV_eq :
    leaf2921InputLogOnePlusV = outerEnclosure 24
      (leaf2921Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2921RoundedFacts : LeafRoundedFacts 8
    leaf2921Certificate.logOnePlusV leaf2921InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2921InputLogOnePlusV_eq }

private noncomputable def leaf2921Inputs : Inputs :=
  inputsOfCaches globalInput sk228RoundedInputs
    chi134InputQChi innerPair56Input
    leaf2921InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2921LowerChecked :
    lowerCheck 24 leaf2921Box leaf2921Inputs = true := by
  rfl'

private theorem leaf2921CoversExact : CoversExact 8
    leaf2921Box leaf2921Certificate leaf2921InnerLog leaf2921Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk228RoundedFacts chi134RoundedFacts
    innerPair56RoundedFacts leaf2921RoundedFacts (by rfl)

private theorem leaf2921FlatSound : Sound leaf2921Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2921CertificateValid
    leaf2921InnerLogValid leaf2921CoversExact leaf2921LowerChecked

private noncomputable def leaf2922Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (241/64), chiLo := (23/128), chiHi := (47/256) }

private noncomputable def leaf2922Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742399/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433154048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1797181763/1073741824) }, upper := { exponent := 0, mantissa := (27711/16384) } }, logOuter := sk225LogOuterCertificate, logK := sk225LogKCertificate, logChi := chi135LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870075903/274866308096) } }, logDArg := sk225LogDArgCertificate }

private noncomputable def leaf2922InnerLog : WideLogData :=
  innerPair420Data

set_option maxRecDepth 1000000 in
private theorem leaf2922LocalValidity :
    LeafFacts leaf2922Box leaf2922Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2922Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433154048) }) = true
      norm_num [leaf2922Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2922CertificateValid :
    WideCertificateValid leaf2922Box leaf2922Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk225ValidityFacts chi135ValidityFacts
    leaf2922LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2922CoverageChecked :
    coverageCheck (innerAD leaf2922Box) leaf2922InnerLog = true := by
  rfl'

private theorem leaf2922InnerLogValid :
    leaf2922InnerLog.Valid 8 (innerAD leaf2922Box) :=
  wideLogDataValid_of_cachedCheck endpoint133PositiveFacts
    endpoint20PositiveFacts.valid leaf2922CoverageChecked

private noncomputable def leaf2922InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629311/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2922InputLogOnePlusV_eq :
    leaf2922InputLogOnePlusV = outerEnclosure 24
      (leaf2922Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2922RoundedFacts : LeafRoundedFacts 8
    leaf2922Certificate.logOnePlusV leaf2922InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2922InputLogOnePlusV_eq }

private noncomputable def leaf2922Inputs : Inputs :=
  inputsOfCaches globalInput sk225RoundedInputs
    chi135InputQChi innerPair420Input
    leaf2922InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2922LowerChecked :
    lowerCheck 24 leaf2922Box leaf2922Inputs = true := by
  rfl'

private theorem leaf2922CoversExact : CoversExact 8
    leaf2922Box leaf2922Certificate leaf2922InnerLog leaf2922Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk225RoundedFacts chi135RoundedFacts
    innerPair420RoundedFacts leaf2922RoundedFacts (by rfl)

private theorem leaf2922FlatSound : Sound leaf2922Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2922CertificateValid
    leaf2922InnerLogValid leaf2922CoversExact leaf2922LowerChecked

private noncomputable def leaf2923Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (241/64), kHi := (121/32), chiLo := (23/128), chiHi := (47/256) }

private noncomputable def leaf2923Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742401/1073741824) }, vSqrt := { lower := (8191/8192), upper := (15270769095/15270347776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1800196233/1073741824) }, upper := { exponent := 0, mantissa := (13879/8192) } }, logOuter := sk226LogOuterCertificate, logK := sk226LogKCertificate, logChi := chi135LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (30541116871/30540695552) } }, logDArg := sk226LogDArgCertificate }

private noncomputable def leaf2923InnerLog : WideLogData :=
  innerPair420Data

set_option maxRecDepth 1000000 in
private theorem leaf2923LocalValidity :
    LeafFacts leaf2923Box leaf2923Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2923Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (15270769095/15270347776) }) = true
      norm_num [leaf2923Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2923CertificateValid :
    WideCertificateValid leaf2923Box leaf2923Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk226ValidityFacts chi135ValidityFacts
    leaf2923LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2923CoverageChecked :
    coverageCheck (innerAD leaf2923Box) leaf2923InnerLog = true := by
  rfl'

private theorem leaf2923InnerLogValid :
    leaf2923InnerLog.Valid 8 (innerAD leaf2923Box) :=
  wideLogDataValid_of_cachedCheck endpoint133PositiveFacts
    endpoint20PositiveFacts.valid leaf2923CoverageChecked

private noncomputable def leaf2923InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (45427/65536) }

set_option maxRecDepth 1000000 in
private theorem leaf2923InputLogOnePlusV_eq :
    leaf2923InputLogOnePlusV = outerEnclosure 24
      (leaf2923Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2923RoundedFacts : LeafRoundedFacts 8
    leaf2923Certificate.logOnePlusV leaf2923InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2923InputLogOnePlusV_eq }

private noncomputable def leaf2923Inputs : Inputs :=
  inputsOfCaches globalInput sk226RoundedInputs
    chi135InputQChi innerPair420Input
    leaf2923InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2923LowerChecked :
    lowerCheck 24 leaf2923Box leaf2923Inputs = true := by
  rfl'

private theorem leaf2923CoversExact : CoversExact 8
    leaf2923Box leaf2923Certificate leaf2923InnerLog leaf2923Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk226RoundedFacts chi135RoundedFacts
    innerPair420RoundedFacts leaf2923RoundedFacts (by rfl)

private theorem leaf2923FlatSound : Sound leaf2923Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2923CertificateValid
    leaf2923InnerLogValid leaf2923CoversExact leaf2923LowerChecked

private noncomputable def leaf2924Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (241/64), chiLo := (47/256), chiHi := (3/16) }

private noncomputable def leaf2924Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742401/1073741824) }, vSqrt := { lower := (8191/8192), upper := (3196207485/3196116992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1812909441/1073741824) }, upper := { exponent := 0, mantissa := (1747/1024) } }, logOuter := sk225LogOuterCertificate, logK := sk225LogKCertificate, logChi := chi136LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (6392324477/6392233984) } }, logDArg := sk225LogDArgCertificate }

private noncomputable def leaf2924InnerLog : WideLogData :=
  innerPair68Data

set_option maxRecDepth 1000000 in
private theorem leaf2924LocalValidity :
    LeafFacts leaf2924Box leaf2924Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2924Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (3196207485/3196116992) }) = true
      norm_num [leaf2924Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2924CertificateValid :
    WideCertificateValid leaf2924Box leaf2924Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk225ValidityFacts chi136ValidityFacts
    leaf2924LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2924CoverageChecked :
    coverageCheck (innerAD leaf2924Box) leaf2924InnerLog = true := by
  rfl'

private theorem leaf2924InnerLogValid :
    leaf2924InnerLog.Valid 8 (innerAD leaf2924Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint62PositiveFacts.valid leaf2924CoverageChecked

private noncomputable def leaf2924InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814659/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2924InputLogOnePlusV_eq :
    leaf2924InputLogOnePlusV = outerEnclosure 24
      (leaf2924Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2924RoundedFacts : LeafRoundedFacts 8
    leaf2924Certificate.logOnePlusV leaf2924InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2924InputLogOnePlusV_eq }

private noncomputable def leaf2924Inputs : Inputs :=
  inputsOfCaches globalInput sk225RoundedInputs
    chi136InputQChi innerPair68Input
    leaf2924InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2924LowerChecked :
    lowerCheck 24 leaf2924Box leaf2924Inputs = true := by
  rfl'

private theorem leaf2924CoversExact : CoversExact 8
    leaf2924Box leaf2924Certificate leaf2924InnerLog leaf2924Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk225RoundedFacts chi136RoundedFacts
    innerPair68RoundedFacts leaf2924RoundedFacts (by rfl)

private theorem leaf2924FlatSound : Sound leaf2924Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2924CertificateValid
    leaf2924InnerLogValid leaf2924CoversExact leaf2924LowerChecked

private noncomputable def leaf2925Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (241/64), kHi := (121/32), chiLo := (47/256), chiHi := (3/16) }

private noncomputable def leaf2925Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742403/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486601216) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1815989443/1073741824) }, upper := { exponent := 0, mantissa := (875/512) } }, logOuter := sk226LogOuterCertificate, logK := sk226LogKCertificate, logChi := chi136LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973985587/54973202432) } }, logDArg := sk226LogDArgCertificate }

private noncomputable def leaf2925InnerLog : WideLogData :=
  innerPair68Data

set_option maxRecDepth 1000000 in
private theorem leaf2925LocalValidity :
    LeafFacts leaf2925Box leaf2925Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2925Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486601216) }) = true
      norm_num [leaf2925Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2925CertificateValid :
    WideCertificateValid leaf2925Box leaf2925Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk226ValidityFacts chi136ValidityFacts
    leaf2925LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2925CoverageChecked :
    coverageCheck (innerAD leaf2925Box) leaf2925InnerLog = true := by
  rfl'

private theorem leaf2925InnerLogValid :
    leaf2925InnerLog.Valid 8 (innerAD leaf2925Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint62PositiveFacts.valid leaf2925CoverageChecked

private noncomputable def leaf2925InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453665/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf2925InputLogOnePlusV_eq :
    leaf2925InputLogOnePlusV = outerEnclosure 24
      (leaf2925Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2925RoundedFacts : LeafRoundedFacts 8
    leaf2925Certificate.logOnePlusV leaf2925InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2925InputLogOnePlusV_eq }

private noncomputable def leaf2925Inputs : Inputs :=
  inputsOfCaches globalInput sk226RoundedInputs
    chi136InputQChi innerPair68Input
    leaf2925InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2925LowerChecked :
    lowerCheck 24 leaf2925Box leaf2925Inputs = true := by
  rfl'

private theorem leaf2925CoversExact : CoversExact 8
    leaf2925Box leaf2925Certificate leaf2925InnerLog leaf2925Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk226RoundedFacts chi136RoundedFacts
    innerPair68RoundedFacts leaf2925RoundedFacts (by rfl)

private theorem leaf2925FlatSound : Sound leaf2925Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2925CertificateValid
    leaf2925InnerLogValid leaf2925CoversExact leaf2925LowerChecked

private noncomputable def leaf2926Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (243/64), chiLo := (23/128), chiHi := (47/256) }

private noncomputable def leaf2926Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742403/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486621184) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1803210703/1073741824) }, upper := { exponent := 0, mantissa := (27805/16384) } }, logOuter := sk227LogOuterCertificate, logK := sk227LogKCertificate, logChi := chi135LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54974005555/54973242368) } }, logDArg := sk227LogDArgCertificate }

private noncomputable def leaf2926InnerLog : WideLogData :=
  innerPair420Data

set_option maxRecDepth 1000000 in
private theorem leaf2926LocalValidity :
    LeafFacts leaf2926Box leaf2926Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2926Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486621184) }) = true
      norm_num [leaf2926Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2926CertificateValid :
    WideCertificateValid leaf2926Box leaf2926Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk227ValidityFacts chi135ValidityFacts
    leaf2926LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2926CoverageChecked :
    coverageCheck (innerAD leaf2926Box) leaf2926InnerLog = true := by
  rfl'

private theorem leaf2926InnerLogValid :
    leaf2926InnerLog.Valid 8 (innerAD leaf2926Box) :=
  wideLogDataValid_of_cachedCheck endpoint133PositiveFacts
    endpoint20PositiveFacts.valid leaf2926CoverageChecked

private noncomputable def leaf2926InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814657/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2926InputLogOnePlusV_eq :
    leaf2926InputLogOnePlusV = outerEnclosure 24
      (leaf2926Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2926RoundedFacts : LeafRoundedFacts 8
    leaf2926Certificate.logOnePlusV leaf2926InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2926InputLogOnePlusV_eq }

private noncomputable def leaf2926Inputs : Inputs :=
  inputsOfCaches globalInput sk227RoundedInputs
    chi135InputQChi innerPair420Input
    leaf2926InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2926LowerChecked :
    lowerCheck 24 leaf2926Box leaf2926Inputs = true := by
  rfl'

private theorem leaf2926CoversExact : CoversExact 8
    leaf2926Box leaf2926Certificate leaf2926InnerLog leaf2926Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk227RoundedFacts chi135RoundedFacts
    innerPair420RoundedFacts leaf2926RoundedFacts (by rfl)

private theorem leaf2926FlatSound : Sound leaf2926Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2926CertificateValid
    leaf2926InnerLogValid leaf2926CoversExact leaf2926LowerChecked

private noncomputable def leaf2927Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (243/64), kHi := (61/16), chiLo := (23/128), chiHi := (47/256) }

private noncomputable def leaf2927Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742405/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433081856) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1806225173/1073741824) }, upper := { exponent := 0, mantissa := (6963/4096) } }, logOuter := sk228LogOuterCertificate, logK := sk228LogKCertificate, logChi := chi135LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870003711/274866163712) } }, logDArg := sk228LogDArgCertificate }

private noncomputable def leaf2927InnerLog : WideLogData :=
  innerPair420Data

set_option maxRecDepth 1000000 in
private theorem leaf2927LocalValidity :
    LeafFacts leaf2927Box leaf2927Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2927Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433081856) }) = true
      norm_num [leaf2927Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2927CertificateValid :
    WideCertificateValid leaf2927Box leaf2927Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk228ValidityFacts chi135ValidityFacts
    leaf2927LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2927CoverageChecked :
    coverageCheck (innerAD leaf2927Box) leaf2927InnerLog = true := by
  rfl'

private theorem leaf2927InnerLogValid :
    leaf2927InnerLog.Valid 8 (innerAD leaf2927Box) :=
  wideLogDataValid_of_cachedCheck endpoint133PositiveFacts
    endpoint20PositiveFacts.valid leaf2927CoverageChecked

private noncomputable def leaf2927InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629315/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2927InputLogOnePlusV_eq :
    leaf2927InputLogOnePlusV = outerEnclosure 24
      (leaf2927Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2927RoundedFacts : LeafRoundedFacts 8
    leaf2927Certificate.logOnePlusV leaf2927InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2927InputLogOnePlusV_eq }

private noncomputable def leaf2927Inputs : Inputs :=
  inputsOfCaches globalInput sk228RoundedInputs
    chi135InputQChi innerPair420Input
    leaf2927InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2927LowerChecked :
    lowerCheck 24 leaf2927Box leaf2927Inputs = true := by
  rfl'

private theorem leaf2927CoversExact : CoversExact 8
    leaf2927Box leaf2927Certificate leaf2927InnerLog leaf2927Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk228RoundedFacts chi135RoundedFacts
    innerPair420RoundedFacts leaf2927RoundedFacts (by rfl)

private theorem leaf2927FlatSound : Sound leaf2927Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2927CertificateValid
    leaf2927InnerLogValid leaf2927CoversExact leaf2927LowerChecked

private noncomputable def leaf2928Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (243/64), chiLo := (47/256), chiHi := (3/16) }

private noncomputable def leaf2928Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742405/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432981504) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1819069445/1073741824) }, upper := { exponent := 0, mantissa := (1753/1024) } }, logOuter := sk227LogOuterCertificate, logK := sk227LogKCertificate, logChi := chi136LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869903359/274865963008) } }, logDArg := sk227LogDArgCertificate }

private noncomputable def leaf2928InnerLog : WideLogData :=
  innerPair68Data

set_option maxRecDepth 1000000 in
private theorem leaf2928LocalValidity :
    LeafFacts leaf2928Box leaf2928Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2928Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432981504) }) = true
      norm_num [leaf2928Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2928CertificateValid :
    WideCertificateValid leaf2928Box leaf2928Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk227ValidityFacts chi136ValidityFacts
    leaf2928LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2928CoverageChecked :
    coverageCheck (innerAD leaf2928Box) leaf2928InnerLog = true := by
  rfl'

private theorem leaf2928InnerLogValid :
    leaf2928InnerLog.Valid 8 (innerAD leaf2928Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint62PositiveFacts.valid leaf2928CoverageChecked

private noncomputable def leaf2928InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629321/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2928InputLogOnePlusV_eq :
    leaf2928InputLogOnePlusV = outerEnclosure 24
      (leaf2928Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2928RoundedFacts : LeafRoundedFacts 8
    leaf2928Certificate.logOnePlusV leaf2928InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2928InputLogOnePlusV_eq }

private noncomputable def leaf2928Inputs : Inputs :=
  inputsOfCaches globalInput sk227RoundedInputs
    chi136InputQChi innerPair68Input
    leaf2928InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2928LowerChecked :
    lowerCheck 24 leaf2928Box leaf2928Inputs = true := by
  rfl'

private theorem leaf2928CoversExact : CoversExact 8
    leaf2928Box leaf2928Certificate leaf2928InnerLog leaf2928Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk227RoundedFacts chi136RoundedFacts
    innerPair68RoundedFacts leaf2928RoundedFacts (by rfl)

private theorem leaf2928FlatSound : Sound leaf2928Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2928CertificateValid
    leaf2928InnerLogValid leaf2928CoversExact leaf2928LowerChecked

private noncomputable def leaf2929Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (243/64), kHi := (61/16), chiLo := (47/256), chiHi := (3/16) }

private noncomputable def leaf2929Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742407/1073741824) }, vSqrt := { lower := (8191/8192), upper := (8084524815/8084291584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1822149447/1073741824) }, upper := { exponent := 0, mantissa := (439/256) } }, logOuter := sk228LogOuterCertificate, logK := sk228LogKCertificate, logChi := chi136LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16168816399/16168583168) } }, logDArg := sk228LogDArgCertificate }

private noncomputable def leaf2929InnerLog : WideLogData :=
  innerPair68Data

set_option maxRecDepth 1000000 in
private theorem leaf2929LocalValidity :
    LeafFacts leaf2929Box leaf2929Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2929Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8084524815/8084291584) }) = true
      norm_num [leaf2929Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2929CertificateValid :
    WideCertificateValid leaf2929Box leaf2929Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk228ValidityFacts chi136ValidityFacts
    leaf2929LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2929CoverageChecked :
    coverageCheck (innerAD leaf2929Box) leaf2929InnerLog = true := by
  rfl'

private theorem leaf2929InnerLogValid :
    leaf2929InnerLog.Valid 8 (innerAD leaf2929Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint62PositiveFacts.valid leaf2929CoverageChecked

private noncomputable def leaf2929InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629323/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2929InputLogOnePlusV_eq :
    leaf2929InputLogOnePlusV = outerEnclosure 24
      (leaf2929Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2929RoundedFacts : LeafRoundedFacts 8
    leaf2929Certificate.logOnePlusV leaf2929InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2929InputLogOnePlusV_eq }

private noncomputable def leaf2929Inputs : Inputs :=
  inputsOfCaches globalInput sk228RoundedInputs
    chi136InputQChi innerPair68Input
    leaf2929InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2929LowerChecked :
    lowerCheck 24 leaf2929Box leaf2929Inputs = true := by
  rfl'

private theorem leaf2929CoversExact : CoversExact 8
    leaf2929Box leaf2929Certificate leaf2929InnerLog leaf2929Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk228RoundedFacts chi136RoundedFacts
    innerPair68RoundedFacts leaf2929RoundedFacts (by rfl)

private theorem leaf2929FlatSound : Sound leaf2929Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2929CertificateValid
    leaf2929InnerLogValid leaf2929CoversExact leaf2929LowerChecked

private noncomputable def leaf2930Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (245/64), chiLo := (11/64), chiHi := (45/256) }

private noncomputable def leaf2930Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742403/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433308672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1777260031/1073741824) }, upper := { exponent := 0, mantissa := (27409/16384) } }, logOuter := sk229LogOuterCertificate, logK := sk229LogKCertificate, logChi := chi133LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870230527/274866617344) } }, logDArg := sk229LogDArgCertificate }

private noncomputable def leaf2930InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2930LocalValidity :
    LeafFacts leaf2930Box leaf2930Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2930Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433308672) }) = true
      norm_num [leaf2930Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2930CertificateValid :
    WideCertificateValid leaf2930Box leaf2930Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk229ValidityFacts chi133ValidityFacts
    leaf2930LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2930CoverageChecked :
    coverageCheck (innerAD leaf2930Box) leaf2930InnerLog = true := by
  rfl'

private theorem leaf2930InnerLogValid :
    leaf2930InnerLog.Valid 8 (innerAD leaf2930Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2930CoverageChecked

private noncomputable def leaf2930InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629301/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2930InputLogOnePlusV_eq :
    leaf2930InputLogOnePlusV = outerEnclosure 24
      (leaf2930Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2930RoundedFacts : LeafRoundedFacts 8
    leaf2930Certificate.logOnePlusV leaf2930InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2930InputLogOnePlusV_eq }

private noncomputable def leaf2930Inputs : Inputs :=
  inputsOfCaches globalInput sk229RoundedInputs
    chi133InputQChi innerPair56Input
    leaf2930InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2930LowerChecked :
    lowerCheck 24 leaf2930Box leaf2930Inputs = true := by
  rfl'

private theorem leaf2930CoversExact : CoversExact 8
    leaf2930Box leaf2930Certificate leaf2930InnerLog leaf2930Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk229RoundedFacts chi133RoundedFacts
    innerPair56RoundedFacts leaf2930RoundedFacts (by rfl)

private theorem leaf2930FlatSound : Sound leaf2930Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2930CertificateValid
    leaf2930InnerLogValid leaf2930CoversExact leaf2930LowerChecked

private noncomputable def leaf2931Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (245/64), kHi := (123/32), chiLo := (11/64), chiHi := (45/256) }

private noncomputable def leaf2931Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742405/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433285632) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1780143437/1073741824) }, upper := { exponent := 0, mantissa := (13727/8192) } }, logOuter := sk230LogOuterCertificate, logK := sk230LogKCertificate, logChi := chi133LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870207487/274866571264) } }, logDArg := sk230LogDArgCertificate }

private noncomputable def leaf2931InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2931LocalValidity :
    LeafFacts leaf2931Box leaf2931Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2931Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433285632) }) = true
      norm_num [leaf2931Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2931CertificateValid :
    WideCertificateValid leaf2931Box leaf2931Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk230ValidityFacts chi133ValidityFacts
    leaf2931LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2931CoverageChecked :
    coverageCheck (innerAD leaf2931Box) leaf2931InnerLog = true := by
  rfl'

private theorem leaf2931InnerLogValid :
    leaf2931InnerLog.Valid 8 (innerAD leaf2931Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2931CoverageChecked

private noncomputable def leaf2931InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629303/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2931InputLogOnePlusV_eq :
    leaf2931InputLogOnePlusV = outerEnclosure 24
      (leaf2931Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2931RoundedFacts : LeafRoundedFacts 8
    leaf2931Certificate.logOnePlusV leaf2931InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2931InputLogOnePlusV_eq }

private noncomputable def leaf2931Inputs : Inputs :=
  inputsOfCaches globalInput sk230RoundedInputs
    chi133InputQChi innerPair56Input
    leaf2931InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2931LowerChecked :
    lowerCheck 24 leaf2931Box leaf2931Inputs = true := by
  rfl'

private theorem leaf2931CoversExact : CoversExact 8
    leaf2931Box leaf2931Certificate leaf2931InnerLog leaf2931Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk230RoundedFacts chi133RoundedFacts
    innerPair56RoundedFacts leaf2931RoundedFacts (by rfl)

private theorem leaf2931FlatSound : Sound leaf2931Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2931CertificateValid
    leaf2931InnerLogValid leaf2931CoversExact leaf2931LowerChecked

private noncomputable def leaf2932Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (245/64), chiLo := (45/256), chiHi := (23/128) }

private noncomputable def leaf2932Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742405/1073741824) }, vSqrt := { lower := (8191/8192), upper := (8084524815/8084304896) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1793249837/1073741824) }, upper := { exponent := 0, mantissa := (13827/8192) } }, logOuter := sk229LogOuterCertificate, logK := sk229LogKCertificate, logChi := chi134LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16168829711/16168609792) } }, logDArg := sk229LogDArgCertificate }

private noncomputable def leaf2932InnerLog : WideLogData :=
  innerPair173Data

set_option maxRecDepth 1000000 in
private theorem leaf2932LocalValidity :
    LeafFacts leaf2932Box leaf2932Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2932Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8084524815/8084304896) }) = true
      norm_num [leaf2932Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2932CertificateValid :
    WideCertificateValid leaf2932Box leaf2932Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk229ValidityFacts chi134ValidityFacts
    leaf2932LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2932CoverageChecked :
    coverageCheck (innerAD leaf2932Box) leaf2932InnerLog = true := by
  rfl'

private theorem leaf2932InnerLogValid :
    leaf2932InnerLog.Valid 8 (innerAD leaf2932Box) :=
  wideLogDataValid_of_cachedCheck endpoint48PositiveFacts
    endpoint20PositiveFacts.valid leaf2932CoverageChecked

private noncomputable def leaf2932InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629309/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2932InputLogOnePlusV_eq :
    leaf2932InputLogOnePlusV = outerEnclosure 24
      (leaf2932Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2932RoundedFacts : LeafRoundedFacts 8
    leaf2932Certificate.logOnePlusV leaf2932InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2932InputLogOnePlusV_eq }

private noncomputable def leaf2932Inputs : Inputs :=
  inputsOfCaches globalInput sk229RoundedInputs
    chi134InputQChi innerPair173Input
    leaf2932InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2932LowerChecked :
    lowerCheck 24 leaf2932Box leaf2932Inputs = true := by
  rfl'

private theorem leaf2932CoversExact : CoversExact 8
    leaf2932Box leaf2932Certificate leaf2932InnerLog leaf2932Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk229RoundedFacts chi134RoundedFacts
    innerPair173RoundedFacts leaf2932RoundedFacts (by rfl)

private theorem leaf2932FlatSound : Sound leaf2932Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2932CertificateValid
    leaf2932InnerLogValid leaf2932CoversExact leaf2932LowerChecked

private noncomputable def leaf2933Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (245/64), kHi := (123/32), chiLo := (45/256), chiHi := (23/128) }

private noncomputable def leaf2933Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742407/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486631936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1796198775/1073741824) }, upper := { exponent := 0, mantissa := (6925/4096) } }, logOuter := sk230LogOuterCertificate, logK := sk230LogKCertificate, logChi := chi134LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54974016307/54973263872) } }, logDArg := sk230LogDArgCertificate }

private noncomputable def leaf2933InnerLog : WideLogData :=
  innerPair420Data

set_option maxRecDepth 1000000 in
private theorem leaf2933LocalValidity :
    LeafFacts leaf2933Box leaf2933Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2933Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486631936) }) = true
      norm_num [leaf2933Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2933CertificateValid :
    WideCertificateValid leaf2933Box leaf2933Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk230ValidityFacts chi134ValidityFacts
    leaf2933LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2933CoverageChecked :
    coverageCheck (innerAD leaf2933Box) leaf2933InnerLog = true := by
  rfl'

private theorem leaf2933InnerLogValid :
    leaf2933InnerLog.Valid 8 (innerAD leaf2933Box) :=
  wideLogDataValid_of_cachedCheck endpoint133PositiveFacts
    endpoint20PositiveFacts.valid leaf2933CoverageChecked

private noncomputable def leaf2933InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814655/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2933InputLogOnePlusV_eq :
    leaf2933InputLogOnePlusV = outerEnclosure 24
      (leaf2933Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2933RoundedFacts : LeafRoundedFacts 8
    leaf2933Certificate.logOnePlusV leaf2933InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2933InputLogOnePlusV_eq }

private noncomputable def leaf2933Inputs : Inputs :=
  inputsOfCaches globalInput sk230RoundedInputs
    chi134InputQChi innerPair420Input
    leaf2933InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2933LowerChecked :
    lowerCheck 24 leaf2933Box leaf2933Inputs = true := by
  rfl'

private theorem leaf2933CoversExact : CoversExact 8
    leaf2933Box leaf2933Certificate leaf2933InnerLog leaf2933Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk230RoundedFacts chi134RoundedFacts
    innerPair420RoundedFacts leaf2933RoundedFacts (by rfl)

private theorem leaf2933FlatSound : Sound leaf2933Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2933CertificateValid
    leaf2933InnerLogValid leaf2933CoversExact leaf2933LowerChecked

private noncomputable def leaf2934Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (247/64), chiLo := (11/64), chiHi := (45/256) }

private noncomputable def leaf2934Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742407/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433262592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1783026843/1073741824) }, upper := { exponent := 0, mantissa := (27499/16384) } }, logOuter := sk231LogOuterCertificate, logK := sk231LogKCertificate, logChi := chi133LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870184447/274866525184) } }, logDArg := sk231LogDArgCertificate }

private noncomputable def leaf2934InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2934LocalValidity :
    LeafFacts leaf2934Box leaf2934Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2934Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433262592) }) = true
      norm_num [leaf2934Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2934CertificateValid :
    WideCertificateValid leaf2934Box leaf2934Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk231ValidityFacts chi133ValidityFacts
    leaf2934LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2934CoverageChecked :
    coverageCheck (innerAD leaf2934Box) leaf2934InnerLog = true := by
  rfl'

private theorem leaf2934InnerLogValid :
    leaf2934InnerLog.Valid 8 (innerAD leaf2934Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2934CoverageChecked

private noncomputable def leaf2934InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453663/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf2934InputLogOnePlusV_eq :
    leaf2934InputLogOnePlusV = outerEnclosure 24
      (leaf2934Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2934RoundedFacts : LeafRoundedFacts 8
    leaf2934Certificate.logOnePlusV leaf2934InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2934InputLogOnePlusV_eq }

private noncomputable def leaf2934Inputs : Inputs :=
  inputsOfCaches globalInput sk231RoundedInputs
    chi133InputQChi innerPair56Input
    leaf2934InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2934LowerChecked :
    lowerCheck 24 leaf2934Box leaf2934Inputs = true := by
  rfl'

private theorem leaf2934CoversExact : CoversExact 8
    leaf2934Box leaf2934Certificate leaf2934InnerLog leaf2934Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk231RoundedFacts chi133RoundedFacts
    innerPair56RoundedFacts leaf2934RoundedFacts (by rfl)

private theorem leaf2934FlatSound : Sound leaf2934Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2934CertificateValid
    leaf2934InnerLogValid leaf2934CoversExact leaf2934LowerChecked

private noncomputable def leaf2935Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (247/64), kHi := (31/8), chiLo := (11/64), chiHi := (45/256) }

private noncomputable def leaf2935Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742409/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433239552) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1785910249/1073741824) }, upper := { exponent := 0, mantissa := (3443/2048) } }, logOuter := sk232LogOuterCertificate, logK := sk232LogKCertificate, logChi := chi133LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870161407/274866479104) } }, logDArg := sk232LogDArgCertificate }

private noncomputable def leaf2935InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2935LocalValidity :
    LeafFacts leaf2935Box leaf2935Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2935Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433239552) }) = true
      norm_num [leaf2935Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2935CertificateValid :
    WideCertificateValid leaf2935Box leaf2935Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk232ValidityFacts chi133ValidityFacts
    leaf2935LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2935CoverageChecked :
    coverageCheck (innerAD leaf2935Box) leaf2935InnerLog = true := by
  rfl'

private theorem leaf2935InnerLogValid :
    leaf2935InnerLog.Valid 8 (innerAD leaf2935Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2935CoverageChecked

private noncomputable def leaf2935InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814653/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2935InputLogOnePlusV_eq :
    leaf2935InputLogOnePlusV = outerEnclosure 24
      (leaf2935Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2935RoundedFacts : LeafRoundedFacts 8
    leaf2935Certificate.logOnePlusV leaf2935InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2935InputLogOnePlusV_eq }

private noncomputable def leaf2935Inputs : Inputs :=
  inputsOfCaches globalInput sk232RoundedInputs
    chi133InputQChi innerPair56Input
    leaf2935InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2935LowerChecked :
    lowerCheck 24 leaf2935Box leaf2935Inputs = true := by
  rfl'

private theorem leaf2935CoversExact : CoversExact 8
    leaf2935Box leaf2935Certificate leaf2935InnerLog leaf2935Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk232RoundedFacts chi133RoundedFacts
    innerPair56RoundedFacts leaf2935RoundedFacts (by rfl)

private theorem leaf2935FlatSound : Sound leaf2935Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2935CertificateValid
    leaf2935InnerLogValid leaf2935CoversExact leaf2935LowerChecked

private noncomputable def leaf2936Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (247/64), chiLo := (45/256), chiHi := (23/128) }

private noncomputable def leaf2936Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742409/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45811045376) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1799147713/1073741824) }, upper := { exponent := 0, mantissa := (13873/8192) } }, logOuter := sk231LogOuterCertificate, logK := sk231LogKCertificate, logChi := chi134LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623352661/91622090752) } }, logDArg := sk231LogDArgCertificate }

private noncomputable def leaf2936InnerLog : WideLogData :=
  innerPair420Data

set_option maxRecDepth 1000000 in
private theorem leaf2936LocalValidity :
    LeafFacts leaf2936Box leaf2936Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2936Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45811045376) }) = true
      norm_num [leaf2936Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2936CertificateValid :
    WideCertificateValid leaf2936Box leaf2936Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk231ValidityFacts chi134ValidityFacts
    leaf2936LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2936CoverageChecked :
    coverageCheck (innerAD leaf2936Box) leaf2936InnerLog = true := by
  rfl'

private theorem leaf2936InnerLogValid :
    leaf2936InnerLog.Valid 8 (innerAD leaf2936Box) :=
  wideLogDataValid_of_cachedCheck endpoint133PositiveFacts
    endpoint20PositiveFacts.valid leaf2936CoverageChecked

private noncomputable def leaf2936InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (45427/65536) }

set_option maxRecDepth 1000000 in
private theorem leaf2936InputLogOnePlusV_eq :
    leaf2936InputLogOnePlusV = outerEnclosure 24
      (leaf2936Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2936RoundedFacts : LeafRoundedFacts 8
    leaf2936Certificate.logOnePlusV leaf2936InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2936InputLogOnePlusV_eq }

private noncomputable def leaf2936Inputs : Inputs :=
  inputsOfCaches globalInput sk231RoundedInputs
    chi134InputQChi innerPair420Input
    leaf2936InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2936LowerChecked :
    lowerCheck 24 leaf2936Box leaf2936Inputs = true := by
  rfl'

private theorem leaf2936CoversExact : CoversExact 8
    leaf2936Box leaf2936Certificate leaf2936InnerLog leaf2936Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk231RoundedFacts chi134RoundedFacts
    innerPair420RoundedFacts leaf2936RoundedFacts (by rfl)

private theorem leaf2936FlatSound : Sound leaf2936Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2936CertificateValid
    leaf2936InnerLogValid leaf2936CoversExact leaf2936LowerChecked

private noncomputable def leaf2937Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (247/64), kHi := (31/8), chiLo := (45/256), chiHi := (23/128) }

private noncomputable def leaf2937Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742411/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433112576) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1802096651/1073741824) }, upper := { exponent := 0, mantissa := (1737/1024) } }, logOuter := sk232LogOuterCertificate, logK := sk232LogKCertificate, logChi := chi134LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870034431/274866225152) } }, logDArg := sk232LogDArgCertificate }

private noncomputable def leaf2937InnerLog : WideLogData :=
  innerPair420Data

set_option maxRecDepth 1000000 in
private theorem leaf2937LocalValidity :
    LeafFacts leaf2937Box leaf2937Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2937Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433112576) }) = true
      norm_num [leaf2937Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2937CertificateValid :
    WideCertificateValid leaf2937Box leaf2937Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk232ValidityFacts chi134ValidityFacts
    leaf2937LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2937CoverageChecked :
    coverageCheck (innerAD leaf2937Box) leaf2937InnerLog = true := by
  rfl'

private theorem leaf2937InnerLogValid :
    leaf2937InnerLog.Valid 8 (innerAD leaf2937Box) :=
  wideLogDataValid_of_cachedCheck endpoint133PositiveFacts
    endpoint20PositiveFacts.valid leaf2937CoverageChecked

private noncomputable def leaf2937InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629313/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2937InputLogOnePlusV_eq :
    leaf2937InputLogOnePlusV = outerEnclosure 24
      (leaf2937Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2937RoundedFacts : LeafRoundedFacts 8
    leaf2937Certificate.logOnePlusV leaf2937InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2937InputLogOnePlusV_eq }

private noncomputable def leaf2937Inputs : Inputs :=
  inputsOfCaches globalInput sk232RoundedInputs
    chi134InputQChi innerPair420Input
    leaf2937InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2937LowerChecked :
    lowerCheck 24 leaf2937Box leaf2937Inputs = true := by
  rfl'

private theorem leaf2937CoversExact : CoversExact 8
    leaf2937Box leaf2937Certificate leaf2937InnerLog leaf2937Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk232RoundedFacts chi134RoundedFacts
    innerPair420RoundedFacts leaf2937RoundedFacts (by rfl)

private theorem leaf2937FlatSound : Sound leaf2937Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2937CertificateValid
    leaf2937InnerLogValid leaf2937CoversExact leaf2937LowerChecked

private noncomputable def leaf2938Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (245/64), chiLo := (23/128), chiHi := (47/256) }

private noncomputable def leaf2938Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742407/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45811019264) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1809239643/1073741824) }, upper := { exponent := 0, mantissa := (27899/16384) } }, logOuter := sk229LogOuterCertificate, logK := sk229LogKCertificate, logChi := chi135LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623326549/91622038528) } }, logDArg := sk229LogDArgCertificate }

private noncomputable def leaf2938InnerLog : WideLogData :=
  innerPair420Data

set_option maxRecDepth 1000000 in
private theorem leaf2938LocalValidity :
    LeafFacts leaf2938Box leaf2938Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2938Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45811019264) }) = true
      norm_num [leaf2938Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2938CertificateValid :
    WideCertificateValid leaf2938Box leaf2938Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk229ValidityFacts chi135ValidityFacts
    leaf2938LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2938CoverageChecked :
    coverageCheck (innerAD leaf2938Box) leaf2938InnerLog = true := by
  rfl'

private theorem leaf2938InnerLogValid :
    leaf2938InnerLog.Valid 8 (innerAD leaf2938Box) :=
  wideLogDataValid_of_cachedCheck endpoint133PositiveFacts
    endpoint20PositiveFacts.valid leaf2938CoverageChecked

private noncomputable def leaf2938InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629317/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2938InputLogOnePlusV_eq :
    leaf2938InputLogOnePlusV = outerEnclosure 24
      (leaf2938Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2938RoundedFacts : LeafRoundedFacts 8
    leaf2938Certificate.logOnePlusV leaf2938InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2938InputLogOnePlusV_eq }

private noncomputable def leaf2938Inputs : Inputs :=
  inputsOfCaches globalInput sk229RoundedInputs
    chi135InputQChi innerPair420Input
    leaf2938InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2938LowerChecked :
    lowerCheck 24 leaf2938Box leaf2938Inputs = true := by
  rfl'

private theorem leaf2938CoversExact : CoversExact 8
    leaf2938Box leaf2938Certificate leaf2938InnerLog leaf2938Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk229RoundedFacts chi135RoundedFacts
    innerPair420RoundedFacts leaf2938RoundedFacts (by rfl)

private theorem leaf2938FlatSound : Sound leaf2938Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2938CertificateValid
    leaf2938InnerLogValid leaf2938CoversExact leaf2938LowerChecked

private noncomputable def leaf2939Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (245/64), kHi := (123/32), chiLo := (23/128), chiHi := (47/256) }

private noncomputable def leaf2939Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742409/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433033728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1812254113/1073741824) }, upper := { exponent := 0, mantissa := (13973/8192) } }, logOuter := sk230LogOuterCertificate, logK := sk230LogKCertificate, logChi := chi135LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869955583/274866067456) } }, logDArg := sk230LogDArgCertificate }

private noncomputable def leaf2939InnerLog : WideLogData :=
  innerPair68Data

set_option maxRecDepth 1000000 in
private theorem leaf2939LocalValidity :
    LeafFacts leaf2939Box leaf2939Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2939Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433033728) }) = true
      norm_num [leaf2939Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2939CertificateValid :
    WideCertificateValid leaf2939Box leaf2939Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk230ValidityFacts chi135ValidityFacts
    leaf2939LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2939CoverageChecked :
    coverageCheck (innerAD leaf2939Box) leaf2939InnerLog = true := by
  rfl'

private theorem leaf2939InnerLogValid :
    leaf2939InnerLog.Valid 8 (innerAD leaf2939Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint62PositiveFacts.valid leaf2939CoverageChecked

private noncomputable def leaf2939InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814659/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2939InputLogOnePlusV_eq :
    leaf2939InputLogOnePlusV = outerEnclosure 24
      (leaf2939Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2939RoundedFacts : LeafRoundedFacts 8
    leaf2939Certificate.logOnePlusV leaf2939InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2939InputLogOnePlusV_eq }

private noncomputable def leaf2939Inputs : Inputs :=
  inputsOfCaches globalInput sk230RoundedInputs
    chi135InputQChi innerPair68Input
    leaf2939InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2939LowerChecked :
    lowerCheck 24 leaf2939Box leaf2939Inputs = true := by
  rfl'

private theorem leaf2939CoversExact : CoversExact 8
    leaf2939Box leaf2939Certificate leaf2939InnerLog leaf2939Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk230RoundedFacts chi135RoundedFacts
    innerPair68RoundedFacts leaf2939RoundedFacts (by rfl)

private theorem leaf2939FlatSound : Sound leaf2939Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2939CertificateValid
    leaf2939InnerLogValid leaf2939CoversExact leaf2939LowerChecked

private noncomputable def leaf2940Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (245/64), chiLo := (47/256), chiHi := (3/16) }

private noncomputable def leaf2940Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742409/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432932352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1825229449/1073741824) }, upper := { exponent := 0, mantissa := (1759/1024) } }, logOuter := sk229LogOuterCertificate, logK := sk229LogKCertificate, logChi := chi136LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869854207/274865864704) } }, logDArg := sk229LogDArgCertificate }

private noncomputable def leaf2940InnerLog : WideLogData :=
  innerPair68Data

set_option maxRecDepth 1000000 in
private theorem leaf2940LocalValidity :
    LeafFacts leaf2940Box leaf2940Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2940Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432932352) }) = true
      norm_num [leaf2940Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2940CertificateValid :
    WideCertificateValid leaf2940Box leaf2940Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk229ValidityFacts chi136ValidityFacts
    leaf2940LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2940CoverageChecked :
    coverageCheck (innerAD leaf2940Box) leaf2940InnerLog = true := by
  rfl'

private theorem leaf2940InnerLogValid :
    leaf2940InnerLog.Valid 8 (innerAD leaf2940Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint62PositiveFacts.valid leaf2940CoverageChecked

private noncomputable def leaf2940InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907331/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2940InputLogOnePlusV_eq :
    leaf2940InputLogOnePlusV = outerEnclosure 24
      (leaf2940Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2940RoundedFacts : LeafRoundedFacts 8
    leaf2940Certificate.logOnePlusV leaf2940InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2940InputLogOnePlusV_eq }

private noncomputable def leaf2940Inputs : Inputs :=
  inputsOfCaches globalInput sk229RoundedInputs
    chi136InputQChi innerPair68Input
    leaf2940InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2940LowerChecked :
    lowerCheck 24 leaf2940Box leaf2940Inputs = true := by
  rfl'

private theorem leaf2940CoversExact : CoversExact 8
    leaf2940Box leaf2940Certificate leaf2940InnerLog leaf2940Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk229RoundedFacts chi136RoundedFacts
    innerPair68RoundedFacts leaf2940RoundedFacts (by rfl)

private theorem leaf2940FlatSound : Sound leaf2940Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2940CertificateValid
    leaf2940InnerLogValid leaf2940CoversExact leaf2940LowerChecked

private noncomputable def leaf2941Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (245/64), kHi := (123/32), chiLo := (47/256), chiHi := (3/16) }

private noncomputable def leaf2941Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742411/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432907776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1828309451/1073741824) }, upper := { exponent := 0, mantissa := (881/512) } }, logOuter := sk230LogOuterCertificate, logK := sk230LogKCertificate, logChi := chi136LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869829631/274865815552) } }, logDArg := sk230LogDArgCertificate }

private noncomputable def leaf2941InnerLog : WideLogData :=
  innerPair218Data

set_option maxRecDepth 1000000 in
private theorem leaf2941LocalValidity :
    LeafFacts leaf2941Box leaf2941Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2941Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432907776) }) = true
      norm_num [leaf2941Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2941CertificateValid :
    WideCertificateValid leaf2941Box leaf2941Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk230ValidityFacts chi136ValidityFacts
    leaf2941LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2941CoverageChecked :
    coverageCheck (innerAD leaf2941Box) leaf2941InnerLog = true := by
  rfl'

private theorem leaf2941InnerLogValid :
    leaf2941InnerLog.Valid 8 (innerAD leaf2941Box) :=
  wideLogDataValid_of_cachedCheck endpoint65PositiveFacts
    endpoint179PositiveFacts.valid leaf2941CoverageChecked

private noncomputable def leaf2941InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814663/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2941InputLogOnePlusV_eq :
    leaf2941InputLogOnePlusV = outerEnclosure 24
      (leaf2941Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2941RoundedFacts : LeafRoundedFacts 8
    leaf2941Certificate.logOnePlusV leaf2941InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2941InputLogOnePlusV_eq }

private noncomputable def leaf2941Inputs : Inputs :=
  inputsOfCaches globalInput sk230RoundedInputs
    chi136InputQChi innerPair218Input
    leaf2941InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2941LowerChecked :
    lowerCheck 24 leaf2941Box leaf2941Inputs = true := by
  rfl'

private theorem leaf2941CoversExact : CoversExact 8
    leaf2941Box leaf2941Certificate leaf2941InnerLog leaf2941Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk230RoundedFacts chi136RoundedFacts
    innerPair218RoundedFacts leaf2941RoundedFacts (by rfl)

private theorem leaf2941FlatSound : Sound leaf2941Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2941CertificateValid
    leaf2941InnerLogValid leaf2941CoversExact leaf2941LowerChecked

private noncomputable def leaf2942Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (247/64), chiLo := (23/128), chiHi := (47/256) }

private noncomputable def leaf2942Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742411/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433009664) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1815268583/1073741824) }, upper := { exponent := 0, mantissa := (27993/16384) } }, logOuter := sk231LogOuterCertificate, logK := sk231LogKCertificate, logChi := chi135LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869931519/274866019328) } }, logDArg := sk231LogDArgCertificate }

private noncomputable def leaf2942InnerLog : WideLogData :=
  innerPair68Data

set_option maxRecDepth 1000000 in
private theorem leaf2942LocalValidity :
    LeafFacts leaf2942Box leaf2942Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2942Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433009664) }) = true
      norm_num [leaf2942Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2942CertificateValid :
    WideCertificateValid leaf2942Box leaf2942Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk231ValidityFacts chi135ValidityFacts
    leaf2942LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2942CoverageChecked :
    coverageCheck (innerAD leaf2942Box) leaf2942InnerLog = true := by
  rfl'

private theorem leaf2942InnerLogValid :
    leaf2942InnerLog.Valid 8 (innerAD leaf2942Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint62PositiveFacts.valid leaf2942CoverageChecked

private noncomputable def leaf2942InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453665/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf2942InputLogOnePlusV_eq :
    leaf2942InputLogOnePlusV = outerEnclosure 24
      (leaf2942Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2942RoundedFacts : LeafRoundedFacts 8
    leaf2942Certificate.logOnePlusV leaf2942InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2942InputLogOnePlusV_eq }

private noncomputable def leaf2942Inputs : Inputs :=
  inputsOfCaches globalInput sk231RoundedInputs
    chi135InputQChi innerPair68Input
    leaf2942InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2942LowerChecked :
    lowerCheck 24 leaf2942Box leaf2942Inputs = true := by
  rfl'

private theorem leaf2942CoversExact : CoversExact 8
    leaf2942Box leaf2942Certificate leaf2942InnerLog leaf2942Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk231RoundedFacts chi135RoundedFacts
    innerPair68RoundedFacts leaf2942RoundedFacts (by rfl)

private theorem leaf2942FlatSound : Sound leaf2942Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2942CertificateValid
    leaf2942InnerLogValid leaf2942CoversExact leaf2942LowerChecked

private noncomputable def leaf2943Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (247/64), kHi := (31/8), chiLo := (23/128), chiHi := (47/256) }

private noncomputable def leaf2943Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742413/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9162461457/9162199040) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1818283053/1073741824) }, upper := { exponent := 0, mantissa := (3505/2048) } }, logOuter := sk232LogOuterCertificate, logK := sk232LogKCertificate, logChi := chi135LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (18324660497/18324398080) } }, logDArg := sk232LogDArgCertificate }

private noncomputable def leaf2943InnerLog : WideLogData :=
  innerPair68Data

set_option maxRecDepth 1000000 in
private theorem leaf2943LocalValidity :
    LeafFacts leaf2943Box leaf2943Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2943Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9162461457/9162199040) }) = true
      norm_num [leaf2943Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2943CertificateValid :
    WideCertificateValid leaf2943Box leaf2943Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk232ValidityFacts chi135ValidityFacts
    leaf2943LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2943CoverageChecked :
    coverageCheck (innerAD leaf2943Box) leaf2943InnerLog = true := by
  rfl'

private theorem leaf2943InnerLogValid :
    leaf2943InnerLog.Valid 8 (innerAD leaf2943Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint62PositiveFacts.valid leaf2943CoverageChecked

private noncomputable def leaf2943InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629321/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2943InputLogOnePlusV_eq :
    leaf2943InputLogOnePlusV = outerEnclosure 24
      (leaf2943Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2943RoundedFacts : LeafRoundedFacts 8
    leaf2943Certificate.logOnePlusV leaf2943InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2943InputLogOnePlusV_eq }

private noncomputable def leaf2943Inputs : Inputs :=
  inputsOfCaches globalInput sk232RoundedInputs
    chi135InputQChi innerPair68Input
    leaf2943InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2943LowerChecked :
    lowerCheck 24 leaf2943Box leaf2943Inputs = true := by
  rfl'

private theorem leaf2943CoversExact : CoversExact 8
    leaf2943Box leaf2943Certificate leaf2943InnerLog leaf2943Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk232RoundedFacts chi135RoundedFacts
    innerPair68RoundedFacts leaf2943RoundedFacts (by rfl)

private theorem leaf2943FlatSound : Sound leaf2943Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2943CertificateValid
    leaf2943InnerLogValid leaf2943CoversExact leaf2943LowerChecked

private noncomputable def leaf2944Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (247/64), chiLo := (47/256), chiHi := (3/16) }

private noncomputable def leaf2944Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742413/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486576640) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1831389453/1073741824) }, upper := { exponent := 0, mantissa := (1765/1024) } }, logOuter := sk231LogOuterCertificate, logK := sk231LogKCertificate, logChi := chi136LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973961011/54973153280) } }, logDArg := sk231LogDArgCertificate }

private noncomputable def leaf2944InnerLog : WideLogData :=
  innerPair90Data

set_option maxRecDepth 1000000 in
private theorem leaf2944LocalValidity :
    LeafFacts leaf2944Box leaf2944Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2944Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486576640) }) = true
      norm_num [leaf2944Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2944CertificateValid :
    WideCertificateValid leaf2944Box leaf2944Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk231ValidityFacts chi136ValidityFacts
    leaf2944LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2944CoverageChecked :
    coverageCheck (innerAD leaf2944Box) leaf2944InnerLog = true := by
  rfl'

private theorem leaf2944InnerLogValid :
    leaf2944InnerLog.Valid 8 (innerAD leaf2944Box) :=
  wideLogDataValid_of_cachedCheck endpoint20PositiveFacts
    endpoint139PositiveFacts.valid leaf2944CoverageChecked

private noncomputable def leaf2944InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629327/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2944InputLogOnePlusV_eq :
    leaf2944InputLogOnePlusV = outerEnclosure 24
      (leaf2944Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2944RoundedFacts : LeafRoundedFacts 8
    leaf2944Certificate.logOnePlusV leaf2944InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2944InputLogOnePlusV_eq }

private noncomputable def leaf2944Inputs : Inputs :=
  inputsOfCaches globalInput sk231RoundedInputs
    chi136InputQChi innerPair90Input
    leaf2944InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2944LowerChecked :
    lowerCheck 24 leaf2944Box leaf2944Inputs = true := by
  rfl'

private theorem leaf2944CoversExact : CoversExact 8
    leaf2944Box leaf2944Certificate leaf2944InnerLog leaf2944Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk231RoundedFacts chi136RoundedFacts
    innerPair90RoundedFacts leaf2944RoundedFacts (by rfl)

private theorem leaf2944FlatSound : Sound leaf2944Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2944CertificateValid
    leaf2944InnerLogValid leaf2944CoversExact leaf2944LowerChecked

private noncomputable def leaf2945Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (247/64), kHi := (31/8), chiLo := (47/256), chiHi := (3/16) }

private noncomputable def leaf2945Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742415/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432858624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1834469455/1073741824) }, upper := { exponent := 0, mantissa := (221/128) } }, logOuter := sk232LogOuterCertificate, logK := sk232LogKCertificate, logChi := chi136LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869780479/274865717248) } }, logDArg := sk232LogDArgCertificate }

private noncomputable def leaf2945InnerLog : WideLogData :=
  innerPair90Data

set_option maxRecDepth 1000000 in
private theorem leaf2945LocalValidity :
    LeafFacts leaf2945Box leaf2945Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2945Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432858624) }) = true
      norm_num [leaf2945Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2945CertificateValid :
    WideCertificateValid leaf2945Box leaf2945Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk232ValidityFacts chi136ValidityFacts
    leaf2945LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2945CoverageChecked :
    coverageCheck (innerAD leaf2945Box) leaf2945InnerLog = true := by
  rfl'

private theorem leaf2945InnerLogValid :
    leaf2945InnerLog.Valid 8 (innerAD leaf2945Box) :=
  wideLogDataValid_of_cachedCheck endpoint20PositiveFacts
    endpoint139PositiveFacts.valid leaf2945CoverageChecked

private noncomputable def leaf2945InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629329/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2945InputLogOnePlusV_eq :
    leaf2945InputLogOnePlusV = outerEnclosure 24
      (leaf2945Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2945RoundedFacts : LeafRoundedFacts 8
    leaf2945Certificate.logOnePlusV leaf2945InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2945InputLogOnePlusV_eq }

private noncomputable def leaf2945Inputs : Inputs :=
  inputsOfCaches globalInput sk232RoundedInputs
    chi136InputQChi innerPair90Input
    leaf2945InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2945LowerChecked :
    lowerCheck 24 leaf2945Box leaf2945Inputs = true := by
  rfl'

private theorem leaf2945CoversExact : CoversExact 8
    leaf2945Box leaf2945Certificate leaf2945InnerLog leaf2945Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk232RoundedFacts chi136RoundedFacts
    innerPair90RoundedFacts leaf2945RoundedFacts (by rfl)

private theorem leaf2945FlatSound : Sound leaf2945Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2945CertificateValid
    leaf2945InnerLogValid leaf2945CoversExact leaf2945LowerChecked

private noncomputable def component61Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (5/32), chiHi := (41/256) }

set_option maxRecDepth 1000000 in
private theorem component61Node0_sound : Sound component61Node0Box :=
  sound_of_literal_split component61Node0Box leaf2882Box leaf2883Box
    .k (241/64) (by rfl) (by rfl)
    leaf2882FlatSound leaf2883FlatSound

private noncomputable def component61Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (41/256), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component61Node1_sound : Sound component61Node1Box :=
  sound_of_literal_split component61Node1Box leaf2884Box leaf2885Box
    .k (241/64) (by rfl) (by rfl)
    leaf2884FlatSound leaf2885FlatSound

private noncomputable def component61Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component61Node2_sound : Sound component61Node2Box :=
  sound_of_literal_split component61Node2Box component61Node0Box component61Node1Box
    .chi (41/256) (by rfl) (by rfl)
    component61Node0_sound component61Node1_sound

private noncomputable def component61Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (5/32), chiHi := (41/256) }

set_option maxRecDepth 1000000 in
private theorem component61Node3_sound : Sound component61Node3Box :=
  sound_of_literal_split component61Node3Box leaf2886Box leaf2887Box
    .k (243/64) (by rfl) (by rfl)
    leaf2886FlatSound leaf2887FlatSound

private noncomputable def component61Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (41/256), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component61Node4_sound : Sound component61Node4Box :=
  sound_of_literal_split component61Node4Box leaf2888Box leaf2889Box
    .k (243/64) (by rfl) (by rfl)
    leaf2888FlatSound leaf2889FlatSound

private noncomputable def component61Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component61Node5_sound : Sound component61Node5Box :=
  sound_of_literal_split component61Node5Box component61Node3Box component61Node4Box
    .chi (41/256) (by rfl) (by rfl)
    component61Node3_sound component61Node4_sound

private noncomputable def component61Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component61Node6_sound : Sound component61Node6Box :=
  sound_of_literal_split component61Node6Box component61Node2Box component61Node5Box
    .k (121/32) (by rfl) (by rfl)
    component61Node2_sound component61Node5_sound

private noncomputable def component61Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (21/128), chiHi := (43/256) }

set_option maxRecDepth 1000000 in
private theorem component61Node7_sound : Sound component61Node7Box :=
  sound_of_literal_split component61Node7Box leaf2890Box leaf2891Box
    .k (241/64) (by rfl) (by rfl)
    leaf2890FlatSound leaf2891FlatSound

private noncomputable def component61Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (43/256), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component61Node8_sound : Sound component61Node8Box :=
  sound_of_literal_split component61Node8Box leaf2892Box leaf2893Box
    .k (241/64) (by rfl) (by rfl)
    leaf2892FlatSound leaf2893FlatSound

private noncomputable def component61Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component61Node9_sound : Sound component61Node9Box :=
  sound_of_literal_split component61Node9Box component61Node7Box component61Node8Box
    .chi (43/256) (by rfl) (by rfl)
    component61Node7_sound component61Node8_sound

private noncomputable def component61Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (21/128), chiHi := (43/256) }

set_option maxRecDepth 1000000 in
private theorem component61Node10_sound : Sound component61Node10Box :=
  sound_of_literal_split component61Node10Box leaf2894Box leaf2895Box
    .k (243/64) (by rfl) (by rfl)
    leaf2894FlatSound leaf2895FlatSound

private noncomputable def component61Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (43/256), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component61Node11_sound : Sound component61Node11Box :=
  sound_of_literal_split component61Node11Box leaf2896Box leaf2897Box
    .k (243/64) (by rfl) (by rfl)
    leaf2896FlatSound leaf2897FlatSound

private noncomputable def component61Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component61Node12_sound : Sound component61Node12Box :=
  sound_of_literal_split component61Node12Box component61Node10Box component61Node11Box
    .chi (43/256) (by rfl) (by rfl)
    component61Node10_sound component61Node11_sound

private noncomputable def component61Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component61Node13_sound : Sound component61Node13Box :=
  sound_of_literal_split component61Node13Box component61Node9Box component61Node12Box
    .k (121/32) (by rfl) (by rfl)
    component61Node9_sound component61Node12_sound

private noncomputable def component61Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (5/32), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component61Node14_sound : Sound component61Node14Box :=
  sound_of_literal_split component61Node14Box component61Node6Box component61Node13Box
    .chi (21/128) (by rfl) (by rfl)
    component61Node6_sound component61Node13_sound

private noncomputable def component61Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (5/32), chiHi := (41/256) }

set_option maxRecDepth 1000000 in
private theorem component61Node15_sound : Sound component61Node15Box :=
  sound_of_literal_split component61Node15Box leaf2898Box leaf2899Box
    .k (245/64) (by rfl) (by rfl)
    leaf2898FlatSound leaf2899FlatSound

private noncomputable def component61Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (41/256), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component61Node16_sound : Sound component61Node16Box :=
  sound_of_literal_split component61Node16Box leaf2900Box leaf2901Box
    .k (245/64) (by rfl) (by rfl)
    leaf2900FlatSound leaf2901FlatSound

private noncomputable def component61Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component61Node17_sound : Sound component61Node17Box :=
  sound_of_literal_split component61Node17Box component61Node15Box component61Node16Box
    .chi (41/256) (by rfl) (by rfl)
    component61Node15_sound component61Node16_sound

private noncomputable def component61Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (5/32), chiHi := (41/256) }

set_option maxRecDepth 1000000 in
private theorem component61Node18_sound : Sound component61Node18Box :=
  sound_of_literal_split component61Node18Box leaf2902Box leaf2903Box
    .k (247/64) (by rfl) (by rfl)
    leaf2902FlatSound leaf2903FlatSound

private noncomputable def component61Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (41/256), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component61Node19_sound : Sound component61Node19Box :=
  sound_of_literal_split component61Node19Box leaf2904Box leaf2905Box
    .k (247/64) (by rfl) (by rfl)
    leaf2904FlatSound leaf2905FlatSound

private noncomputable def component61Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component61Node20_sound : Sound component61Node20Box :=
  sound_of_literal_split component61Node20Box component61Node18Box component61Node19Box
    .chi (41/256) (by rfl) (by rfl)
    component61Node18_sound component61Node19_sound

private noncomputable def component61Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component61Node21_sound : Sound component61Node21Box :=
  sound_of_literal_split component61Node21Box component61Node17Box component61Node20Box
    .k (123/32) (by rfl) (by rfl)
    component61Node17_sound component61Node20_sound

private noncomputable def component61Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (21/128), chiHi := (43/256) }

set_option maxRecDepth 1000000 in
private theorem component61Node22_sound : Sound component61Node22Box :=
  sound_of_literal_split component61Node22Box leaf2906Box leaf2907Box
    .k (245/64) (by rfl) (by rfl)
    leaf2906FlatSound leaf2907FlatSound

private noncomputable def component61Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (43/256), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component61Node23_sound : Sound component61Node23Box :=
  sound_of_literal_split component61Node23Box leaf2908Box leaf2909Box
    .k (245/64) (by rfl) (by rfl)
    leaf2908FlatSound leaf2909FlatSound

private noncomputable def component61Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component61Node24_sound : Sound component61Node24Box :=
  sound_of_literal_split component61Node24Box component61Node22Box component61Node23Box
    .chi (43/256) (by rfl) (by rfl)
    component61Node22_sound component61Node23_sound

private noncomputable def component61Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (21/128), chiHi := (43/256) }

set_option maxRecDepth 1000000 in
private theorem component61Node25_sound : Sound component61Node25Box :=
  sound_of_literal_split component61Node25Box leaf2910Box leaf2911Box
    .k (247/64) (by rfl) (by rfl)
    leaf2910FlatSound leaf2911FlatSound

private noncomputable def component61Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (43/256), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component61Node26_sound : Sound component61Node26Box :=
  sound_of_literal_split component61Node26Box leaf2912Box leaf2913Box
    .k (247/64) (by rfl) (by rfl)
    leaf2912FlatSound leaf2913FlatSound

private noncomputable def component61Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component61Node27_sound : Sound component61Node27Box :=
  sound_of_literal_split component61Node27Box component61Node25Box component61Node26Box
    .chi (43/256) (by rfl) (by rfl)
    component61Node25_sound component61Node26_sound

private noncomputable def component61Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component61Node28_sound : Sound component61Node28Box :=
  sound_of_literal_split component61Node28Box component61Node24Box component61Node27Box
    .k (123/32) (by rfl) (by rfl)
    component61Node24_sound component61Node27_sound

private noncomputable def component61Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (5/32), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component61Node29_sound : Sound component61Node29Box :=
  sound_of_literal_split component61Node29Box component61Node21Box component61Node28Box
    .chi (21/128) (by rfl) (by rfl)
    component61Node21_sound component61Node28_sound

private noncomputable def component61Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (5/32), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component61Node30_sound : Sound component61Node30Box :=
  sound_of_literal_split component61Node30Box component61Node14Box component61Node29Box
    .k (61/16) (by rfl) (by rfl)
    component61Node14_sound component61Node29_sound

private noncomputable def component61Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (11/64), chiHi := (45/256) }

set_option maxRecDepth 1000000 in
private theorem component61Node31_sound : Sound component61Node31Box :=
  sound_of_literal_split component61Node31Box leaf2914Box leaf2915Box
    .k (241/64) (by rfl) (by rfl)
    leaf2914FlatSound leaf2915FlatSound

private noncomputable def component61Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (45/256), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component61Node32_sound : Sound component61Node32Box :=
  sound_of_literal_split component61Node32Box leaf2916Box leaf2917Box
    .k (241/64) (by rfl) (by rfl)
    leaf2916FlatSound leaf2917FlatSound

private noncomputable def component61Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (11/64), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component61Node33_sound : Sound component61Node33Box :=
  sound_of_literal_split component61Node33Box component61Node31Box component61Node32Box
    .chi (45/256) (by rfl) (by rfl)
    component61Node31_sound component61Node32_sound

private noncomputable def component61Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (11/64), chiHi := (45/256) }

set_option maxRecDepth 1000000 in
private theorem component61Node34_sound : Sound component61Node34Box :=
  sound_of_literal_split component61Node34Box leaf2918Box leaf2919Box
    .k (243/64) (by rfl) (by rfl)
    leaf2918FlatSound leaf2919FlatSound

private noncomputable def component61Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (45/256), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component61Node35_sound : Sound component61Node35Box :=
  sound_of_literal_split component61Node35Box leaf2920Box leaf2921Box
    .k (243/64) (by rfl) (by rfl)
    leaf2920FlatSound leaf2921FlatSound

private noncomputable def component61Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (11/64), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component61Node36_sound : Sound component61Node36Box :=
  sound_of_literal_split component61Node36Box component61Node34Box component61Node35Box
    .chi (45/256) (by rfl) (by rfl)
    component61Node34_sound component61Node35_sound

private noncomputable def component61Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (11/64), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component61Node37_sound : Sound component61Node37Box :=
  sound_of_literal_split component61Node37Box component61Node33Box component61Node36Box
    .k (121/32) (by rfl) (by rfl)
    component61Node33_sound component61Node36_sound

private noncomputable def component61Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (23/128), chiHi := (47/256) }

set_option maxRecDepth 1000000 in
private theorem component61Node38_sound : Sound component61Node38Box :=
  sound_of_literal_split component61Node38Box leaf2922Box leaf2923Box
    .k (241/64) (by rfl) (by rfl)
    leaf2922FlatSound leaf2923FlatSound

private noncomputable def component61Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (47/256), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component61Node39_sound : Sound component61Node39Box :=
  sound_of_literal_split component61Node39Box leaf2924Box leaf2925Box
    .k (241/64) (by rfl) (by rfl)
    leaf2924FlatSound leaf2925FlatSound

private noncomputable def component61Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (23/128), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component61Node40_sound : Sound component61Node40Box :=
  sound_of_literal_split component61Node40Box component61Node38Box component61Node39Box
    .chi (47/256) (by rfl) (by rfl)
    component61Node38_sound component61Node39_sound

private noncomputable def component61Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (23/128), chiHi := (47/256) }

set_option maxRecDepth 1000000 in
private theorem component61Node41_sound : Sound component61Node41Box :=
  sound_of_literal_split component61Node41Box leaf2926Box leaf2927Box
    .k (243/64) (by rfl) (by rfl)
    leaf2926FlatSound leaf2927FlatSound

private noncomputable def component61Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (47/256), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component61Node42_sound : Sound component61Node42Box :=
  sound_of_literal_split component61Node42Box leaf2928Box leaf2929Box
    .k (243/64) (by rfl) (by rfl)
    leaf2928FlatSound leaf2929FlatSound

private noncomputable def component61Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (23/128), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component61Node43_sound : Sound component61Node43Box :=
  sound_of_literal_split component61Node43Box component61Node41Box component61Node42Box
    .chi (47/256) (by rfl) (by rfl)
    component61Node41_sound component61Node42_sound

private noncomputable def component61Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (23/128), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component61Node44_sound : Sound component61Node44Box :=
  sound_of_literal_split component61Node44Box component61Node40Box component61Node43Box
    .k (121/32) (by rfl) (by rfl)
    component61Node40_sound component61Node43_sound

private noncomputable def component61Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (11/64), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component61Node45_sound : Sound component61Node45Box :=
  sound_of_literal_split component61Node45Box component61Node37Box component61Node44Box
    .chi (23/128) (by rfl) (by rfl)
    component61Node37_sound component61Node44_sound

private noncomputable def component61Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (11/64), chiHi := (45/256) }

set_option maxRecDepth 1000000 in
private theorem component61Node46_sound : Sound component61Node46Box :=
  sound_of_literal_split component61Node46Box leaf2930Box leaf2931Box
    .k (245/64) (by rfl) (by rfl)
    leaf2930FlatSound leaf2931FlatSound

private noncomputable def component61Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (45/256), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component61Node47_sound : Sound component61Node47Box :=
  sound_of_literal_split component61Node47Box leaf2932Box leaf2933Box
    .k (245/64) (by rfl) (by rfl)
    leaf2932FlatSound leaf2933FlatSound

private noncomputable def component61Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (11/64), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component61Node48_sound : Sound component61Node48Box :=
  sound_of_literal_split component61Node48Box component61Node46Box component61Node47Box
    .chi (45/256) (by rfl) (by rfl)
    component61Node46_sound component61Node47_sound

private noncomputable def component61Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (11/64), chiHi := (45/256) }

set_option maxRecDepth 1000000 in
private theorem component61Node49_sound : Sound component61Node49Box :=
  sound_of_literal_split component61Node49Box leaf2934Box leaf2935Box
    .k (247/64) (by rfl) (by rfl)
    leaf2934FlatSound leaf2935FlatSound

private noncomputable def component61Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (45/256), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component61Node50_sound : Sound component61Node50Box :=
  sound_of_literal_split component61Node50Box leaf2936Box leaf2937Box
    .k (247/64) (by rfl) (by rfl)
    leaf2936FlatSound leaf2937FlatSound

private noncomputable def component61Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (11/64), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component61Node51_sound : Sound component61Node51Box :=
  sound_of_literal_split component61Node51Box component61Node49Box component61Node50Box
    .chi (45/256) (by rfl) (by rfl)
    component61Node49_sound component61Node50_sound

private noncomputable def component61Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (11/64), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component61Node52_sound : Sound component61Node52Box :=
  sound_of_literal_split component61Node52Box component61Node48Box component61Node51Box
    .k (123/32) (by rfl) (by rfl)
    component61Node48_sound component61Node51_sound

private noncomputable def component61Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (23/128), chiHi := (47/256) }

set_option maxRecDepth 1000000 in
private theorem component61Node53_sound : Sound component61Node53Box :=
  sound_of_literal_split component61Node53Box leaf2938Box leaf2939Box
    .k (245/64) (by rfl) (by rfl)
    leaf2938FlatSound leaf2939FlatSound

private noncomputable def component61Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (47/256), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component61Node54_sound : Sound component61Node54Box :=
  sound_of_literal_split component61Node54Box leaf2940Box leaf2941Box
    .k (245/64) (by rfl) (by rfl)
    leaf2940FlatSound leaf2941FlatSound

private noncomputable def component61Node55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (23/128), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component61Node55_sound : Sound component61Node55Box :=
  sound_of_literal_split component61Node55Box component61Node53Box component61Node54Box
    .chi (47/256) (by rfl) (by rfl)
    component61Node53_sound component61Node54_sound

private noncomputable def component61Node56Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (23/128), chiHi := (47/256) }

set_option maxRecDepth 1000000 in
private theorem component61Node56_sound : Sound component61Node56Box :=
  sound_of_literal_split component61Node56Box leaf2942Box leaf2943Box
    .k (247/64) (by rfl) (by rfl)
    leaf2942FlatSound leaf2943FlatSound

private noncomputable def component61Node57Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (47/256), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component61Node57_sound : Sound component61Node57Box :=
  sound_of_literal_split component61Node57Box leaf2944Box leaf2945Box
    .k (247/64) (by rfl) (by rfl)
    leaf2944FlatSound leaf2945FlatSound

private noncomputable def component61Node58Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (23/128), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component61Node58_sound : Sound component61Node58Box :=
  sound_of_literal_split component61Node58Box component61Node56Box component61Node57Box
    .chi (47/256) (by rfl) (by rfl)
    component61Node56_sound component61Node57_sound

private noncomputable def component61Node59Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (23/128), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component61Node59_sound : Sound component61Node59Box :=
  sound_of_literal_split component61Node59Box component61Node55Box component61Node58Box
    .k (123/32) (by rfl) (by rfl)
    component61Node55_sound component61Node58_sound

private noncomputable def component61Node60Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (11/64), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component61Node60_sound : Sound component61Node60Box :=
  sound_of_literal_split component61Node60Box component61Node52Box component61Node59Box
    .chi (23/128) (by rfl) (by rfl)
    component61Node52_sound component61Node59_sound

private noncomputable def component61Node61Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (11/64), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component61Node61_sound : Sound component61Node61Box :=
  sound_of_literal_split component61Node61Box component61Node45Box component61Node60Box
    .k (61/16) (by rfl) (by rfl)
    component61Node45_sound component61Node60_sound

noncomputable def component61Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (5/32), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
theorem component61_sound : Sound component61Box :=
  sound_of_literal_split component61Box component61Node30Box component61Node61Box
    .chi (11/64) (by rfl) (by rfl)
    component61Node30_sound component61Node61_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
