import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch6
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch10
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch9
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

private noncomputable def leaf5909Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (3/8), chiHi := (97/256) }

private noncomputable def leaf5909Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871347/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356733696) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1291766351/1073741824) }, upper := { exponent := 1, mantissa := (19929/16384) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi305LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715456255/68713467392) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf5909InnerLog : WideLogData :=
  innerPair278Data

set_option maxRecDepth 1000000 in
private theorem leaf5909LocalValidity :
    LeafFacts leaf5909Box leaf5909Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5909Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356733696) }) = true
      norm_num [leaf5909Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5909CertificateValid :
    WideCertificateValid leaf5909Box leaf5909Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi305ValidityFacts
    leaf5909LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5909CoverageChecked :
    coverageCheck (innerAD leaf5909Box) leaf5909InnerLog = true := by
  rfl'

private theorem leaf5909InnerLogValid :
    leaf5909InnerLog.Valid 8 (innerAD leaf5909Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint78PositiveFacts.valid leaf5909CoverageChecked

private noncomputable def leaf5909InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814783/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5909InputLogOnePlusV_eq :
    leaf5909InputLogOnePlusV = outerEnclosure 24
      (leaf5909Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5909RoundedFacts : LeafRoundedFacts 8
    leaf5909Certificate.logOnePlusV leaf5909InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5909InputLogOnePlusV_eq }

private noncomputable def leaf5909Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi305InputQChi innerPair278Input
    leaf5909InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5909LowerChecked :
    lowerCheck 24 leaf5909Box leaf5909Inputs = true := by
  rfl'

private theorem leaf5909CoversExact : CoversExact 8
    leaf5909Box leaf5909Certificate leaf5909InnerLog leaf5909Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi305RoundedFacts
    innerPair278RoundedFacts leaf5909RoundedFacts (by rfl)

private theorem leaf5909FlatSound : Sound leaf5909Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5909CertificateValid
    leaf5909InnerLogValid leaf5909CoversExact leaf5909LowerChecked

private noncomputable def leaf5910Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (97/256), chiHi := (49/128) }

private noncomputable def leaf5910Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871349/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356702720) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1299630189/1073741824) }, upper := { exponent := 1, mantissa := (10025/8192) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi306LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715425279/68713405440) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf5910InnerLog : WideLogData :=
  innerPair590Data

set_option maxRecDepth 1000000 in
private theorem leaf5910LocalValidity :
    LeafFacts leaf5910Box leaf5910Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5910Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356702720) }) = true
      norm_num [leaf5910Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5910CertificateValid :
    WideCertificateValid leaf5910Box leaf5910Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi306ValidityFacts
    leaf5910LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5910CoverageChecked :
    coverageCheck (innerAD leaf5910Box) leaf5910InnerLog = true := by
  rfl'

private theorem leaf5910InnerLogValid :
    leaf5910InnerLog.Valid 8 (innerAD leaf5910Box) :=
  wideLogDataValid_of_cachedCheck endpoint305PositiveFacts
    endpoint403PositiveFacts.valid leaf5910CoverageChecked

private noncomputable def leaf5910InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814787/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5910InputLogOnePlusV_eq :
    leaf5910InputLogOnePlusV = outerEnclosure 24
      (leaf5910Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5910RoundedFacts : LeafRoundedFacts 8
    leaf5910Certificate.logOnePlusV leaf5910InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5910InputLogOnePlusV_eq }

private noncomputable def leaf5910Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi306InputQChi innerPair590Input
    leaf5910InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5910LowerChecked :
    lowerCheck 24 leaf5910Box leaf5910Inputs = true := by
  rfl'

private theorem leaf5910CoversExact : CoversExact 8
    leaf5910Box leaf5910Certificate leaf5910InnerLog leaf5910Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi306RoundedFacts
    innerPair590RoundedFacts leaf5910RoundedFacts (by rfl)

private theorem leaf5910FlatSound : Sound leaf5910Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5910CertificateValid
    leaf5910InnerLogValid leaf5910CoversExact leaf5910LowerChecked

private noncomputable def leaf5911Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (3/8), chiHi := (97/256) }

private noncomputable def leaf5911Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871349/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356708864) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1298057421/1073741824) }, upper := { exponent := 1, mantissa := (10013/8192) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi305LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715431423/68713417728) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf5911InnerLog : WideLogData :=
  innerPair590Data

set_option maxRecDepth 1000000 in
private theorem leaf5911LocalValidity :
    LeafFacts leaf5911Box leaf5911Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5911Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356708864) }) = true
      norm_num [leaf5911Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5911CertificateValid :
    WideCertificateValid leaf5911Box leaf5911Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi305ValidityFacts
    leaf5911LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5911CoverageChecked :
    coverageCheck (innerAD leaf5911Box) leaf5911InnerLog = true := by
  rfl'

private theorem leaf5911InnerLogValid :
    leaf5911InnerLog.Valid 8 (innerAD leaf5911Box) :=
  wideLogDataValid_of_cachedCheck endpoint305PositiveFacts
    endpoint403PositiveFacts.valid leaf5911CoverageChecked

private noncomputable def leaf5911InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907393/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5911InputLogOnePlusV_eq :
    leaf5911InputLogOnePlusV = outerEnclosure 24
      (leaf5911Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5911RoundedFacts : LeafRoundedFacts 8
    leaf5911Certificate.logOnePlusV leaf5911InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5911InputLogOnePlusV_eq }

private noncomputable def leaf5911Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi305InputQChi innerPair590Input
    leaf5911InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5911LowerChecked :
    lowerCheck 24 leaf5911Box leaf5911Inputs = true := by
  rfl'

private theorem leaf5911CoversExact : CoversExact 8
    leaf5911Box leaf5911Certificate leaf5911InnerLog leaf5911Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi305RoundedFacts
    innerPair590RoundedFacts leaf5911RoundedFacts (by rfl)

private theorem leaf5911FlatSound : Sound leaf5911Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5911CertificateValid
    leaf5911InnerLogValid leaf5911CoversExact leaf5911LowerChecked

private noncomputable def leaf5912Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (97/256), chiHi := (49/128) }

private noncomputable def leaf5912Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871351/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356677632) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1305986791/1073741824) }, upper := { exponent := 1, mantissa := (5037/4096) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi306LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715400191/68713355264) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf5912InnerLog : WideLogData :=
  innerPair592Data

set_option maxRecDepth 1000000 in
private theorem leaf5912LocalValidity :
    LeafFacts leaf5912Box leaf5912Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5912Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356677632) }) = true
      norm_num [leaf5912Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5912CertificateValid :
    WideCertificateValid leaf5912Box leaf5912Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi306ValidityFacts
    leaf5912LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5912CoverageChecked :
    coverageCheck (innerAD leaf5912Box) leaf5912InnerLog = true := by
  rfl'

private theorem leaf5912InnerLogValid :
    leaf5912InnerLog.Valid 8 (innerAD leaf5912Box) :=
  wideLogDataValid_of_cachedCheck endpoint308PositiveFacts
    endpoint94PositiveFacts.valid leaf5912CoverageChecked

private noncomputable def leaf5912InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907395/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5912InputLogOnePlusV_eq :
    leaf5912InputLogOnePlusV = outerEnclosure 24
      (leaf5912Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5912RoundedFacts : LeafRoundedFacts 8
    leaf5912Certificate.logOnePlusV leaf5912InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5912InputLogOnePlusV_eq }

private noncomputable def leaf5912Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi306InputQChi innerPair592Input
    leaf5912InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5912LowerChecked :
    lowerCheck 24 leaf5912Box leaf5912Inputs = true := by
  rfl'

private theorem leaf5912CoversExact : CoversExact 8
    leaf5912Box leaf5912Certificate leaf5912InnerLog leaf5912Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi306RoundedFacts
    innerPair592RoundedFacts leaf5912RoundedFacts (by rfl)

private theorem leaf5912FlatSound : Sound leaf5912Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5912CertificateValid
    leaf5912InnerLogValid leaf5912CoversExact leaf5912LowerChecked

private noncomputable def leaf5913Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (49/128), chiHi := (99/256) }

private noncomputable def leaf5913Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871351/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356671744) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1307494027/1073741824) }, upper := { exponent := 1, mantissa := (20171/16384) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi307LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715394303/68713343488) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf5913InnerLog : WideLogData :=
  innerPair279Data

set_option maxRecDepth 1000000 in
private theorem leaf5913LocalValidity :
    LeafFacts leaf5913Box leaf5913Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5913Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356671744) }) = true
      norm_num [leaf5913Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5913CertificateValid :
    WideCertificateValid leaf5913Box leaf5913Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi307ValidityFacts
    leaf5913LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5913CoverageChecked :
    coverageCheck (innerAD leaf5913Box) leaf5913InnerLog = true := by
  rfl'

private theorem leaf5913InnerLogValid :
    leaf5913InnerLog.Valid 8 (innerAD leaf5913Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint79PositiveFacts.valid leaf5913CoverageChecked

private noncomputable def leaf5913InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629581/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5913InputLogOnePlusV_eq :
    leaf5913InputLogOnePlusV = outerEnclosure 24
      (leaf5913Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5913RoundedFacts : LeafRoundedFacts 8
    leaf5913Certificate.logOnePlusV leaf5913InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5913InputLogOnePlusV_eq }

private noncomputable def leaf5913Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi307InputQChi innerPair279Input
    leaf5913InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5913LowerChecked :
    lowerCheck 24 leaf5913Box leaf5913Inputs = true := by
  rfl'

private theorem leaf5913CoversExact : CoversExact 8
    leaf5913Box leaf5913Certificate leaf5913InnerLog leaf5913Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi307RoundedFacts
    innerPair279RoundedFacts leaf5913RoundedFacts (by rfl)

private theorem leaf5913FlatSound : Sound leaf5913Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5913CertificateValid
    leaf5913InnerLogValid leaf5913CoversExact leaf5913LowerChecked

private noncomputable def leaf5914Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (99/256), chiHi := (25/64) }

private noncomputable def leaf5914Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871353/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356640768) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1315357865/1073741824) }, upper := { exponent := 1, mantissa := (5073/4096) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi308LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715363327/68713281536) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf5914InnerLog : WideLogData :=
  innerPair285Data

set_option maxRecDepth 1000000 in
private theorem leaf5914LocalValidity :
    LeafFacts leaf5914Box leaf5914Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5914Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356640768) }) = true
      norm_num [leaf5914Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5914CertificateValid :
    WideCertificateValid leaf5914Box leaf5914Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi308ValidityFacts
    leaf5914LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5914CoverageChecked :
    coverageCheck (innerAD leaf5914Box) leaf5914InnerLog = true := by
  rfl'

private theorem leaf5914InnerLogValid :
    leaf5914InnerLog.Valid 8 (innerAD leaf5914Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint79PositiveFacts.valid leaf5914CoverageChecked

private noncomputable def leaf5914InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629589/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5914InputLogOnePlusV_eq :
    leaf5914InputLogOnePlusV = outerEnclosure 24
      (leaf5914Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5914RoundedFacts : LeafRoundedFacts 8
    leaf5914Certificate.logOnePlusV leaf5914InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5914InputLogOnePlusV_eq }

private noncomputable def leaf5914Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi308InputQChi innerPair285Input
    leaf5914InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5914LowerChecked :
    lowerCheck 24 leaf5914Box leaf5914Inputs = true := by
  rfl'

private theorem leaf5914CoversExact : CoversExact 8
    leaf5914Box leaf5914Certificate leaf5914InnerLog leaf5914Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi308RoundedFacts
    innerPair285RoundedFacts leaf5914RoundedFacts (by rfl)

private theorem leaf5914FlatSound : Sound leaf5914Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5914CertificateValid
    leaf5914InnerLogValid leaf5914CoversExact leaf5914LowerChecked

private noncomputable def leaf5915Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (49/128), chiHi := (99/256) }

private noncomputable def leaf5915Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871353/536870912) }, vSqrt := { lower := (8191/8192), upper := (2021101327/2020979200) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1313916161/1073741824) }, upper := { exponent := 1, mantissa := (10135/8192) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi307LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (4042080527/4041958400) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf5915InnerLog : WideLogData :=
  innerPair285Data

set_option maxRecDepth 1000000 in
private theorem leaf5915LocalValidity :
    LeafFacts leaf5915Box leaf5915Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5915Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (2021101327/2020979200) }) = true
      norm_num [leaf5915Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5915CertificateValid :
    WideCertificateValid leaf5915Box leaf5915Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi307ValidityFacts
    leaf5915LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5915CoverageChecked :
    coverageCheck (innerAD leaf5915Box) leaf5915InnerLog = true := by
  rfl'

private theorem leaf5915InnerLogValid :
    leaf5915InnerLog.Valid 8 (innerAD leaf5915Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint79PositiveFacts.valid leaf5915CoverageChecked

private noncomputable def leaf5915InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907397/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5915InputLogOnePlusV_eq :
    leaf5915InputLogOnePlusV = outerEnclosure 24
      (leaf5915Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5915RoundedFacts : LeafRoundedFacts 8
    leaf5915Certificate.logOnePlusV leaf5915InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5915InputLogOnePlusV_eq }

private noncomputable def leaf5915Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi307InputQChi innerPair285Input
    leaf5915InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5915LowerChecked :
    lowerCheck 24 leaf5915Box leaf5915Inputs = true := by
  rfl'

private theorem leaf5915CoversExact : CoversExact 8
    leaf5915Box leaf5915Certificate leaf5915InnerLog leaf5915Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi307RoundedFacts
    innerPair285RoundedFacts leaf5915RoundedFacts (by rfl)

private theorem leaf5915FlatSound : Sound leaf5915Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5915CertificateValid
    leaf5915InnerLogValid leaf5915CoversExact leaf5915LowerChecked

private noncomputable def leaf5916Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (99/256), chiHi := (25/64) }

private noncomputable def leaf5916Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871355/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68713230336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1321845531/1073741824) }, upper := { exponent := 1, mantissa := (2549/2048) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi308LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429626877/137426460672) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf5916InnerLog : WideLogData :=
  innerPair285Data

set_option maxRecDepth 1000000 in
private theorem leaf5916LocalValidity :
    LeafFacts leaf5916Box leaf5916Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5916Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68713230336) }) = true
      norm_num [leaf5916Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5916CertificateValid :
    WideCertificateValid leaf5916Box leaf5916Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi308ValidityFacts
    leaf5916LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5916CoverageChecked :
    coverageCheck (innerAD leaf5916Box) leaf5916InnerLog = true := by
  rfl'

private theorem leaf5916InnerLogValid :
    leaf5916InnerLog.Valid 8 (innerAD leaf5916Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint79PositiveFacts.valid leaf5916CoverageChecked

private noncomputable def leaf5916InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629467/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5916InputLogOnePlusV_eq :
    leaf5916InputLogOnePlusV = outerEnclosure 24
      (leaf5916Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5916RoundedFacts : LeafRoundedFacts 8
    leaf5916Certificate.logOnePlusV leaf5916InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5916InputLogOnePlusV_eq }

private noncomputable def leaf5916Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi308InputQChi innerPair285Input
    leaf5916InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5916LowerChecked :
    lowerCheck 24 leaf5916Box leaf5916Inputs = true := by
  rfl'

private theorem leaf5916CoversExact : CoversExact 8
    leaf5916Box leaf5916Certificate leaf5916InnerLog leaf5916Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi308RoundedFacts
    innerPair285RoundedFacts leaf5916RoundedFacts (by rfl)

private theorem leaf5916FlatSound : Sound leaf5916Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5916CertificateValid
    leaf5916InnerLogValid leaf5916CoversExact leaf5916LowerChecked

private noncomputable def leaf5917Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (3/8), chiHi := (97/256) }

private noncomputable def leaf5917Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871351/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356684032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1304348491/1073741824) }, upper := { exponent := 1, mantissa := (20123/16384) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi305LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715406591/68713368064) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf5917InnerLog : WideLogData :=
  innerPair592Data

set_option maxRecDepth 1000000 in
private theorem leaf5917LocalValidity :
    LeafFacts leaf5917Box leaf5917Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5917Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356684032) }) = true
      norm_num [leaf5917Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5917CertificateValid :
    WideCertificateValid leaf5917Box leaf5917Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi305ValidityFacts
    leaf5917LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5917CoverageChecked :
    coverageCheck (innerAD leaf5917Box) leaf5917InnerLog = true := by
  rfl'

private theorem leaf5917InnerLogValid :
    leaf5917InnerLog.Valid 8 (innerAD leaf5917Box) :=
  wideLogDataValid_of_cachedCheck endpoint308PositiveFacts
    endpoint94PositiveFacts.valid leaf5917CoverageChecked

private noncomputable def leaf5917InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814789/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5917InputLogOnePlusV_eq :
    leaf5917InputLogOnePlusV = outerEnclosure 24
      (leaf5917Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5917RoundedFacts : LeafRoundedFacts 8
    leaf5917Certificate.logOnePlusV leaf5917InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5917InputLogOnePlusV_eq }

private noncomputable def leaf5917Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi305InputQChi innerPair592Input
    leaf5917InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5917LowerChecked :
    lowerCheck 24 leaf5917Box leaf5917Inputs = true := by
  rfl'

private theorem leaf5917CoversExact : CoversExact 8
    leaf5917Box leaf5917Certificate leaf5917InnerLog leaf5917Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi305RoundedFacts
    innerPair592RoundedFacts leaf5917RoundedFacts (by rfl)

private theorem leaf5917FlatSound : Sound leaf5917Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5917CertificateValid
    leaf5917InnerLogValid leaf5917CoversExact leaf5917LowerChecked

private noncomputable def leaf5918Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (97/256), chiHi := (49/128) }

private noncomputable def leaf5918Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871353/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356652544) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1312343393/1073741824) }, upper := { exponent := 1, mantissa := (10123/8192) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi306LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715375103/68713305088) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf5918InnerLog : WideLogData :=
  innerPair285Data

set_option maxRecDepth 1000000 in
private theorem leaf5918LocalValidity :
    LeafFacts leaf5918Box leaf5918Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5918Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356652544) }) = true
      norm_num [leaf5918Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5918CertificateValid :
    WideCertificateValid leaf5918Box leaf5918Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi306ValidityFacts
    leaf5918LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5918CoverageChecked :
    coverageCheck (innerAD leaf5918Box) leaf5918InnerLog = true := by
  rfl'

private theorem leaf5918InnerLogValid :
    leaf5918InnerLog.Valid 8 (innerAD leaf5918Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint79PositiveFacts.valid leaf5918CoverageChecked

private noncomputable def leaf5918InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814793/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5918InputLogOnePlusV_eq :
    leaf5918InputLogOnePlusV = outerEnclosure 24
      (leaf5918Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5918RoundedFacts : LeafRoundedFacts 8
    leaf5918Certificate.logOnePlusV leaf5918InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5918InputLogOnePlusV_eq }

private noncomputable def leaf5918Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi306InputQChi innerPair285Input
    leaf5918InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5918LowerChecked :
    lowerCheck 24 leaf5918Box leaf5918Inputs = true := by
  rfl'

private theorem leaf5918CoversExact : CoversExact 8
    leaf5918Box leaf5918Certificate leaf5918InnerLog leaf5918Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi306RoundedFacts
    innerPair285RoundedFacts leaf5918RoundedFacts (by rfl)

private theorem leaf5918FlatSound : Sound leaf5918Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5918CertificateValid
    leaf5918InnerLogValid leaf5918CoversExact leaf5918LowerChecked

private noncomputable def leaf5919Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (3/8), chiHi := (97/256) }

private noncomputable def leaf5919Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871353/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356659200) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1310639561/1073741824) }, upper := { exponent := 1, mantissa := (5055/4096) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi305LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715381759/68713318400) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf5919InnerLog : WideLogData :=
  innerPair289Data

set_option maxRecDepth 1000000 in
private theorem leaf5919LocalValidity :
    LeafFacts leaf5919Box leaf5919Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5919Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356659200) }) = true
      norm_num [leaf5919Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5919CertificateValid :
    WideCertificateValid leaf5919Box leaf5919Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi305ValidityFacts
    leaf5919LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5919CoverageChecked :
    coverageCheck (innerAD leaf5919Box) leaf5919InnerLog = true := by
  rfl'

private theorem leaf5919InnerLogValid :
    leaf5919InnerLog.Valid 8 (innerAD leaf5919Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint94PositiveFacts.valid leaf5919CoverageChecked

private noncomputable def leaf5919InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629585/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5919InputLogOnePlusV_eq :
    leaf5919InputLogOnePlusV = outerEnclosure 24
      (leaf5919Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5919RoundedFacts : LeafRoundedFacts 8
    leaf5919Certificate.logOnePlusV leaf5919InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5919InputLogOnePlusV_eq }

private noncomputable def leaf5919Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi305InputQChi innerPair289Input
    leaf5919InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5919LowerChecked :
    lowerCheck 24 leaf5919Box leaf5919Inputs = true := by
  rfl'

private theorem leaf5919CoversExact : CoversExact 8
    leaf5919Box leaf5919Certificate leaf5919InnerLog leaf5919Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi305RoundedFacts
    innerPair289RoundedFacts leaf5919RoundedFacts (by rfl)

private theorem leaf5919FlatSound : Sound leaf5919Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5919CertificateValid
    leaf5919InnerLogValid leaf5919CoversExact leaf5919LowerChecked

private noncomputable def leaf5920Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (97/256), chiHi := (49/128) }

private noncomputable def leaf5920Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871355/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356627456) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1318699995/1073741824) }, upper := { exponent := 1, mantissa := (2543/2048) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi306LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715350015/68713254912) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf5920InnerLog : WideLogData :=
  innerPair285Data

set_option maxRecDepth 1000000 in
private theorem leaf5920LocalValidity :
    LeafFacts leaf5920Box leaf5920Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5920Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356627456) }) = true
      norm_num [leaf5920Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5920CertificateValid :
    WideCertificateValid leaf5920Box leaf5920Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi306ValidityFacts
    leaf5920LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5920CoverageChecked :
    coverageCheck (innerAD leaf5920Box) leaf5920InnerLog = true := by
  rfl'

private theorem leaf5920InnerLogValid :
    leaf5920InnerLog.Valid 8 (innerAD leaf5920Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint79PositiveFacts.valid leaf5920CoverageChecked

private noncomputable def leaf5920InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453699/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5920InputLogOnePlusV_eq :
    leaf5920InputLogOnePlusV = outerEnclosure 24
      (leaf5920Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5920RoundedFacts : LeafRoundedFacts 8
    leaf5920Certificate.logOnePlusV leaf5920InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5920InputLogOnePlusV_eq }

private noncomputable def leaf5920Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi306InputQChi innerPair285Input
    leaf5920InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5920LowerChecked :
    lowerCheck 24 leaf5920Box leaf5920Inputs = true := by
  rfl'

private theorem leaf5920CoversExact : CoversExact 8
    leaf5920Box leaf5920Certificate leaf5920InnerLog leaf5920Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi306RoundedFacts
    innerPair285RoundedFacts leaf5920RoundedFacts (by rfl)

private theorem leaf5920FlatSound : Sound leaf5920Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5920CertificateValid
    leaf5920InnerLogValid leaf5920CoversExact leaf5920LowerChecked

private noncomputable def leaf5921Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (49/128), chiHi := (99/256) }

private noncomputable def leaf5921Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871355/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68713242112) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1320338295/1073741824) }, upper := { exponent := 1, mantissa := (20369/16384) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi307LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429638653/137426484224) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf5921InnerLog : WideLogData :=
  innerPair285Data

set_option maxRecDepth 1000000 in
private theorem leaf5921LocalValidity :
    LeafFacts leaf5921Box leaf5921Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5921Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68713242112) }) = true
      norm_num [leaf5921Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5921CertificateValid :
    WideCertificateValid leaf5921Box leaf5921Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi307ValidityFacts
    leaf5921LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5921CoverageChecked :
    coverageCheck (innerAD leaf5921Box) leaf5921InnerLog = true := by
  rfl'

private theorem leaf5921InnerLogValid :
    leaf5921InnerLog.Valid 8 (innerAD leaf5921Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint79PositiveFacts.valid leaf5921CoverageChecked

private noncomputable def leaf5921InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814733/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5921InputLogOnePlusV_eq :
    leaf5921InputLogOnePlusV = outerEnclosure 24
      (leaf5921Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5921RoundedFacts : LeafRoundedFacts 8
    leaf5921Certificate.logOnePlusV leaf5921InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5921InputLogOnePlusV_eq }

private noncomputable def leaf5921Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi307InputQChi innerPair285Input
    leaf5921InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5921LowerChecked :
    lowerCheck 24 leaf5921Box leaf5921Inputs = true := by
  rfl'

private theorem leaf5921CoversExact : CoversExact 8
    leaf5921Box leaf5921Certificate leaf5921InnerLog leaf5921Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi307RoundedFacts
    innerPair285RoundedFacts leaf5921RoundedFacts (by rfl)

private theorem leaf5921FlatSound : Sound leaf5921Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5921CertificateValid
    leaf5921InnerLogValid leaf5921CoversExact leaf5921LowerChecked

private noncomputable def leaf5922Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (99/256), chiHi := (25/64) }

private noncomputable def leaf5922Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871357/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68713179136) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1328333197/1073741824) }, upper := { exponent := 1, mantissa := (5123/4096) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi308LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429575677/137426358272) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf5922InnerLog : WideLogData :=
  innerPair362Data

set_option maxRecDepth 1000000 in
private theorem leaf5922LocalValidity :
    LeafFacts leaf5922Box leaf5922Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5922Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68713179136) }) = true
      norm_num [leaf5922Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5922CertificateValid :
    WideCertificateValid leaf5922Box leaf5922Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi308ValidityFacts
    leaf5922LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5922CoverageChecked :
    coverageCheck (innerAD leaf5922Box) leaf5922InnerLog = true := by
  rfl'

private theorem leaf5922InnerLogValid :
    leaf5922InnerLog.Valid 8 (innerAD leaf5922Box) :=
  wideLogDataValid_of_cachedCheck endpoint94PositiveFacts
    endpoint419PositiveFacts.valid leaf5922CoverageChecked

private noncomputable def leaf5922InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814737/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5922InputLogOnePlusV_eq :
    leaf5922InputLogOnePlusV = outerEnclosure 24
      (leaf5922Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5922RoundedFacts : LeafRoundedFacts 8
    leaf5922Certificate.logOnePlusV leaf5922InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5922InputLogOnePlusV_eq }

private noncomputable def leaf5922Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi308InputQChi innerPair362Input
    leaf5922InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5922LowerChecked :
    lowerCheck 24 leaf5922Box leaf5922Inputs = true := by
  rfl'

private theorem leaf5922CoversExact : CoversExact 8
    leaf5922Box leaf5922Certificate leaf5922InnerLog leaf5922Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi308RoundedFacts
    innerPair362RoundedFacts leaf5922RoundedFacts (by rfl)

private theorem leaf5922FlatSound : Sound leaf5922Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5922CertificateValid
    leaf5922InnerLogValid leaf5922CoversExact leaf5922LowerChecked

private noncomputable def leaf5923Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (49/128), chiHi := (99/256) }

private noncomputable def leaf5923Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871357/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68713191424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1326760429/1073741824) }, upper := { exponent := 1, mantissa := (5117/4096) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi307LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429587965/137426382848) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf5923InnerLog : WideLogData :=
  innerPair285Data

set_option maxRecDepth 1000000 in
private theorem leaf5923LocalValidity :
    LeafFacts leaf5923Box leaf5923Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5923Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68713191424) }) = true
      norm_num [leaf5923Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5923CertificateValid :
    WideCertificateValid leaf5923Box leaf5923Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi307ValidityFacts
    leaf5923LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5923CoverageChecked :
    coverageCheck (innerAD leaf5923Box) leaf5923InnerLog = true := by
  rfl'

private theorem leaf5923InnerLogValid :
    leaf5923InnerLog.Valid 8 (innerAD leaf5923Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint79PositiveFacts.valid leaf5923CoverageChecked

private noncomputable def leaf5923InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (363421/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf5923InputLogOnePlusV_eq :
    leaf5923InputLogOnePlusV = outerEnclosure 24
      (leaf5923Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5923RoundedFacts : LeafRoundedFacts 8
    leaf5923Certificate.logOnePlusV leaf5923InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5923InputLogOnePlusV_eq }

private noncomputable def leaf5923Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi307InputQChi innerPair285Input
    leaf5923InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5923LowerChecked :
    lowerCheck 24 leaf5923Box leaf5923Inputs = true := by
  rfl'

private theorem leaf5923CoversExact : CoversExact 8
    leaf5923Box leaf5923Certificate leaf5923InnerLog leaf5923Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi307RoundedFacts
    innerPair285RoundedFacts leaf5923RoundedFacts (by rfl)

private theorem leaf5923FlatSound : Sound leaf5923Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5923CertificateValid
    leaf5923InnerLogValid leaf5923CoversExact leaf5923LowerChecked

private noncomputable def leaf5924Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (99/256), chiHi := (25/64) }

private noncomputable def leaf5924Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871359/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68713127936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1334820863/1073741824) }, upper := { exponent := 1, mantissa := (1287/1024) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi308LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429524477/137426255872) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf5924InnerLog : WideLogData :=
  innerPair667Data

set_option maxRecDepth 1000000 in
private theorem leaf5924LocalValidity :
    LeafFacts leaf5924Box leaf5924Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5924Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68713127936) }) = true
      norm_num [leaf5924Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5924CertificateValid :
    WideCertificateValid leaf5924Box leaf5924Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi308ValidityFacts
    leaf5924LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5924CoverageChecked :
    coverageCheck (innerAD leaf5924Box) leaf5924InnerLog = true := by
  rfl'

private theorem leaf5924InnerLogValid :
    leaf5924InnerLog.Valid 8 (innerAD leaf5924Box) :=
  wideLogDataValid_of_cachedCheck endpoint414PositiveFacts
    endpoint419PositiveFacts.valid leaf5924CoverageChecked

private noncomputable def leaf5924InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453685/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5924InputLogOnePlusV_eq :
    leaf5924InputLogOnePlusV = outerEnclosure 24
      (leaf5924Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5924RoundedFacts : LeafRoundedFacts 8
    leaf5924Certificate.logOnePlusV leaf5924InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5924InputLogOnePlusV_eq }

private noncomputable def leaf5924Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi308InputQChi innerPair667Input
    leaf5924InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5924LowerChecked :
    lowerCheck 24 leaf5924Box leaf5924Inputs = true := by
  rfl'

private theorem leaf5924CoversExact : CoversExact 8
    leaf5924Box leaf5924Certificate leaf5924InnerLog leaf5924Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi308RoundedFacts
    innerPair667RoundedFacts leaf5924RoundedFacts (by rfl)

private theorem leaf5924FlatSound : Sound leaf5924Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5924CertificateValid
    leaf5924InnerLogValid leaf5924CoversExact leaf5924LowerChecked

private noncomputable def leaf5925Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (25/64), chiHi := (101/256) }

private noncomputable def leaf5925Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871355/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68713219584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1323221703/1073741824) }, upper := { exponent := 1, mantissa := (20413/16384) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi309LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429616125/137426439168) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf5925InnerLog : WideLogData :=
  innerPair285Data

set_option maxRecDepth 1000000 in
private theorem leaf5925LocalValidity :
    LeafFacts leaf5925Box leaf5925Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5925Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68713219584) }) = true
      norm_num [leaf5925Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5925CertificateValid :
    WideCertificateValid leaf5925Box leaf5925Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi309ValidityFacts
    leaf5925LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5925CoverageChecked :
    coverageCheck (innerAD leaf5925Box) leaf5925InnerLog = true := by
  rfl'

private theorem leaf5925InnerLogValid :
    leaf5925InnerLog.Valid 8 (innerAD leaf5925Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint79PositiveFacts.valid leaf5925CoverageChecked

private noncomputable def leaf5925InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629469/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5925InputLogOnePlusV_eq :
    leaf5925InputLogOnePlusV = outerEnclosure 24
      (leaf5925Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5925RoundedFacts : LeafRoundedFacts 8
    leaf5925Certificate.logOnePlusV leaf5925InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5925InputLogOnePlusV_eq }

private noncomputable def leaf5925Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi309InputQChi innerPair285Input
    leaf5925InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5925LowerChecked :
    lowerCheck 24 leaf5925Box leaf5925Inputs = true := by
  rfl'

private theorem leaf5925CoversExact : CoversExact 8
    leaf5925Box leaf5925Certificate leaf5925InnerLog leaf5925Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi309RoundedFacts
    innerPair285RoundedFacts leaf5925RoundedFacts (by rfl)

private theorem leaf5925FlatSound : Sound leaf5925Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5925CertificateValid
    leaf5925InnerLogValid leaf5925CoversExact leaf5925LowerChecked

private noncomputable def leaf5926Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (101/256), chiHi := (51/128) }

private noncomputable def leaf5926Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871357/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68713157632) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1331085541/1073741824) }, upper := { exponent := 1, mantissa := (10267/8192) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi310LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429554173/137426315264) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf5926InnerLog : WideLogData :=
  innerPair362Data

set_option maxRecDepth 1000000 in
private theorem leaf5926LocalValidity :
    LeafFacts leaf5926Box leaf5926Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5926Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68713157632) }) = true
      norm_num [leaf5926Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5926CertificateValid :
    WideCertificateValid leaf5926Box leaf5926Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi310ValidityFacts
    leaf5926LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5926CoverageChecked :
    coverageCheck (innerAD leaf5926Box) leaf5926InnerLog = true := by
  rfl'

private theorem leaf5926InnerLogValid :
    leaf5926InnerLog.Valid 8 (innerAD leaf5926Box) :=
  wideLogDataValid_of_cachedCheck endpoint94PositiveFacts
    endpoint419PositiveFacts.valid leaf5926CoverageChecked

private noncomputable def leaf5926InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907369/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5926InputLogOnePlusV_eq :
    leaf5926InputLogOnePlusV = outerEnclosure 24
      (leaf5926Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5926RoundedFacts : LeafRoundedFacts 8
    leaf5926Certificate.logOnePlusV leaf5926InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5926InputLogOnePlusV_eq }

private noncomputable def leaf5926Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi310InputQChi innerPair362Input
    leaf5926InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5926LowerChecked :
    lowerCheck 24 leaf5926Box leaf5926Inputs = true := by
  rfl'

private theorem leaf5926CoversExact : CoversExact 8
    leaf5926Box leaf5926Certificate leaf5926InnerLog leaf5926Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi310RoundedFacts
    innerPair362RoundedFacts leaf5926RoundedFacts (by rfl)

private theorem leaf5926FlatSound : Sound leaf5926Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5926CertificateValid
    leaf5926InnerLogValid leaf5926CoversExact leaf5926LowerChecked

private noncomputable def leaf5927Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (25/64), chiHi := (101/256) }

private noncomputable def leaf5927Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871357/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68713167872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1329774901/1073741824) }, upper := { exponent := 1, mantissa := (10257/8192) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi309LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429564413/137426335744) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf5927InnerLog : WideLogData :=
  innerPair362Data

set_option maxRecDepth 1000000 in
private theorem leaf5927LocalValidity :
    LeafFacts leaf5927Box leaf5927Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5927Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68713167872) }) = true
      norm_num [leaf5927Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5927CertificateValid :
    WideCertificateValid leaf5927Box leaf5927Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi309ValidityFacts
    leaf5927LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5927CoverageChecked :
    coverageCheck (innerAD leaf5927Box) leaf5927InnerLog = true := by
  rfl'

private theorem leaf5927InnerLogValid :
    leaf5927InnerLog.Valid 8 (innerAD leaf5927Box) :=
  wideLogDataValid_of_cachedCheck endpoint94PositiveFacts
    endpoint419PositiveFacts.valid leaf5927CoverageChecked

private noncomputable def leaf5927InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629475/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5927InputLogOnePlusV_eq :
    leaf5927InputLogOnePlusV = outerEnclosure 24
      (leaf5927Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5927RoundedFacts : LeafRoundedFacts 8
    leaf5927Certificate.logOnePlusV leaf5927InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5927InputLogOnePlusV_eq }

private noncomputable def leaf5927Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi309InputQChi innerPair362Input
    leaf5927InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5927LowerChecked :
    lowerCheck 24 leaf5927Box leaf5927Inputs = true := by
  rfl'

private theorem leaf5927CoversExact : CoversExact 8
    leaf5927Box leaf5927Certificate leaf5927InnerLog leaf5927Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi309RoundedFacts
    innerPair362RoundedFacts leaf5927RoundedFacts (by rfl)

private theorem leaf5927FlatSound : Sound leaf5927Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5927CertificateValid
    leaf5927InnerLogValid leaf5927CoversExact leaf5927LowerChecked

private noncomputable def leaf5928Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (101/256), chiHi := (51/128) }

private noncomputable def leaf5928Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871359/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68713105408) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1337704271/1073741824) }, upper := { exponent := 1, mantissa := (5159/4096) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi310LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429501949/137426210816) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf5928InnerLog : WideLogData :=
  innerPair286Data

set_option maxRecDepth 1000000 in
private theorem leaf5928LocalValidity :
    LeafFacts leaf5928Box leaf5928Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5928Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68713105408) }) = true
      norm_num [leaf5928Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5928CertificateValid :
    WideCertificateValid leaf5928Box leaf5928Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi310ValidityFacts
    leaf5928LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5928CoverageChecked :
    coverageCheck (innerAD leaf5928Box) leaf5928InnerLog = true := by
  rfl'

private theorem leaf5928InnerLogValid :
    leaf5928InnerLog.Valid 8 (innerAD leaf5928Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint90PositiveFacts.valid leaf5928CoverageChecked

private noncomputable def leaf5928InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629483/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5928InputLogOnePlusV_eq :
    leaf5928InputLogOnePlusV = outerEnclosure 24
      (leaf5928Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5928RoundedFacts : LeafRoundedFacts 8
    leaf5928Certificate.logOnePlusV leaf5928InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5928InputLogOnePlusV_eq }

private noncomputable def leaf5928Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi310InputQChi innerPair286Input
    leaf5928InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5928LowerChecked :
    lowerCheck 24 leaf5928Box leaf5928Inputs = true := by
  rfl'

private theorem leaf5928CoversExact : CoversExact 8
    leaf5928Box leaf5928Certificate leaf5928InnerLog leaf5928Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi310RoundedFacts
    innerPair286RoundedFacts leaf5928RoundedFacts (by rfl)

private theorem leaf5928FlatSound : Sound leaf5928Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5928CertificateValid
    leaf5928InnerLogValid leaf5928CoversExact leaf5928LowerChecked

private noncomputable def leaf5929Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (51/128), chiHi := (103/256) }

private noncomputable def leaf5929Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871359/536870912) }, vSqrt := { lower := (8191/8192), upper := (967836571/967790080) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1338949379/1073741824) }, upper := { exponent := 1, mantissa := (20655/16384) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi311LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (1935626651/1935580160) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf5929InnerLog : WideLogData :=
  innerPair286Data

set_option maxRecDepth 1000000 in
private theorem leaf5929LocalValidity :
    LeafFacts leaf5929Box leaf5929Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5929Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (967836571/967790080) }) = true
      norm_num [leaf5929Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5929CertificateValid :
    WideCertificateValid leaf5929Box leaf5929Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi311ValidityFacts
    leaf5929LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5929CoverageChecked :
    coverageCheck (innerAD leaf5929Box) leaf5929InnerLog = true := by
  rfl'

private theorem leaf5929InnerLogValid :
    leaf5929InnerLog.Valid 8 (innerAD leaf5929Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint90PositiveFacts.valid leaf5929CoverageChecked

private noncomputable def leaf5929InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907371/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5929InputLogOnePlusV_eq :
    leaf5929InputLogOnePlusV = outerEnclosure 24
      (leaf5929Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5929RoundedFacts : LeafRoundedFacts 8
    leaf5929Certificate.logOnePlusV leaf5929InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5929InputLogOnePlusV_eq }

private noncomputable def leaf5929Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi311InputQChi innerPair286Input
    leaf5929InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5929LowerChecked :
    lowerCheck 24 leaf5929Box leaf5929Inputs = true := by
  rfl'

private theorem leaf5929CoversExact : CoversExact 8
    leaf5929Box leaf5929Certificate leaf5929InnerLog leaf5929Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi311RoundedFacts
    innerPair286RoundedFacts leaf5929RoundedFacts (by rfl)

private theorem leaf5929FlatSound : Sound leaf5929Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5929CertificateValid
    leaf5929InnerLogValid leaf5929CoversExact leaf5929LowerChecked

private noncomputable def leaf5930Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (103/256), chiHi := (13/32) }

private noncomputable def leaf5930Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871361/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68713033728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1346813217/1073741824) }, upper := { exponent := 1, mantissa := (2597/2048) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi312LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429430269/137426067456) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf5930InnerLog : WideLogData :=
  innerPair293Data

set_option maxRecDepth 1000000 in
private theorem leaf5930LocalValidity :
    LeafFacts leaf5930Box leaf5930Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5930Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68713033728) }) = true
      norm_num [leaf5930Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5930CertificateValid :
    WideCertificateValid leaf5930Box leaf5930Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi312ValidityFacts
    leaf5930LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5930CoverageChecked :
    coverageCheck (innerAD leaf5930Box) leaf5930InnerLog = true := by
  rfl'

private theorem leaf5930InnerLogValid :
    leaf5930InnerLog.Valid 8 (innerAD leaf5930Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint90PositiveFacts.valid leaf5930CoverageChecked

private noncomputable def leaf5930InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629491/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5930InputLogOnePlusV_eq :
    leaf5930InputLogOnePlusV = outerEnclosure 24
      (leaf5930Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5930RoundedFacts : LeafRoundedFacts 8
    leaf5930Certificate.logOnePlusV leaf5930InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5930InputLogOnePlusV_eq }

private noncomputable def leaf5930Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi312InputQChi innerPair293Input
    leaf5930InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5930LowerChecked :
    lowerCheck 24 leaf5930Box leaf5930Inputs = true := by
  rfl'

private theorem leaf5930CoversExact : CoversExact 8
    leaf5930Box leaf5930Certificate leaf5930InnerLog leaf5930Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi312RoundedFacts
    innerPair293RoundedFacts leaf5930RoundedFacts (by rfl)

private theorem leaf5930FlatSound : Sound leaf5930Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5930CertificateValid
    leaf5930InnerLogValid leaf5930CoversExact leaf5930LowerChecked

private noncomputable def leaf5931Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (51/128), chiHi := (103/256) }

private noncomputable def leaf5931Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871361/536870912) }, vSqrt := { lower := (8191/8192), upper := (5285876657/5285618688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1345633641/1073741824) }, upper := { exponent := 1, mantissa := (10379/8192) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi311LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (10571495345/10571237376) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf5931InnerLog : WideLogData :=
  innerPair293Data

set_option maxRecDepth 1000000 in
private theorem leaf5931LocalValidity :
    LeafFacts leaf5931Box leaf5931Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5931Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5285876657/5285618688) }) = true
      norm_num [leaf5931Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5931CertificateValid :
    WideCertificateValid leaf5931Box leaf5931Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi311ValidityFacts
    leaf5931LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5931CoverageChecked :
    coverageCheck (innerAD leaf5931Box) leaf5931InnerLog = true := by
  rfl'

private theorem leaf5931InnerLogValid :
    leaf5931InnerLog.Valid 8 (innerAD leaf5931Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint90PositiveFacts.valid leaf5931CoverageChecked

private noncomputable def leaf5931InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814745/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5931InputLogOnePlusV_eq :
    leaf5931InputLogOnePlusV = outerEnclosure 24
      (leaf5931Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5931RoundedFacts : LeafRoundedFacts 8
    leaf5931Certificate.logOnePlusV leaf5931InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5931InputLogOnePlusV_eq }

private noncomputable def leaf5931Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi311InputQChi innerPair293Input
    leaf5931InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5931LowerChecked :
    lowerCheck 24 leaf5931Box leaf5931Inputs = true := by
  rfl'

private theorem leaf5931CoversExact : CoversExact 8
    leaf5931Box leaf5931Certificate leaf5931InnerLog leaf5931Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi311RoundedFacts
    innerPair293RoundedFacts leaf5931RoundedFacts (by rfl)

private theorem leaf5931FlatSound : Sound leaf5931Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5931CertificateValid
    leaf5931InnerLogValid leaf5931CoversExact leaf5931LowerChecked

private noncomputable def leaf5932Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (103/256), chiHi := (13/32) }

private noncomputable def leaf5932Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871363/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712980480) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1353563011/1073741824) }, upper := { exponent := 1, mantissa := (1305/1024) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi312LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429377021/137425960960) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf5932InnerLog : WideLogData :=
  innerPair293Data

set_option maxRecDepth 1000000 in
private theorem leaf5932LocalValidity :
    LeafFacts leaf5932Box leaf5932Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5932Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712980480) }) = true
      norm_num [leaf5932Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5932CertificateValid :
    WideCertificateValid leaf5932Box leaf5932Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi312ValidityFacts
    leaf5932LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5932CoverageChecked :
    coverageCheck (innerAD leaf5932Box) leaf5932InnerLog = true := by
  rfl'

private theorem leaf5932InnerLogValid :
    leaf5932InnerLog.Valid 8 (innerAD leaf5932Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint90PositiveFacts.valid leaf5932CoverageChecked

private noncomputable def leaf5932InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814749/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5932InputLogOnePlusV_eq :
    leaf5932InputLogOnePlusV = outerEnclosure 24
      (leaf5932Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5932RoundedFacts : LeafRoundedFacts 8
    leaf5932Certificate.logOnePlusV leaf5932InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5932InputLogOnePlusV_eq }

private noncomputable def leaf5932Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi312InputQChi innerPair293Input
    leaf5932InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5932LowerChecked :
    lowerCheck 24 leaf5932Box leaf5932Inputs = true := by
  rfl'

private theorem leaf5932CoversExact : CoversExact 8
    leaf5932Box leaf5932Certificate leaf5932InnerLog leaf5932Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi312RoundedFacts
    innerPair293RoundedFacts leaf5932RoundedFacts (by rfl)

private theorem leaf5932FlatSound : Sound leaf5932Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5932CertificateValid
    leaf5932InnerLogValid leaf5932CoversExact leaf5932LowerChecked

private noncomputable def leaf5933Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (25/64), chiHi := (101/256) }

private noncomputable def leaf5933Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871359/536870912) }, vSqrt := { lower := (8191/8192), upper := (5285876657/5285624320) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1336328099/1073741824) }, upper := { exponent := 1, mantissa := (20615/16384) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi309LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (10571500977/10571248640) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf5933InnerLog : WideLogData :=
  innerPair668Data

set_option maxRecDepth 1000000 in
private theorem leaf5933LocalValidity :
    LeafFacts leaf5933Box leaf5933Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5933Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5285876657/5285624320) }) = true
      norm_num [leaf5933Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5933CertificateValid :
    WideCertificateValid leaf5933Box leaf5933Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi309ValidityFacts
    leaf5933LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5933CoverageChecked :
    coverageCheck (innerAD leaf5933Box) leaf5933InnerLog = true := by
  rfl'

private theorem leaf5933InnerLogValid :
    leaf5933InnerLog.Valid 8 (innerAD leaf5933Box) :=
  wideLogDataValid_of_cachedCheck endpoint414PositiveFacts
    endpoint434PositiveFacts.valid leaf5933CoverageChecked

private noncomputable def leaf5933InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629481/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5933InputLogOnePlusV_eq :
    leaf5933InputLogOnePlusV = outerEnclosure 24
      (leaf5933Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5933RoundedFacts : LeafRoundedFacts 8
    leaf5933Certificate.logOnePlusV leaf5933InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5933InputLogOnePlusV_eq }

private noncomputable def leaf5933Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi309InputQChi innerPair668Input
    leaf5933InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5933LowerChecked :
    lowerCheck 24 leaf5933Box leaf5933Inputs = true := by
  rfl'

private theorem leaf5933CoversExact : CoversExact 8
    leaf5933Box leaf5933Certificate leaf5933InnerLog leaf5933Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi309RoundedFacts
    innerPair668RoundedFacts leaf5933RoundedFacts (by rfl)

private theorem leaf5933FlatSound : Sound leaf5933Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5933CertificateValid
    leaf5933InnerLogValid leaf5933CoversExact leaf5933LowerChecked

private noncomputable def leaf5934Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (101/256), chiHi := (51/128) }

private noncomputable def leaf5934Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871361/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68713053184) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1344323001/1073741824) }, upper := { exponent := 1, mantissa := (10369/8192) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi310LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429449725/137426106368) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf5934InnerLog : WideLogData :=
  innerPair293Data

set_option maxRecDepth 1000000 in
private theorem leaf5934LocalValidity :
    LeafFacts leaf5934Box leaf5934Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5934Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68713053184) }) = true
      norm_num [leaf5934Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5934CertificateValid :
    WideCertificateValid leaf5934Box leaf5934Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi310ValidityFacts
    leaf5934LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5934CoverageChecked :
    coverageCheck (innerAD leaf5934Box) leaf5934InnerLog = true := by
  rfl'

private theorem leaf5934InnerLogValid :
    leaf5934InnerLog.Valid 8 (innerAD leaf5934Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint90PositiveFacts.valid leaf5934CoverageChecked

private noncomputable def leaf5934InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629489/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5934InputLogOnePlusV_eq :
    leaf5934InputLogOnePlusV = outerEnclosure 24
      (leaf5934Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5934RoundedFacts : LeafRoundedFacts 8
    leaf5934Certificate.logOnePlusV leaf5934InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5934InputLogOnePlusV_eq }

private noncomputable def leaf5934Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi310InputQChi innerPair293Input
    leaf5934InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5934LowerChecked :
    lowerCheck 24 leaf5934Box leaf5934Inputs = true := by
  rfl'

private theorem leaf5934CoversExact : CoversExact 8
    leaf5934Box leaf5934Certificate leaf5934InnerLog leaf5934Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi310RoundedFacts
    innerPair293RoundedFacts leaf5934RoundedFacts (by rfl)

private theorem leaf5934FlatSound : Sound leaf5934Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5934CertificateValid
    leaf5934InnerLogValid leaf5934CoversExact leaf5934LowerChecked

private noncomputable def leaf5935Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (25/64), chiHi := (101/256) }

private noncomputable def leaf5935Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871361/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68713064448) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1342881297/1073741824) }, upper := { exponent := 1, mantissa := (5179/4096) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi309LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429460989/137426128896) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf5935InnerLog : WideLogData :=
  innerPair293Data

set_option maxRecDepth 1000000 in
private theorem leaf5935LocalValidity :
    LeafFacts leaf5935Box leaf5935Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5935Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68713064448) }) = true
      norm_num [leaf5935Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5935CertificateValid :
    WideCertificateValid leaf5935Box leaf5935Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi309ValidityFacts
    leaf5935LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5935CoverageChecked :
    coverageCheck (innerAD leaf5935Box) leaf5935InnerLog = true := by
  rfl'

private theorem leaf5935InnerLogValid :
    leaf5935InnerLog.Valid 8 (innerAD leaf5935Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint90PositiveFacts.valid leaf5935CoverageChecked

private noncomputable def leaf5935InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726843/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf5935InputLogOnePlusV_eq :
    leaf5935InputLogOnePlusV = outerEnclosure 24
      (leaf5935Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5935RoundedFacts : LeafRoundedFacts 8
    leaf5935Certificate.logOnePlusV leaf5935InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5935InputLogOnePlusV_eq }

private noncomputable def leaf5935Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi309InputQChi innerPair293Input
    leaf5935InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5935LowerChecked :
    lowerCheck 24 leaf5935Box leaf5935Inputs = true := by
  rfl'

private theorem leaf5935CoversExact : CoversExact 8
    leaf5935Box leaf5935Certificate leaf5935InnerLog leaf5935Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi309RoundedFacts
    innerPair293RoundedFacts leaf5935RoundedFacts (by rfl)

private theorem leaf5935FlatSound : Sound leaf5935Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5935CertificateValid
    leaf5935InnerLogValid leaf5935CoversExact leaf5935LowerChecked

private noncomputable def leaf5936Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (101/256), chiHi := (51/128) }

private noncomputable def leaf5936Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871363/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68713000960) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1350941731/1073741824) }, upper := { exponent := 1, mantissa := (2605/2048) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi310LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429397501/137426001920) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf5936InnerLog : WideLogData :=
  innerPair293Data

set_option maxRecDepth 1000000 in
private theorem leaf5936LocalValidity :
    LeafFacts leaf5936Box leaf5936Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5936Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68713000960) }) = true
      norm_num [leaf5936Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5936CertificateValid :
    WideCertificateValid leaf5936Box leaf5936Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi310ValidityFacts
    leaf5936LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5936CoverageChecked :
    coverageCheck (innerAD leaf5936Box) leaf5936InnerLog = true := by
  rfl'

private theorem leaf5936InnerLogValid :
    leaf5936InnerLog.Valid 8 (innerAD leaf5936Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint90PositiveFacts.valid leaf5936CoverageChecked

private noncomputable def leaf5936InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629495/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5936InputLogOnePlusV_eq :
    leaf5936InputLogOnePlusV = outerEnclosure 24
      (leaf5936Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5936RoundedFacts : LeafRoundedFacts 8
    leaf5936Certificate.logOnePlusV leaf5936InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5936InputLogOnePlusV_eq }

private noncomputable def leaf5936Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi310InputQChi innerPair293Input
    leaf5936InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5936LowerChecked :
    lowerCheck 24 leaf5936Box leaf5936Inputs = true := by
  rfl'

private theorem leaf5936CoversExact : CoversExact 8
    leaf5936Box leaf5936Certificate leaf5936InnerLog leaf5936Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi310RoundedFacts
    innerPair293RoundedFacts leaf5936RoundedFacts (by rfl)

private theorem leaf5936FlatSound : Sound leaf5936Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5936CertificateValid
    leaf5936InnerLogValid leaf5936CoversExact leaf5936LowerChecked

private noncomputable def leaf5937Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (51/128), chiHi := (103/256) }

private noncomputable def leaf5937Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871363/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712990208) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1352317903/1073741824) }, upper := { exponent := 1, mantissa := (20861/16384) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi311LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429386749/137425980416) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf5937InnerLog : WideLogData :=
  innerPair293Data

set_option maxRecDepth 1000000 in
private theorem leaf5937LocalValidity :
    LeafFacts leaf5937Box leaf5937Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5937Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712990208) }) = true
      norm_num [leaf5937Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5937CertificateValid :
    WideCertificateValid leaf5937Box leaf5937Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi311ValidityFacts
    leaf5937LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5937CoverageChecked :
    coverageCheck (innerAD leaf5937Box) leaf5937InnerLog = true := by
  rfl'

private theorem leaf5937InnerLogValid :
    leaf5937InnerLog.Valid 8 (innerAD leaf5937Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint90PositiveFacts.valid leaf5937CoverageChecked

private noncomputable def leaf5937InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629497/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5937InputLogOnePlusV_eq :
    leaf5937InputLogOnePlusV = outerEnclosure 24
      (leaf5937Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5937RoundedFacts : LeafRoundedFacts 8
    leaf5937Certificate.logOnePlusV leaf5937InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5937InputLogOnePlusV_eq }

private noncomputable def leaf5937Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi311InputQChi innerPair293Input
    leaf5937InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5937LowerChecked :
    lowerCheck 24 leaf5937Box leaf5937Inputs = true := by
  rfl'

private theorem leaf5937CoversExact : CoversExact 8
    leaf5937Box leaf5937Certificate leaf5937InnerLog leaf5937Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi311RoundedFacts
    innerPair293RoundedFacts leaf5937RoundedFacts (by rfl)

private theorem leaf5937FlatSound : Sound leaf5937Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5937CertificateValid
    leaf5937InnerLogValid leaf5937CoversExact leaf5937LowerChecked

private noncomputable def leaf5938Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (103/256), chiHi := (13/32) }

private noncomputable def leaf5938Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871365/536870912) }, vSqrt := { lower := (8191/8192), upper := (4042140973/4041936896) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1360312805/1073741824) }, upper := { exponent := 1, mantissa := (2623/2048) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi312LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (8084077869/8083873792) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf5938InnerLog : WideLogData :=
  innerPair293Data

set_option maxRecDepth 1000000 in
private theorem leaf5938LocalValidity :
    LeafFacts leaf5938Box leaf5938Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5938Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4042140973/4041936896) }) = true
      norm_num [leaf5938Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5938CertificateValid :
    WideCertificateValid leaf5938Box leaf5938Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi312ValidityFacts
    leaf5938LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5938CoverageChecked :
    coverageCheck (innerAD leaf5938Box) leaf5938InnerLog = true := by
  rfl'

private theorem leaf5938InnerLogValid :
    leaf5938InnerLog.Valid 8 (innerAD leaf5938Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint90PositiveFacts.valid leaf5938CoverageChecked

private noncomputable def leaf5938InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (181711/262144) }

set_option maxRecDepth 1000000 in
private theorem leaf5938InputLogOnePlusV_eq :
    leaf5938InputLogOnePlusV = outerEnclosure 24
      (leaf5938Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5938RoundedFacts : LeafRoundedFacts 8
    leaf5938Certificate.logOnePlusV leaf5938InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5938InputLogOnePlusV_eq }

private noncomputable def leaf5938Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi312InputQChi innerPair293Input
    leaf5938InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5938LowerChecked :
    lowerCheck 24 leaf5938Box leaf5938Inputs = true := by
  rfl'

private theorem leaf5938CoversExact : CoversExact 8
    leaf5938Box leaf5938Certificate leaf5938InnerLog leaf5938Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi312RoundedFacts
    innerPair293RoundedFacts leaf5938RoundedFacts (by rfl)

private theorem leaf5938FlatSound : Sound leaf5938Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5938CertificateValid
    leaf5938InnerLogValid leaf5938CoversExact leaf5938LowerChecked

private noncomputable def leaf5939Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (51/128), chiHi := (103/256) }

private noncomputable def leaf5939Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871365/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712937472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1359002165/1073741824) }, upper := { exponent := 1, mantissa := (5241/4096) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi311LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429334013/137425874944) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf5939InnerLog : WideLogData :=
  innerPair293Data

set_option maxRecDepth 1000000 in
private theorem leaf5939LocalValidity :
    LeafFacts leaf5939Box leaf5939Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5939Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712937472) }) = true
      norm_num [leaf5939Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5939CertificateValid :
    WideCertificateValid leaf5939Box leaf5939Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi311ValidityFacts
    leaf5939LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5939CoverageChecked :
    coverageCheck (innerAD leaf5939Box) leaf5939InnerLog = true := by
  rfl'

private theorem leaf5939InnerLogValid :
    leaf5939InnerLog.Valid 8 (innerAD leaf5939Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint90PositiveFacts.valid leaf5939CoverageChecked

private noncomputable def leaf5939InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629503/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5939InputLogOnePlusV_eq :
    leaf5939InputLogOnePlusV = outerEnclosure 24
      (leaf5939Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5939RoundedFacts : LeafRoundedFacts 8
    leaf5939Certificate.logOnePlusV leaf5939InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5939InputLogOnePlusV_eq }

private noncomputable def leaf5939Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi311InputQChi innerPair293Input
    leaf5939InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5939LowerChecked :
    lowerCheck 24 leaf5939Box leaf5939Inputs = true := by
  rfl'

private theorem leaf5939CoversExact : CoversExact 8
    leaf5939Box leaf5939Certificate leaf5939InnerLog leaf5939Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi311RoundedFacts
    innerPair293RoundedFacts leaf5939RoundedFacts (by rfl)

private theorem leaf5939FlatSound : Sound leaf5939Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5939CertificateValid
    leaf5939InnerLogValid leaf5939CoversExact leaf5939LowerChecked

private noncomputable def leaf5940Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (103/256), chiHi := (13/32) }

private noncomputable def leaf5940Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871367/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712873984) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1367062599/1073741824) }, upper := { exponent := 1, mantissa := (659/512) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi312LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429270525/137425747968) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf5940InnerLog : WideLogData :=
  innerPair681Data

set_option maxRecDepth 1000000 in
private theorem leaf5940LocalValidity :
    LeafFacts leaf5940Box leaf5940Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5940Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712873984) }) = true
      norm_num [leaf5940Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5940CertificateValid :
    WideCertificateValid leaf5940Box leaf5940Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi312ValidityFacts
    leaf5940LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5940CoverageChecked :
    coverageCheck (innerAD leaf5940Box) leaf5940InnerLog = true := by
  rfl'

private theorem leaf5940InnerLogValid :
    leaf5940InnerLog.Valid 8 (innerAD leaf5940Box) :=
  wideLogDataValid_of_cachedCheck endpoint434PositiveFacts
    endpoint435PositiveFacts.valid leaf5940CoverageChecked

private noncomputable def leaf5940InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629511/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5940InputLogOnePlusV_eq :
    leaf5940InputLogOnePlusV = outerEnclosure 24
      (leaf5940Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5940RoundedFacts : LeafRoundedFacts 8
    leaf5940Certificate.logOnePlusV leaf5940InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5940InputLogOnePlusV_eq }

private noncomputable def leaf5940Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi312InputQChi innerPair681Input
    leaf5940InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5940LowerChecked :
    lowerCheck 24 leaf5940Box leaf5940Inputs = true := by
  rfl'

private theorem leaf5940CoversExact : CoversExact 8
    leaf5940Box leaf5940Certificate leaf5940InnerLog leaf5940Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi312RoundedFacts
    innerPair681RoundedFacts leaf5940RoundedFacts (by rfl)

private theorem leaf5940FlatSound : Sound leaf5940Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5940CertificateValid
    leaf5940InnerLogValid leaf5940CoversExact leaf5940LowerChecked

private noncomputable def leaf5941Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (3/8), chiHi := (97/256) }

private noncomputable def leaf5941Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871355/536870912) }, vSqrt := { lower := (8191/8192), upper := (158335127/158325504) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1316930631/1073741824) }, upper := { exponent := 1, mantissa := (20317/16384) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi305LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (316660631/316651008) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf5941InnerLog : WideLogData :=
  innerPair285Data

set_option maxRecDepth 1000000 in
private theorem leaf5941LocalValidity :
    LeafFacts leaf5941Box leaf5941Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5941Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (158335127/158325504) }) = true
      norm_num [leaf5941Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5941CertificateValid :
    WideCertificateValid leaf5941Box leaf5941Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi305ValidityFacts
    leaf5941LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5941CoverageChecked :
    coverageCheck (innerAD leaf5941Box) leaf5941InnerLog = true := by
  rfl'

private theorem leaf5941InnerLogValid :
    leaf5941InnerLog.Valid 8 (innerAD leaf5941Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint79PositiveFacts.valid leaf5941CoverageChecked

private noncomputable def leaf5941InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629591/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5941InputLogOnePlusV_eq :
    leaf5941InputLogOnePlusV = outerEnclosure 24
      (leaf5941Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5941RoundedFacts : LeafRoundedFacts 8
    leaf5941Certificate.logOnePlusV leaf5941InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5941InputLogOnePlusV_eq }

private noncomputable def leaf5941Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi305InputQChi innerPair285Input
    leaf5941InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5941LowerChecked :
    lowerCheck 24 leaf5941Box leaf5941Inputs = true := by
  rfl'

private theorem leaf5941CoversExact : CoversExact 8
    leaf5941Box leaf5941Certificate leaf5941InnerLog leaf5941Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi305RoundedFacts
    innerPair285RoundedFacts leaf5941RoundedFacts (by rfl)

private theorem leaf5941FlatSound : Sound leaf5941Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5941CertificateValid
    leaf5941InnerLogValid leaf5941CoversExact leaf5941LowerChecked

private noncomputable def leaf5942Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (97/256), chiHi := (49/128) }

private noncomputable def leaf5942Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871357/536870912) }, vSqrt := { lower := (8191/8192), upper := (967836571/967791616) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1325056597/1073741824) }, upper := { exponent := 1, mantissa := (10221/8192) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi306LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (1935628187/1935583232) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf5942InnerLog : WideLogData :=
  innerPair285Data

set_option maxRecDepth 1000000 in
private theorem leaf5942LocalValidity :
    LeafFacts leaf5942Box leaf5942Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5942Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (967836571/967791616) }) = true
      norm_num [leaf5942Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5942CertificateValid :
    WideCertificateValid leaf5942Box leaf5942Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi306ValidityFacts
    leaf5942LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5942CoverageChecked :
    coverageCheck (innerAD leaf5942Box) leaf5942InnerLog = true := by
  rfl'

private theorem leaf5942InnerLogValid :
    leaf5942InnerLog.Valid 8 (innerAD leaf5942Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint79PositiveFacts.valid leaf5942CoverageChecked

private noncomputable def leaf5942InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814735/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5942InputLogOnePlusV_eq :
    leaf5942InputLogOnePlusV = outerEnclosure 24
      (leaf5942Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5942RoundedFacts : LeafRoundedFacts 8
    leaf5942Certificate.logOnePlusV leaf5942InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5942InputLogOnePlusV_eq }

private noncomputable def leaf5942Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi306InputQChi innerPair285Input
    leaf5942InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5942LowerChecked :
    lowerCheck 24 leaf5942Box leaf5942Inputs = true := by
  rfl'

private theorem leaf5942CoversExact : CoversExact 8
    leaf5942Box leaf5942Certificate leaf5942InnerLog leaf5942Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi306RoundedFacts
    innerPair285RoundedFacts leaf5942RoundedFacts (by rfl)

private theorem leaf5942FlatSound : Sound leaf5942Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5942CertificateValid
    leaf5942InnerLogValid leaf5942CoversExact leaf5942LowerChecked

private noncomputable def leaf5943Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (3/8), chiHi := (97/256) }

private noncomputable def leaf5943Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871357/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68713219072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1323221701/1073741824) }, upper := { exponent := 1, mantissa := (10207/8192) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi305LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429615613/137426438144) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf5943InnerLog : WideLogData :=
  innerPair285Data

set_option maxRecDepth 1000000 in
private theorem leaf5943LocalValidity :
    LeafFacts leaf5943Box leaf5943Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5943Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68713219072) }) = true
      norm_num [leaf5943Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5943CertificateValid :
    WideCertificateValid leaf5943Box leaf5943Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi305ValidityFacts
    leaf5943LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5943CoverageChecked :
    coverageCheck (innerAD leaf5943Box) leaf5943InnerLog = true := by
  rfl'

private theorem leaf5943InnerLogValid :
    leaf5943InnerLog.Valid 8 (innerAD leaf5943Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint79PositiveFacts.valid leaf5943CoverageChecked

private noncomputable def leaf5943InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629469/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5943InputLogOnePlusV_eq :
    leaf5943InputLogOnePlusV = outerEnclosure 24
      (leaf5943Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5943RoundedFacts : LeafRoundedFacts 8
    leaf5943Certificate.logOnePlusV leaf5943InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5943InputLogOnePlusV_eq }

private noncomputable def leaf5943Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi305InputQChi innerPair285Input
    leaf5943InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5943LowerChecked :
    lowerCheck 24 leaf5943Box leaf5943Inputs = true := by
  rfl'

private theorem leaf5943CoversExact : CoversExact 8
    leaf5943Box leaf5943Certificate leaf5943InnerLog leaf5943Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi305RoundedFacts
    innerPair285RoundedFacts leaf5943RoundedFacts (by rfl)

private theorem leaf5943FlatSound : Sound leaf5943Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5943CertificateValid
    leaf5943InnerLogValid leaf5943CoversExact leaf5943LowerChecked

private noncomputable def leaf5944Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (97/256), chiHi := (49/128) }

private noncomputable def leaf5944Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871359/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68713154560) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1331413199/1073741824) }, upper := { exponent := 1, mantissa := (5135/4096) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi306LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429551101/137426309120) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf5944InnerLog : WideLogData :=
  innerPair362Data

set_option maxRecDepth 1000000 in
private theorem leaf5944LocalValidity :
    LeafFacts leaf5944Box leaf5944Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5944Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68713154560) }) = true
      norm_num [leaf5944Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5944CertificateValid :
    WideCertificateValid leaf5944Box leaf5944Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi306ValidityFacts
    leaf5944LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5944CoverageChecked :
    coverageCheck (innerAD leaf5944Box) leaf5944InnerLog = true := by
  rfl'

private theorem leaf5944InnerLogValid :
    leaf5944InnerLog.Valid 8 (innerAD leaf5944Box) :=
  wideLogDataValid_of_cachedCheck endpoint94PositiveFacts
    endpoint419PositiveFacts.valid leaf5944CoverageChecked

private noncomputable def leaf5944InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629477/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5944InputLogOnePlusV_eq :
    leaf5944InputLogOnePlusV = outerEnclosure 24
      (leaf5944Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5944RoundedFacts : LeafRoundedFacts 8
    leaf5944Certificate.logOnePlusV leaf5944InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5944InputLogOnePlusV_eq }

private noncomputable def leaf5944Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi306InputQChi innerPair362Input
    leaf5944InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5944LowerChecked :
    lowerCheck 24 leaf5944Box leaf5944Inputs = true := by
  rfl'

private theorem leaf5944CoversExact : CoversExact 8
    leaf5944Box leaf5944Certificate leaf5944InnerLog leaf5944Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi306RoundedFacts
    innerPair362RoundedFacts leaf5944RoundedFacts (by rfl)

private theorem leaf5944FlatSound : Sound leaf5944Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5944CertificateValid
    leaf5944InnerLogValid leaf5944CoversExact leaf5944LowerChecked

private noncomputable def leaf5945Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (49/128), chiHi := (99/256) }

private noncomputable def leaf5945Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871359/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68713140736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1333182563/1073741824) }, upper := { exponent := 1, mantissa := (20567/16384) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi307LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429537277/137426281472) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf5945InnerLog : WideLogData :=
  innerPair362Data

set_option maxRecDepth 1000000 in
private theorem leaf5945LocalValidity :
    LeafFacts leaf5945Box leaf5945Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5945Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68713140736) }) = true
      norm_num [leaf5945Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5945CertificateValid :
    WideCertificateValid leaf5945Box leaf5945Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi307ValidityFacts
    leaf5945LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5945CoverageChecked :
    coverageCheck (innerAD leaf5945Box) leaf5945InnerLog = true := by
  rfl'

private theorem leaf5945InnerLogValid :
    leaf5945InnerLog.Valid 8 (innerAD leaf5945Box) :=
  wideLogDataValid_of_cachedCheck endpoint94PositiveFacts
    endpoint419PositiveFacts.valid leaf5945CoverageChecked

private noncomputable def leaf5945InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814739/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5945InputLogOnePlusV_eq :
    leaf5945InputLogOnePlusV = outerEnclosure 24
      (leaf5945Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5945RoundedFacts : LeafRoundedFacts 8
    leaf5945Certificate.logOnePlusV leaf5945InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5945InputLogOnePlusV_eq }

private noncomputable def leaf5945Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi307InputQChi innerPair362Input
    leaf5945InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5945LowerChecked :
    lowerCheck 24 leaf5945Box leaf5945Inputs = true := by
  rfl'

private theorem leaf5945CoversExact : CoversExact 8
    leaf5945Box leaf5945Certificate leaf5945InnerLog leaf5945Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi307RoundedFacts
    innerPair362RoundedFacts leaf5945RoundedFacts (by rfl)

private theorem leaf5945FlatSound : Sound leaf5945Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5945CertificateValid
    leaf5945InnerLogValid leaf5945CoversExact leaf5945LowerChecked

private noncomputable def leaf5946Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (99/256), chiHi := (25/64) }

private noncomputable def leaf5946Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871361/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68713076736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1341308529/1073741824) }, upper := { exponent := 1, mantissa := (5173/4096) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi308LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429473277/137426153472) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf5946InnerLog : WideLogData :=
  innerPair668Data

set_option maxRecDepth 1000000 in
private theorem leaf5946LocalValidity :
    LeafFacts leaf5946Box leaf5946Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5946Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68713076736) }) = true
      norm_num [leaf5946Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5946CertificateValid :
    WideCertificateValid leaf5946Box leaf5946Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi308ValidityFacts
    leaf5946LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5946CoverageChecked :
    coverageCheck (innerAD leaf5946Box) leaf5946InnerLog = true := by
  rfl'

private theorem leaf5946InnerLogValid :
    leaf5946InnerLog.Valid 8 (innerAD leaf5946Box) :=
  wideLogDataValid_of_cachedCheck endpoint414PositiveFacts
    endpoint434PositiveFacts.valid leaf5946CoverageChecked

private noncomputable def leaf5946InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814743/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5946InputLogOnePlusV_eq :
    leaf5946InputLogOnePlusV = outerEnclosure 24
      (leaf5946Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5946RoundedFacts : LeafRoundedFacts 8
    leaf5946Certificate.logOnePlusV leaf5946InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5946InputLogOnePlusV_eq }

private noncomputable def leaf5946Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi308InputQChi innerPair668Input
    leaf5946InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5946LowerChecked :
    lowerCheck 24 leaf5946Box leaf5946Inputs = true := by
  rfl'

private theorem leaf5946CoversExact : CoversExact 8
    leaf5946Box leaf5946Certificate leaf5946InnerLog leaf5946Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi308RoundedFacts
    innerPair668RoundedFacts leaf5946RoundedFacts (by rfl)

private theorem leaf5946FlatSound : Sound leaf5946Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5946CertificateValid
    leaf5946InnerLogValid leaf5946CoversExact leaf5946LowerChecked

private noncomputable def leaf5947Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (49/128), chiHi := (99/256) }

private noncomputable def leaf5947Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871361/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68713090048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1339604697/1073741824) }, upper := { exponent := 1, mantissa := (10333/8192) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi307LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429486589/137426180096) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf5947InnerLog : WideLogData :=
  innerPair668Data

set_option maxRecDepth 1000000 in
private theorem leaf5947LocalValidity :
    LeafFacts leaf5947Box leaf5947Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5947Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68713090048) }) = true
      norm_num [leaf5947Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5947CertificateValid :
    WideCertificateValid leaf5947Box leaf5947Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi307ValidityFacts
    leaf5947LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5947CoverageChecked :
    coverageCheck (innerAD leaf5947Box) leaf5947InnerLog = true := by
  rfl'

private theorem leaf5947InnerLogValid :
    leaf5947InnerLog.Valid 8 (innerAD leaf5947Box) :=
  wideLogDataValid_of_cachedCheck endpoint414PositiveFacts
    endpoint434PositiveFacts.valid leaf5947CoverageChecked

private noncomputable def leaf5947InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907371/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5947InputLogOnePlusV_eq :
    leaf5947InputLogOnePlusV = outerEnclosure 24
      (leaf5947Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5947RoundedFacts : LeafRoundedFacts 8
    leaf5947Certificate.logOnePlusV leaf5947InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5947InputLogOnePlusV_eq }

private noncomputable def leaf5947Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi307InputQChi innerPair668Input
    leaf5947InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5947LowerChecked :
    lowerCheck 24 leaf5947Box leaf5947Inputs = true := by
  rfl'

private theorem leaf5947CoversExact : CoversExact 8
    leaf5947Box leaf5947Certificate leaf5947InnerLog leaf5947Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi307RoundedFacts
    innerPair668RoundedFacts leaf5947RoundedFacts (by rfl)

private theorem leaf5947FlatSound : Sound leaf5947Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5947CertificateValid
    leaf5947InnerLogValid leaf5947CoversExact leaf5947LowerChecked

private noncomputable def leaf5948Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (99/256), chiHi := (25/64) }

private noncomputable def leaf5948Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871363/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68713025536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1347796195/1073741824) }, upper := { exponent := 1, mantissa := (2599/2048) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi308LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429422077/137426051072) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf5948InnerLog : WideLogData :=
  innerPair293Data

set_option maxRecDepth 1000000 in
private theorem leaf5948LocalValidity :
    LeafFacts leaf5948Box leaf5948Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5948Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68713025536) }) = true
      norm_num [leaf5948Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5948CertificateValid :
    WideCertificateValid leaf5948Box leaf5948Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi308ValidityFacts
    leaf5948LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5948CoverageChecked :
    coverageCheck (innerAD leaf5948Box) leaf5948InnerLog = true := by
  rfl'

private theorem leaf5948InnerLogValid :
    leaf5948InnerLog.Valid 8 (innerAD leaf5948Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint90PositiveFacts.valid leaf5948CoverageChecked

private noncomputable def leaf5948InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907373/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5948InputLogOnePlusV_eq :
    leaf5948InputLogOnePlusV = outerEnclosure 24
      (leaf5948Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5948RoundedFacts : LeafRoundedFacts 8
    leaf5948Certificate.logOnePlusV leaf5948InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5948InputLogOnePlusV_eq }

private noncomputable def leaf5948Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi308InputQChi innerPair293Input
    leaf5948InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5948LowerChecked :
    lowerCheck 24 leaf5948Box leaf5948Inputs = true := by
  rfl'

private theorem leaf5948CoversExact : CoversExact 8
    leaf5948Box leaf5948Certificate leaf5948InnerLog leaf5948Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi308RoundedFacts
    innerPair293RoundedFacts leaf5948RoundedFacts (by rfl)

private theorem leaf5948FlatSound : Sound leaf5948Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5948CertificateValid
    leaf5948InnerLogValid leaf5948CoversExact leaf5948LowerChecked

private noncomputable def leaf5949Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (3/8), chiHi := (97/256) }

private noncomputable def leaf5949Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871359/536870912) }, vSqrt := { lower := (8191/8192), upper := (5285876657/5285628416) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1329512771/1073741824) }, upper := { exponent := 1, mantissa := (20511/16384) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi305LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (10571505073/10571256832) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf5949InnerLog : WideLogData :=
  innerPair362Data

set_option maxRecDepth 1000000 in
private theorem leaf5949LocalValidity :
    LeafFacts leaf5949Box leaf5949Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5949Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5285876657/5285628416) }) = true
      norm_num [leaf5949Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5949CertificateValid :
    WideCertificateValid leaf5949Box leaf5949Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi305ValidityFacts
    leaf5949LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5949CoverageChecked :
    coverageCheck (innerAD leaf5949Box) leaf5949InnerLog = true := by
  rfl'

private theorem leaf5949InnerLogValid :
    leaf5949InnerLog.Valid 8 (innerAD leaf5949Box) :=
  wideLogDataValid_of_cachedCheck endpoint94PositiveFacts
    endpoint419PositiveFacts.valid leaf5949CoverageChecked

private noncomputable def leaf5949InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629475/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5949InputLogOnePlusV_eq :
    leaf5949InputLogOnePlusV = outerEnclosure 24
      (leaf5949Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5949RoundedFacts : LeafRoundedFacts 8
    leaf5949Certificate.logOnePlusV leaf5949InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5949InputLogOnePlusV_eq }

private noncomputable def leaf5949Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi305InputQChi innerPair362Input
    leaf5949InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5949LowerChecked :
    lowerCheck 24 leaf5949Box leaf5949Inputs = true := by
  rfl'

private theorem leaf5949CoversExact : CoversExact 8
    leaf5949Box leaf5949Certificate leaf5949InnerLog leaf5949Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi305RoundedFacts
    innerPair362RoundedFacts leaf5949RoundedFacts (by rfl)

private theorem leaf5949FlatSound : Sound leaf5949Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5949CertificateValid
    leaf5949InnerLogValid leaf5949CoversExact leaf5949LowerChecked

private noncomputable def leaf5950Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (97/256), chiHi := (49/128) }

private noncomputable def leaf5950Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871361/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68713104384) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1337769801/1073741824) }, upper := { exponent := 1, mantissa := (10319/8192) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi306LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429500925/137426208768) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf5950InnerLog : WideLogData :=
  innerPair668Data

set_option maxRecDepth 1000000 in
private theorem leaf5950LocalValidity :
    LeafFacts leaf5950Box leaf5950Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5950Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68713104384) }) = true
      norm_num [leaf5950Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5950CertificateValid :
    WideCertificateValid leaf5950Box leaf5950Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi306ValidityFacts
    leaf5950LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5950CoverageChecked :
    coverageCheck (innerAD leaf5950Box) leaf5950InnerLog = true := by
  rfl'

private theorem leaf5950InnerLogValid :
    leaf5950InnerLog.Valid 8 (innerAD leaf5950Box) :=
  wideLogDataValid_of_cachedCheck endpoint414PositiveFacts
    endpoint434PositiveFacts.valid leaf5950CoverageChecked

private noncomputable def leaf5950InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629483/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5950InputLogOnePlusV_eq :
    leaf5950InputLogOnePlusV = outerEnclosure 24
      (leaf5950Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5950RoundedFacts : LeafRoundedFacts 8
    leaf5950Certificate.logOnePlusV leaf5950InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5950InputLogOnePlusV_eq }

private noncomputable def leaf5950Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi306InputQChi innerPair668Input
    leaf5950InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5950LowerChecked :
    lowerCheck 24 leaf5950Box leaf5950Inputs = true := by
  rfl'

private theorem leaf5950CoversExact : CoversExact 8
    leaf5950Box leaf5950Certificate leaf5950InnerLog leaf5950Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi306RoundedFacts
    innerPair668RoundedFacts leaf5950RoundedFacts (by rfl)

private theorem leaf5950FlatSound : Sound leaf5950Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5950CertificateValid
    leaf5950InnerLogValid leaf5950CoversExact leaf5950LowerChecked

private noncomputable def leaf5951Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (3/8), chiHi := (97/256) }

private noncomputable def leaf5951Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871361/536870912) }, vSqrt := { lower := (65527/65536), upper := (68716396541/68713119744) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1335803841/1073741824) }, upper := { exponent := 1, mantissa := (161/128) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi305LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (137429516285/137426239488) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf5951InnerLog : WideLogData :=
  innerPair667Data

set_option maxRecDepth 1000000 in
private theorem leaf5951LocalValidity :
    LeafFacts leaf5951Box leaf5951Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5951Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (68716396541/68713119744) }) = true
      norm_num [leaf5951Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5951CertificateValid :
    WideCertificateValid leaf5951Box leaf5951Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi305ValidityFacts
    leaf5951LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5951CoverageChecked :
    coverageCheck (innerAD leaf5951Box) leaf5951InnerLog = true := by
  rfl'

private theorem leaf5951InnerLogValid :
    leaf5951InnerLog.Valid 8 (innerAD leaf5951Box) :=
  wideLogDataValid_of_cachedCheck endpoint414PositiveFacts
    endpoint419PositiveFacts.valid leaf5951CoverageChecked

private noncomputable def leaf5951InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629481/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5951InputLogOnePlusV_eq :
    leaf5951InputLogOnePlusV = outerEnclosure 24
      (leaf5951Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5951RoundedFacts : LeafRoundedFacts 8
    leaf5951Certificate.logOnePlusV leaf5951InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5951InputLogOnePlusV_eq }

private noncomputable def leaf5951Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi305InputQChi innerPair667Input
    leaf5951InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5951LowerChecked :
    lowerCheck 24 leaf5951Box leaf5951Inputs = true := by
  rfl'

private theorem leaf5951CoversExact : CoversExact 8
    leaf5951Box leaf5951Certificate leaf5951InnerLog leaf5951Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi305RoundedFacts
    innerPair667RoundedFacts leaf5951RoundedFacts (by rfl)

private theorem leaf5951FlatSound : Sound leaf5951Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5951CertificateValid
    leaf5951InnerLogValid leaf5951CoversExact leaf5951LowerChecked

private noncomputable def leaf5952Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (97/256), chiHi := (49/128) }

private noncomputable def leaf5952Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871363/536870912) }, vSqrt := { lower := (65527/65536), upper := (68716396541/68713054208) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1344126403/1073741824) }, upper := { exponent := 1, mantissa := (81/64) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi306LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (137429450749/137426108416) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf5952InnerLog : WideLogData :=
  innerPair297Data

set_option maxRecDepth 1000000 in
private theorem leaf5952LocalValidity :
    LeafFacts leaf5952Box leaf5952Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5952Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (68716396541/68713054208) }) = true
      norm_num [leaf5952Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5952CertificateValid :
    WideCertificateValid leaf5952Box leaf5952Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi306ValidityFacts
    leaf5952LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5952CoverageChecked :
    coverageCheck (innerAD leaf5952Box) leaf5952InnerLog = true := by
  rfl'

private theorem leaf5952InnerLogValid :
    leaf5952InnerLog.Valid 8 (innerAD leaf5952Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint434PositiveFacts.valid leaf5952CoverageChecked

private noncomputable def leaf5952InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629489/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5952InputLogOnePlusV_eq :
    leaf5952InputLogOnePlusV = outerEnclosure 24
      (leaf5952Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5952RoundedFacts : LeafRoundedFacts 8
    leaf5952Certificate.logOnePlusV leaf5952InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5952InputLogOnePlusV_eq }

private noncomputable def leaf5952Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi306InputQChi innerPair297Input
    leaf5952InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5952LowerChecked :
    lowerCheck 24 leaf5952Box leaf5952Inputs = true := by
  rfl'

private theorem leaf5952CoversExact : CoversExact 8
    leaf5952Box leaf5952Certificate leaf5952InnerLog leaf5952Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi306RoundedFacts
    innerPair297RoundedFacts leaf5952RoundedFacts (by rfl)

private theorem leaf5952FlatSound : Sound leaf5952Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5952CertificateValid
    leaf5952InnerLogValid leaf5952CoversExact leaf5952LowerChecked

private noncomputable def leaf5953Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (49/128), chiHi := (99/256) }

private noncomputable def leaf5953Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871363/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68713039360) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1346026831/1073741824) }, upper := { exponent := 1, mantissa := (20765/16384) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi307LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429435901/137426078720) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf5953InnerLog : WideLogData :=
  innerPair299Data

set_option maxRecDepth 1000000 in
private theorem leaf5953LocalValidity :
    LeafFacts leaf5953Box leaf5953Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5953Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68713039360) }) = true
      norm_num [leaf5953Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5953CertificateValid :
    WideCertificateValid leaf5953Box leaf5953Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi307ValidityFacts
    leaf5953LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5953CoverageChecked :
    coverageCheck (innerAD leaf5953Box) leaf5953InnerLog = true := by
  rfl'

private theorem leaf5953InnerLogValid :
    leaf5953InnerLog.Valid 8 (innerAD leaf5953Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint437PositiveFacts.valid leaf5953CoverageChecked

private noncomputable def leaf5953InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629491/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5953InputLogOnePlusV_eq :
    leaf5953InputLogOnePlusV = outerEnclosure 24
      (leaf5953Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5953RoundedFacts : LeafRoundedFacts 8
    leaf5953Certificate.logOnePlusV leaf5953InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5953InputLogOnePlusV_eq }

private noncomputable def leaf5953Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi307InputQChi innerPair299Input
    leaf5953InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5953LowerChecked :
    lowerCheck 24 leaf5953Box leaf5953Inputs = true := by
  rfl'

private theorem leaf5953CoversExact : CoversExact 8
    leaf5953Box leaf5953Certificate leaf5953InnerLog leaf5953Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi307RoundedFacts
    innerPair299RoundedFacts leaf5953RoundedFacts (by rfl)

private theorem leaf5953FlatSound : Sound leaf5953Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5953CertificateValid
    leaf5953InnerLogValid leaf5953CoversExact leaf5953LowerChecked

private noncomputable def leaf5954Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (99/256), chiHi := (25/64) }

private noncomputable def leaf5954Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871365/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712974336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1354283861/1073741824) }, upper := { exponent := 1, mantissa := (5223/4096) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi308LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429370877/137425948672) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf5954InnerLog : WideLogData :=
  innerPair293Data

set_option maxRecDepth 1000000 in
private theorem leaf5954LocalValidity :
    LeafFacts leaf5954Box leaf5954Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5954Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712974336) }) = true
      norm_num [leaf5954Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5954CertificateValid :
    WideCertificateValid leaf5954Box leaf5954Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi308ValidityFacts
    leaf5954LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5954CoverageChecked :
    coverageCheck (innerAD leaf5954Box) leaf5954InnerLog = true := by
  rfl'

private theorem leaf5954InnerLogValid :
    leaf5954InnerLog.Valid 8 (innerAD leaf5954Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint90PositiveFacts.valid leaf5954CoverageChecked

private noncomputable def leaf5954InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629499/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5954InputLogOnePlusV_eq :
    leaf5954InputLogOnePlusV = outerEnclosure 24
      (leaf5954Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5954RoundedFacts : LeafRoundedFacts 8
    leaf5954Certificate.logOnePlusV leaf5954InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5954InputLogOnePlusV_eq }

private noncomputable def leaf5954Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi308InputQChi innerPair293Input
    leaf5954InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5954LowerChecked :
    lowerCheck 24 leaf5954Box leaf5954Inputs = true := by
  rfl'

private theorem leaf5954CoversExact : CoversExact 8
    leaf5954Box leaf5954Certificate leaf5954InnerLog leaf5954Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi308RoundedFacts
    innerPair293RoundedFacts leaf5954RoundedFacts (by rfl)

private theorem leaf5954FlatSound : Sound leaf5954Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5954CertificateValid
    leaf5954InnerLogValid leaf5954CoversExact leaf5954LowerChecked

private noncomputable def leaf5955Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (49/128), chiHi := (99/256) }

private noncomputable def leaf5955Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871365/536870912) }, vSqrt := { lower := (65527/65536), upper := (68716396541/68712988672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1352448965/1073741824) }, upper := { exponent := 1, mantissa := (163/128) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi307LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (137429385213/137425977344) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf5955InnerLog : WideLogData :=
  innerPair293Data

set_option maxRecDepth 1000000 in
private theorem leaf5955LocalValidity :
    LeafFacts leaf5955Box leaf5955Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5955Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (68716396541/68712988672) }) = true
      norm_num [leaf5955Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5955CertificateValid :
    WideCertificateValid leaf5955Box leaf5955Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi307ValidityFacts
    leaf5955LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5955CoverageChecked :
    coverageCheck (innerAD leaf5955Box) leaf5955InnerLog = true := by
  rfl'

private theorem leaf5955InnerLogValid :
    leaf5955InnerLog.Valid 8 (innerAD leaf5955Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint90PositiveFacts.valid leaf5955CoverageChecked

private noncomputable def leaf5955InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629497/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5955InputLogOnePlusV_eq :
    leaf5955InputLogOnePlusV = outerEnclosure 24
      (leaf5955Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5955RoundedFacts : LeafRoundedFacts 8
    leaf5955Certificate.logOnePlusV leaf5955InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5955InputLogOnePlusV_eq }

private noncomputable def leaf5955Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi307InputQChi innerPair293Input
    leaf5955InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5955LowerChecked :
    lowerCheck 24 leaf5955Box leaf5955Inputs = true := by
  rfl'

private theorem leaf5955CoversExact : CoversExact 8
    leaf5955Box leaf5955Certificate leaf5955InnerLog leaf5955Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi307RoundedFacts
    innerPair293RoundedFacts leaf5955RoundedFacts (by rfl)

private theorem leaf5955FlatSound : Sound leaf5955Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5955CertificateValid
    leaf5955InnerLogValid leaf5955CoversExact leaf5955LowerChecked

private noncomputable def leaf5956Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (99/256), chiHi := (25/64) }

private noncomputable def leaf5956Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871367/536870912) }, vSqrt := { lower := (65527/65536), upper := (5285876657/5285609472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1360771527/1073741824) }, upper := { exponent := 1, mantissa := (41/32) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi308LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (10571486129/10571218944) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf5956InnerLog : WideLogData :=
  innerPair293Data

set_option maxRecDepth 1000000 in
private theorem leaf5956LocalValidity :
    LeafFacts leaf5956Box leaf5956Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5956Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (5285876657/5285609472) }) = true
      norm_num [leaf5956Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5956CertificateValid :
    WideCertificateValid leaf5956Box leaf5956Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi308ValidityFacts
    leaf5956LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5956CoverageChecked :
    coverageCheck (innerAD leaf5956Box) leaf5956InnerLog = true := by
  rfl'

private theorem leaf5956InnerLogValid :
    leaf5956InnerLog.Valid 8 (innerAD leaf5956Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint90PositiveFacts.valid leaf5956CoverageChecked

private noncomputable def leaf5956InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629505/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5956InputLogOnePlusV_eq :
    leaf5956InputLogOnePlusV = outerEnclosure 24
      (leaf5956Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5956RoundedFacts : LeafRoundedFacts 8
    leaf5956Certificate.logOnePlusV leaf5956InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5956InputLogOnePlusV_eq }

private noncomputable def leaf5956Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi308InputQChi innerPair293Input
    leaf5956InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5956LowerChecked :
    lowerCheck 24 leaf5956Box leaf5956Inputs = true := by
  rfl'

private theorem leaf5956CoversExact : CoversExact 8
    leaf5956Box leaf5956Certificate leaf5956InnerLog leaf5956Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi308RoundedFacts
    innerPair293RoundedFacts leaf5956RoundedFacts (by rfl)

private theorem leaf5956FlatSound : Sound leaf5956Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5956CertificateValid
    leaf5956InnerLogValid leaf5956CoversExact leaf5956LowerChecked

private noncomputable def leaf5957Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (25/64), chiHi := (101/256) }

private noncomputable def leaf5957Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871363/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68713012736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1349434495/1073741824) }, upper := { exponent := 1, mantissa := (20817/16384) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi309LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429409277/137426025472) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf5957InnerLog : WideLogData :=
  innerPair293Data

set_option maxRecDepth 1000000 in
private theorem leaf5957LocalValidity :
    LeafFacts leaf5957Box leaf5957Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5957Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68713012736) }) = true
      norm_num [leaf5957Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5957CertificateValid :
    WideCertificateValid leaf5957Box leaf5957Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi309ValidityFacts
    leaf5957LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5957CoverageChecked :
    coverageCheck (innerAD leaf5957Box) leaf5957InnerLog = true := by
  rfl'

private theorem leaf5957InnerLogValid :
    leaf5957InnerLog.Valid 8 (innerAD leaf5957Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint90PositiveFacts.valid leaf5957CoverageChecked

private noncomputable def leaf5957InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814747/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5957InputLogOnePlusV_eq :
    leaf5957InputLogOnePlusV = outerEnclosure 24
      (leaf5957Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5957RoundedFacts : LeafRoundedFacts 8
    leaf5957Certificate.logOnePlusV leaf5957InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5957InputLogOnePlusV_eq }

private noncomputable def leaf5957Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi309InputQChi innerPair293Input
    leaf5957InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5957LowerChecked :
    lowerCheck 24 leaf5957Box leaf5957Inputs = true := by
  rfl'

private theorem leaf5957CoversExact : CoversExact 8
    leaf5957Box leaf5957Certificate leaf5957InnerLog leaf5957Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi309RoundedFacts
    innerPair293RoundedFacts leaf5957RoundedFacts (by rfl)

private theorem leaf5957FlatSound : Sound leaf5957Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5957CertificateValid
    leaf5957InnerLogValid leaf5957CoversExact leaf5957LowerChecked

private noncomputable def leaf5958Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (101/256), chiHi := (51/128) }

private noncomputable def leaf5958Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871365/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712948736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1357560461/1073741824) }, upper := { exponent := 1, mantissa := (10471/8192) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi310LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429345277/137425897472) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf5958InnerLog : WideLogData :=
  innerPair293Data

set_option maxRecDepth 1000000 in
private theorem leaf5958LocalValidity :
    LeafFacts leaf5958Box leaf5958Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5958Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712948736) }) = true
      norm_num [leaf5958Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5958CertificateValid :
    WideCertificateValid leaf5958Box leaf5958Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi310ValidityFacts
    leaf5958LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5958CoverageChecked :
    coverageCheck (innerAD leaf5958Box) leaf5958InnerLog = true := by
  rfl'

private theorem leaf5958InnerLogValid :
    leaf5958InnerLog.Valid 8 (innerAD leaf5958Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint90PositiveFacts.valid leaf5958CoverageChecked

private noncomputable def leaf5958InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814751/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5958InputLogOnePlusV_eq :
    leaf5958InputLogOnePlusV = outerEnclosure 24
      (leaf5958Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5958RoundedFacts : LeafRoundedFacts 8
    leaf5958Certificate.logOnePlusV leaf5958InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5958InputLogOnePlusV_eq }

private noncomputable def leaf5958Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi310InputQChi innerPair293Input
    leaf5958InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5958LowerChecked :
    lowerCheck 24 leaf5958Box leaf5958Inputs = true := by
  rfl'

private theorem leaf5958CoversExact : CoversExact 8
    leaf5958Box leaf5958Certificate leaf5958InnerLog leaf5958Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi310RoundedFacts
    innerPair293RoundedFacts leaf5958RoundedFacts (by rfl)

private theorem leaf5958FlatSound : Sound leaf5958Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5958CertificateValid
    leaf5958InnerLogValid leaf5958CoversExact leaf5958LowerChecked

private noncomputable def leaf5959Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (25/64), chiHi := (101/256) }

private noncomputable def leaf5959Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871365/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712961024) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1355987693/1073741824) }, upper := { exponent := 1, mantissa := (10459/8192) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi309LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429357565/137425922048) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf5959InnerLog : WideLogData :=
  innerPair293Data

set_option maxRecDepth 1000000 in
private theorem leaf5959LocalValidity :
    LeafFacts leaf5959Box leaf5959Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5959Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712961024) }) = true
      norm_num [leaf5959Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5959CertificateValid :
    WideCertificateValid leaf5959Box leaf5959Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi309ValidityFacts
    leaf5959LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5959CoverageChecked :
    coverageCheck (innerAD leaf5959Box) leaf5959InnerLog = true := by
  rfl'

private theorem leaf5959InnerLogValid :
    leaf5959InnerLog.Valid 8 (innerAD leaf5959Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint90PositiveFacts.valid leaf5959CoverageChecked

private noncomputable def leaf5959InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907375/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5959InputLogOnePlusV_eq :
    leaf5959InputLogOnePlusV = outerEnclosure 24
      (leaf5959Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5959RoundedFacts : LeafRoundedFacts 8
    leaf5959Certificate.logOnePlusV leaf5959InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5959InputLogOnePlusV_eq }

private noncomputable def leaf5959Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi309InputQChi innerPair293Input
    leaf5959InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5959LowerChecked :
    lowerCheck 24 leaf5959Box leaf5959Inputs = true := by
  rfl'

private theorem leaf5959CoversExact : CoversExact 8
    leaf5959Box leaf5959Certificate leaf5959InnerLog leaf5959Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi309RoundedFacts
    innerPair293RoundedFacts leaf5959RoundedFacts (by rfl)

private theorem leaf5959FlatSound : Sound leaf5959Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5959CertificateValid
    leaf5959InnerLogValid leaf5959CoversExact leaf5959LowerChecked

private noncomputable def leaf5960Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (101/256), chiHi := (51/128) }

private noncomputable def leaf5960Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871367/536870912) }, vSqrt := { lower := (8191/8192), upper := (5285876657/5285607424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1364179191/1073741824) }, upper := { exponent := 1, mantissa := (5261/4096) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi310LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (10571484081/10571214848) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf5960InnerLog : WideLogData :=
  innerPair681Data

set_option maxRecDepth 1000000 in
private theorem leaf5960LocalValidity :
    LeafFacts leaf5960Box leaf5960Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5960Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5285876657/5285607424) }) = true
      norm_num [leaf5960Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5960CertificateValid :
    WideCertificateValid leaf5960Box leaf5960Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi310ValidityFacts
    leaf5960LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5960CoverageChecked :
    coverageCheck (innerAD leaf5960Box) leaf5960InnerLog = true := by
  rfl'

private theorem leaf5960InnerLogValid :
    leaf5960InnerLog.Valid 8 (innerAD leaf5960Box) :=
  wideLogDataValid_of_cachedCheck endpoint434PositiveFacts
    endpoint435PositiveFacts.valid leaf5960CoverageChecked

private noncomputable def leaf5960InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907377/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5960InputLogOnePlusV_eq :
    leaf5960InputLogOnePlusV = outerEnclosure 24
      (leaf5960Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5960RoundedFacts : LeafRoundedFacts 8
    leaf5960Certificate.logOnePlusV leaf5960InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5960InputLogOnePlusV_eq }

private noncomputable def leaf5960Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi310InputQChi innerPair681Input
    leaf5960InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5960LowerChecked :
    lowerCheck 24 leaf5960Box leaf5960Inputs = true := by
  rfl'

private theorem leaf5960CoversExact : CoversExact 8
    leaf5960Box leaf5960Certificate leaf5960InnerLog leaf5960Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi310RoundedFacts
    innerPair681RoundedFacts leaf5960RoundedFacts (by rfl)

private theorem leaf5960FlatSound : Sound leaf5960Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5960CertificateValid
    leaf5960InnerLogValid leaf5960CoversExact leaf5960LowerChecked

private noncomputable def leaf5961Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (51/128), chiHi := (103/256) }

private noncomputable def leaf5961Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871367/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712884736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1365686427/1073741824) }, upper := { exponent := 1, mantissa := (21067/16384) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi311LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429281277/137425769472) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf5961InnerLog : WideLogData :=
  innerPair681Data

set_option maxRecDepth 1000000 in
private theorem leaf5961LocalValidity :
    LeafFacts leaf5961Box leaf5961Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5961Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712884736) }) = true
      norm_num [leaf5961Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5961CertificateValid :
    WideCertificateValid leaf5961Box leaf5961Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi311ValidityFacts
    leaf5961LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5961CoverageChecked :
    coverageCheck (innerAD leaf5961Box) leaf5961InnerLog = true := by
  rfl'

private theorem leaf5961InnerLogValid :
    leaf5961InnerLog.Valid 8 (innerAD leaf5961Box) :=
  wideLogDataValid_of_cachedCheck endpoint434PositiveFacts
    endpoint435PositiveFacts.valid leaf5961CoverageChecked

private noncomputable def leaf5961InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629509/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5961InputLogOnePlusV_eq :
    leaf5961InputLogOnePlusV = outerEnclosure 24
      (leaf5961Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5961RoundedFacts : LeafRoundedFacts 8
    leaf5961Certificate.logOnePlusV leaf5961InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5961InputLogOnePlusV_eq }

private noncomputable def leaf5961Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi311InputQChi innerPair681Input
    leaf5961InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5961LowerChecked :
    lowerCheck 24 leaf5961Box leaf5961Inputs = true := by
  rfl'

private theorem leaf5961CoversExact : CoversExact 8
    leaf5961Box leaf5961Certificate leaf5961InnerLog leaf5961Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi311RoundedFacts
    innerPair681RoundedFacts leaf5961RoundedFacts (by rfl)

private theorem leaf5961FlatSound : Sound leaf5961Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5961CertificateValid
    leaf5961InnerLogValid leaf5961CoversExact leaf5961LowerChecked

private noncomputable def leaf5962Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (103/256), chiHi := (13/32) }

private noncomputable def leaf5962Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871369/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712820736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1373812393/1073741824) }, upper := { exponent := 1, mantissa := (2649/2048) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi312LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429217277/137425641472) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf5962InnerLog : WideLogData :=
  innerPair294Data

set_option maxRecDepth 1000000 in
private theorem leaf5962LocalValidity :
    LeafFacts leaf5962Box leaf5962Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5962Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712820736) }) = true
      norm_num [leaf5962Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5962CertificateValid :
    WideCertificateValid leaf5962Box leaf5962Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi312ValidityFacts
    leaf5962LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5962CoverageChecked :
    coverageCheck (innerAD leaf5962Box) leaf5962InnerLog = true := by
  rfl'

private theorem leaf5962InnerLogValid :
    leaf5962InnerLog.Valid 8 (innerAD leaf5962Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint91PositiveFacts.valid leaf5962CoverageChecked

private noncomputable def leaf5962InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629517/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5962InputLogOnePlusV_eq :
    leaf5962InputLogOnePlusV = outerEnclosure 24
      (leaf5962Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5962RoundedFacts : LeafRoundedFacts 8
    leaf5962Certificate.logOnePlusV leaf5962InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5962InputLogOnePlusV_eq }

private noncomputable def leaf5962Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi312InputQChi innerPair294Input
    leaf5962InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5962LowerChecked :
    lowerCheck 24 leaf5962Box leaf5962Inputs = true := by
  rfl'

private theorem leaf5962CoversExact : CoversExact 8
    leaf5962Box leaf5962Certificate leaf5962InnerLog leaf5962Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi312RoundedFacts
    innerPair294RoundedFacts leaf5962RoundedFacts (by rfl)

private theorem leaf5962FlatSound : Sound leaf5962Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5962CertificateValid
    leaf5962InnerLogValid leaf5962CoversExact leaf5962LowerChecked

private noncomputable def leaf5963Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (51/128), chiHi := (103/256) }

private noncomputable def leaf5963Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871369/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712832000) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1372370689/1073741824) }, upper := { exponent := 1, mantissa := (10585/8192) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi311LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429228541/137425664000) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf5963InnerLog : WideLogData :=
  innerPair294Data

set_option maxRecDepth 1000000 in
private theorem leaf5963LocalValidity :
    LeafFacts leaf5963Box leaf5963Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5963Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712832000) }) = true
      norm_num [leaf5963Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5963CertificateValid :
    WideCertificateValid leaf5963Box leaf5963Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi311ValidityFacts
    leaf5963LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5963CoverageChecked :
    coverageCheck (innerAD leaf5963Box) leaf5963InnerLog = true := by
  rfl'

private theorem leaf5963InnerLogValid :
    leaf5963InnerLog.Valid 8 (innerAD leaf5963Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint91PositiveFacts.valid leaf5963CoverageChecked

private noncomputable def leaf5963InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907379/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5963InputLogOnePlusV_eq :
    leaf5963InputLogOnePlusV = outerEnclosure 24
      (leaf5963Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5963RoundedFacts : LeafRoundedFacts 8
    leaf5963Certificate.logOnePlusV leaf5963InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5963InputLogOnePlusV_eq }

private noncomputable def leaf5963Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi311InputQChi innerPair294Input
    leaf5963InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5963LowerChecked :
    lowerCheck 24 leaf5963Box leaf5963Inputs = true := by
  rfl'

private theorem leaf5963CoversExact : CoversExact 8
    leaf5963Box leaf5963Certificate leaf5963InnerLog leaf5963Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi311RoundedFacts
    innerPair294RoundedFacts leaf5963RoundedFacts (by rfl)

private theorem leaf5963FlatSound : Sound leaf5963Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5963CertificateValid
    leaf5963InnerLogValid leaf5963CoversExact leaf5963LowerChecked

private noncomputable def leaf5964Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (103/256), chiHi := (13/32) }

private noncomputable def leaf5964Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871371/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712767488) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1380562187/1073741824) }, upper := { exponent := 1, mantissa := (1331/1024) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi312LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429164029/137425534976) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf5964InnerLog : WideLogData :=
  innerPair339Data

set_option maxRecDepth 1000000 in
private theorem leaf5964LocalValidity :
    LeafFacts leaf5964Box leaf5964Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5964Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712767488) }) = true
      norm_num [leaf5964Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5964CertificateValid :
    WideCertificateValid leaf5964Box leaf5964Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi312ValidityFacts
    leaf5964LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5964CoverageChecked :
    coverageCheck (innerAD leaf5964Box) leaf5964InnerLog = true := by
  rfl'

private theorem leaf5964InnerLogValid :
    leaf5964InnerLog.Valid 8 (innerAD leaf5964Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint91PositiveFacts.valid leaf5964CoverageChecked

private noncomputable def leaf5964InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907381/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5964InputLogOnePlusV_eq :
    leaf5964InputLogOnePlusV = outerEnclosure 24
      (leaf5964Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5964RoundedFacts : LeafRoundedFacts 8
    leaf5964Certificate.logOnePlusV leaf5964InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5964InputLogOnePlusV_eq }

private noncomputable def leaf5964Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi312InputQChi innerPair339Input
    leaf5964InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5964LowerChecked :
    lowerCheck 24 leaf5964Box leaf5964Inputs = true := by
  rfl'

private theorem leaf5964CoversExact : CoversExact 8
    leaf5964Box leaf5964Certificate leaf5964InnerLog leaf5964Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi312RoundedFacts
    innerPair339RoundedFacts leaf5964RoundedFacts (by rfl)

private theorem leaf5964FlatSound : Sound leaf5964Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5964CertificateValid
    leaf5964InnerLogValid leaf5964CoversExact leaf5964LowerChecked

private noncomputable def leaf5965Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (25/64), chiHi := (101/256) }

private noncomputable def leaf5965Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871367/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712909312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1362540891/1073741824) }, upper := { exponent := 1, mantissa := (21019/16384) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi309LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429305853/137425818624) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf5965InnerLog : WideLogData :=
  innerPair681Data

set_option maxRecDepth 1000000 in
private theorem leaf5965LocalValidity :
    LeafFacts leaf5965Box leaf5965Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5965Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712909312) }) = true
      norm_num [leaf5965Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5965CertificateValid :
    WideCertificateValid leaf5965Box leaf5965Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi309ValidityFacts
    leaf5965LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5965CoverageChecked :
    coverageCheck (innerAD leaf5965Box) leaf5965InnerLog = true := by
  rfl'

private theorem leaf5965InnerLogValid :
    leaf5965InnerLog.Valid 8 (innerAD leaf5965Box) :=
  wideLogDataValid_of_cachedCheck endpoint434PositiveFacts
    endpoint435PositiveFacts.valid leaf5965CoverageChecked

private noncomputable def leaf5965InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814753/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5965InputLogOnePlusV_eq :
    leaf5965InputLogOnePlusV = outerEnclosure 24
      (leaf5965Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5965RoundedFacts : LeafRoundedFacts 8
    leaf5965Certificate.logOnePlusV leaf5965InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5965InputLogOnePlusV_eq }

private noncomputable def leaf5965Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi309InputQChi innerPair681Input
    leaf5965InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5965LowerChecked :
    lowerCheck 24 leaf5965Box leaf5965Inputs = true := by
  rfl'

private theorem leaf5965CoversExact : CoversExact 8
    leaf5965Box leaf5965Certificate leaf5965InnerLog leaf5965Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi309RoundedFacts
    innerPair681RoundedFacts leaf5965RoundedFacts (by rfl)

private theorem leaf5965FlatSound : Sound leaf5965Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5965CertificateValid
    leaf5965InnerLogValid leaf5965CoversExact leaf5965LowerChecked

private noncomputable def leaf5966Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (101/256), chiHi := (51/128) }

private noncomputable def leaf5966Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871369/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712844288) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1370797921/1073741824) }, upper := { exponent := 1, mantissa := (10573/8192) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi310LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429240829/137425688576) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf5966InnerLog : WideLogData :=
  innerPair693Data

set_option maxRecDepth 1000000 in
private theorem leaf5966LocalValidity :
    LeafFacts leaf5966Box leaf5966Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5966Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712844288) }) = true
      norm_num [leaf5966Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5966CertificateValid :
    WideCertificateValid leaf5966Box leaf5966Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi310ValidityFacts
    leaf5966LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5966CoverageChecked :
    coverageCheck (innerAD leaf5966Box) leaf5966InnerLog = true := by
  rfl'

private theorem leaf5966InnerLogValid :
    leaf5966InnerLog.Valid 8 (innerAD leaf5966Box) :=
  wideLogDataValid_of_cachedCheck endpoint437PositiveFacts
    endpoint436PositiveFacts.valid leaf5966CoverageChecked

private noncomputable def leaf5966InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814757/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5966InputLogOnePlusV_eq :
    leaf5966InputLogOnePlusV = outerEnclosure 24
      (leaf5966Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5966RoundedFacts : LeafRoundedFacts 8
    leaf5966Certificate.logOnePlusV leaf5966InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5966InputLogOnePlusV_eq }

private noncomputable def leaf5966Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi310InputQChi innerPair693Input
    leaf5966InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5966LowerChecked :
    lowerCheck 24 leaf5966Box leaf5966Inputs = true := by
  rfl'

private theorem leaf5966CoversExact : CoversExact 8
    leaf5966Box leaf5966Certificate leaf5966InnerLog leaf5966Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi310RoundedFacts
    innerPair693RoundedFacts leaf5966RoundedFacts (by rfl)

private theorem leaf5966FlatSound : Sound leaf5966Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5966CertificateValid
    leaf5966InnerLogValid leaf5966CoversExact leaf5966LowerChecked

private noncomputable def leaf5967Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (25/64), chiHi := (101/256) }

private noncomputable def leaf5967Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871369/536870912) }, vSqrt := { lower := (65527/65536), upper := (4042140973/4041932800) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1369094089/1073741824) }, upper := { exponent := 1, mantissa := (165/128) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi309LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (8084073773/8083865600) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf5967InnerLog : WideLogData :=
  innerPair692Data

set_option maxRecDepth 1000000 in
private theorem leaf5967LocalValidity :
    LeafFacts leaf5967Box leaf5967Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5967Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (4042140973/4041932800) }) = true
      norm_num [leaf5967Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5967CertificateValid :
    WideCertificateValid leaf5967Box leaf5967Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi309ValidityFacts
    leaf5967LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5967CoverageChecked :
    coverageCheck (innerAD leaf5967Box) leaf5967InnerLog = true := by
  rfl'

private theorem leaf5967InnerLogValid :
    leaf5967InnerLog.Valid 8 (innerAD leaf5967Box) :=
  wideLogDataValid_of_cachedCheck endpoint437PositiveFacts
    endpoint435PositiveFacts.valid leaf5967CoverageChecked

private noncomputable def leaf5967InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629513/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5967InputLogOnePlusV_eq :
    leaf5967InputLogOnePlusV = outerEnclosure 24
      (leaf5967Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5967RoundedFacts : LeafRoundedFacts 8
    leaf5967Certificate.logOnePlusV leaf5967InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5967InputLogOnePlusV_eq }

private noncomputable def leaf5967Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi309InputQChi innerPair692Input
    leaf5967InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5967LowerChecked :
    lowerCheck 24 leaf5967Box leaf5967Inputs = true := by
  rfl'

private theorem leaf5967CoversExact : CoversExact 8
    leaf5967Box leaf5967Certificate leaf5967InnerLog leaf5967Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi309RoundedFacts
    innerPair692RoundedFacts leaf5967RoundedFacts (by rfl)

private theorem leaf5967FlatSound : Sound leaf5967Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5967CertificateValid
    leaf5967InnerLogValid leaf5967CoversExact leaf5967LowerChecked

private noncomputable def leaf5968Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (101/256), chiHi := (51/128) }

private noncomputable def leaf5968Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871371/536870912) }, vSqrt := { lower := (65527/65536), upper := (68716396541/68712792064) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1377416651/1073741824) }, upper := { exponent := 1, mantissa := (83/64) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi310LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (137429188605/137425584128) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf5968InnerLog : WideLogData :=
  innerPair339Data

set_option maxRecDepth 1000000 in
private theorem leaf5968LocalValidity :
    LeafFacts leaf5968Box leaf5968Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5968Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (68716396541/68712792064) }) = true
      norm_num [leaf5968Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5968CertificateValid :
    WideCertificateValid leaf5968Box leaf5968Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi310ValidityFacts
    leaf5968LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5968CoverageChecked :
    coverageCheck (innerAD leaf5968Box) leaf5968InnerLog = true := by
  rfl'

private theorem leaf5968InnerLogValid :
    leaf5968InnerLog.Valid 8 (innerAD leaf5968Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint91PositiveFacts.valid leaf5968CoverageChecked

private noncomputable def leaf5968InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629521/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5968InputLogOnePlusV_eq :
    leaf5968InputLogOnePlusV = outerEnclosure 24
      (leaf5968Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5968RoundedFacts : LeafRoundedFacts 8
    leaf5968Certificate.logOnePlusV leaf5968InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5968InputLogOnePlusV_eq }

private noncomputable def leaf5968Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi310InputQChi innerPair339Input
    leaf5968InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5968LowerChecked :
    lowerCheck 24 leaf5968Box leaf5968Inputs = true := by
  rfl'

private theorem leaf5968CoversExact : CoversExact 8
    leaf5968Box leaf5968Certificate leaf5968InnerLog leaf5968Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi310RoundedFacts
    innerPair339RoundedFacts leaf5968RoundedFacts (by rfl)

private theorem leaf5968FlatSound : Sound leaf5968Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5968CertificateValid
    leaf5968InnerLogValid leaf5968CoversExact leaf5968LowerChecked

private noncomputable def leaf5969Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (51/128), chiHi := (103/256) }

private noncomputable def leaf5969Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871371/536870912) }, vSqrt := { lower := (8191/8192), upper := (4042140973/4041928192) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1379054951/1073741824) }, upper := { exponent := 1, mantissa := (21273/16384) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi311LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (8084069165/8083856384) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf5969InnerLog : WideLogData :=
  innerPair339Data

set_option maxRecDepth 1000000 in
private theorem leaf5969LocalValidity :
    LeafFacts leaf5969Box leaf5969Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5969Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4042140973/4041928192) }) = true
      norm_num [leaf5969Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5969CertificateValid :
    WideCertificateValid leaf5969Box leaf5969Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi311ValidityFacts
    leaf5969LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5969CoverageChecked :
    coverageCheck (innerAD leaf5969Box) leaf5969InnerLog = true := by
  rfl'

private theorem leaf5969InnerLogValid :
    leaf5969InnerLog.Valid 8 (innerAD leaf5969Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint91PositiveFacts.valid leaf5969CoverageChecked

private noncomputable def leaf5969InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814761/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5969InputLogOnePlusV_eq :
    leaf5969InputLogOnePlusV = outerEnclosure 24
      (leaf5969Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5969RoundedFacts : LeafRoundedFacts 8
    leaf5969Certificate.logOnePlusV leaf5969InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5969InputLogOnePlusV_eq }

private noncomputable def leaf5969Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi311InputQChi innerPair339Input
    leaf5969InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5969LowerChecked :
    lowerCheck 24 leaf5969Box leaf5969Inputs = true := by
  rfl'

private theorem leaf5969CoversExact : CoversExact 8
    leaf5969Box leaf5969Certificate leaf5969InnerLog leaf5969Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi311RoundedFacts
    innerPair339RoundedFacts leaf5969RoundedFacts (by rfl)

private theorem leaf5969FlatSound : Sound leaf5969Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5969CertificateValid
    leaf5969InnerLogValid leaf5969CoversExact leaf5969LowerChecked

private noncomputable def leaf5970Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (103/256), chiHi := (13/32) }

private noncomputable def leaf5970Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871373/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712714240) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1387311981/1073741824) }, upper := { exponent := 1, mantissa := (2675/2048) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi312LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429110781/137425428480) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf5970InnerLog : WideLogData :=
  innerPair339Data

set_option maxRecDepth 1000000 in
private theorem leaf5970LocalValidity :
    LeafFacts leaf5970Box leaf5970Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5970Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712714240) }) = true
      norm_num [leaf5970Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5970CertificateValid :
    WideCertificateValid leaf5970Box leaf5970Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi312ValidityFacts
    leaf5970LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5970CoverageChecked :
    coverageCheck (innerAD leaf5970Box) leaf5970InnerLog = true := by
  rfl'

private theorem leaf5970InnerLogValid :
    leaf5970InnerLog.Valid 8 (innerAD leaf5970Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint91PositiveFacts.valid leaf5970CoverageChecked

private noncomputable def leaf5970InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814765/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5970InputLogOnePlusV_eq :
    leaf5970InputLogOnePlusV = outerEnclosure 24
      (leaf5970Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5970RoundedFacts : LeafRoundedFacts 8
    leaf5970Certificate.logOnePlusV leaf5970InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5970InputLogOnePlusV_eq }

private noncomputable def leaf5970Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi312InputQChi innerPair339Input
    leaf5970InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5970LowerChecked :
    lowerCheck 24 leaf5970Box leaf5970Inputs = true := by
  rfl'

private theorem leaf5970CoversExact : CoversExact 8
    leaf5970Box leaf5970Certificate leaf5970InnerLog leaf5970Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi312RoundedFacts
    innerPair339RoundedFacts leaf5970RoundedFacts (by rfl)

private theorem leaf5970FlatSound : Sound leaf5970Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5970CertificateValid
    leaf5970InnerLogValid leaf5970CoversExact leaf5970LowerChecked

private noncomputable def leaf5971Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (51/128), chiHi := (103/256) }

private noncomputable def leaf5971Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871373/536870912) }, vSqrt := { lower := (65527/65536), upper := (68716396541/68712726528) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1385739213/1073741824) }, upper := { exponent := 1, mantissa := (167/128) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi311LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (137429123069/137425453056) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf5971InnerLog : WideLogData :=
  innerPair339Data

set_option maxRecDepth 1000000 in
private theorem leaf5971LocalValidity :
    LeafFacts leaf5971Box leaf5971Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5971Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (68716396541/68712726528) }) = true
      norm_num [leaf5971Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5971CertificateValid :
    WideCertificateValid leaf5971Box leaf5971Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi311ValidityFacts
    leaf5971LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5971CoverageChecked :
    coverageCheck (innerAD leaf5971Box) leaf5971InnerLog = true := by
  rfl'

private theorem leaf5971InnerLogValid :
    leaf5971InnerLog.Valid 8 (innerAD leaf5971Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint91PositiveFacts.valid leaf5971CoverageChecked

private noncomputable def leaf5971InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629529/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5971InputLogOnePlusV_eq :
    leaf5971InputLogOnePlusV = outerEnclosure 24
      (leaf5971Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5971RoundedFacts : LeafRoundedFacts 8
    leaf5971Certificate.logOnePlusV leaf5971InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5971InputLogOnePlusV_eq }

private noncomputable def leaf5971Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi311InputQChi innerPair339Input
    leaf5971InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5971LowerChecked :
    lowerCheck 24 leaf5971Box leaf5971Inputs = true := by
  rfl'

private theorem leaf5971CoversExact : CoversExact 8
    leaf5971Box leaf5971Certificate leaf5971InnerLog leaf5971Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi311RoundedFacts
    innerPair339RoundedFacts leaf5971RoundedFacts (by rfl)

private theorem leaf5971FlatSound : Sound leaf5971Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5971CertificateValid
    leaf5971InnerLogValid leaf5971CoversExact leaf5971LowerChecked

private noncomputable def leaf5972Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (103/256), chiHi := (13/32) }

private noncomputable def leaf5972Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871375/536870912) }, vSqrt := { lower := (65527/65536), upper := (68716396541/68712660992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1394061775/1073741824) }, upper := { exponent := 1, mantissa := (21/16) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi312LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (137429057533/137425321984) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf5972InnerLog : WideLogData :=
  innerPair339Data

set_option maxRecDepth 1000000 in
private theorem leaf5972LocalValidity :
    LeafFacts leaf5972Box leaf5972Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5972Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (68716396541/68712660992) }) = true
      norm_num [leaf5972Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5972CertificateValid :
    WideCertificateValid leaf5972Box leaf5972Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi312ValidityFacts
    leaf5972LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5972CoverageChecked :
    coverageCheck (innerAD leaf5972Box) leaf5972InnerLog = true := by
  rfl'

private theorem leaf5972InnerLogValid :
    leaf5972InnerLog.Valid 8 (innerAD leaf5972Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint91PositiveFacts.valid leaf5972CoverageChecked

private noncomputable def leaf5972InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629537/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5972InputLogOnePlusV_eq :
    leaf5972InputLogOnePlusV = outerEnclosure 24
      (leaf5972Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5972RoundedFacts : LeafRoundedFacts 8
    leaf5972Certificate.logOnePlusV leaf5972InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5972InputLogOnePlusV_eq }

private noncomputable def leaf5972Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi312InputQChi innerPair339Input
    leaf5972InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5972LowerChecked :
    lowerCheck 24 leaf5972Box leaf5972Inputs = true := by
  rfl'

private theorem leaf5972CoversExact : CoversExact 8
    leaf5972Box leaf5972Certificate leaf5972InnerLog leaf5972Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi312RoundedFacts
    innerPair339RoundedFacts leaf5972RoundedFacts (by rfl)

private theorem leaf5972FlatSound : Sound leaf5972Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5972CertificateValid
    leaf5972InnerLogValid leaf5972CoversExact leaf5972LowerChecked

private noncomputable def component119Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (3/8), chiHi := (49/128) }

set_option maxRecDepth 1000000 in
private theorem component119Node0_sound : Sound component119Node0Box :=
  sound_of_literal_split component119Node0Box leaf5909Box leaf5910Box
    .chi (97/256) (by rfl) (by rfl)
    leaf5909FlatSound leaf5910FlatSound

private noncomputable def component119Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (3/8), chiHi := (49/128) }

set_option maxRecDepth 1000000 in
private theorem component119Node1_sound : Sound component119Node1Box :=
  sound_of_literal_split component119Node1Box leaf5911Box leaf5912Box
    .chi (97/256) (by rfl) (by rfl)
    leaf5911FlatSound leaf5912FlatSound

private noncomputable def component119Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (3/8), chiHi := (49/128) }

set_option maxRecDepth 1000000 in
private theorem component119Node2_sound : Sound component119Node2Box :=
  sound_of_literal_split component119Node2Box component119Node0Box component119Node1Box
    .k (121/32) (by rfl) (by rfl)
    component119Node0_sound component119Node1_sound

private noncomputable def component119Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (49/128), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component119Node3_sound : Sound component119Node3Box :=
  sound_of_literal_split component119Node3Box leaf5913Box leaf5914Box
    .chi (99/256) (by rfl) (by rfl)
    leaf5913FlatSound leaf5914FlatSound

private noncomputable def component119Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (49/128), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component119Node4_sound : Sound component119Node4Box :=
  sound_of_literal_split component119Node4Box leaf5915Box leaf5916Box
    .chi (99/256) (by rfl) (by rfl)
    leaf5915FlatSound leaf5916FlatSound

private noncomputable def component119Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (49/128), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component119Node5_sound : Sound component119Node5Box :=
  sound_of_literal_split component119Node5Box component119Node3Box component119Node4Box
    .k (121/32) (by rfl) (by rfl)
    component119Node3_sound component119Node4_sound

private noncomputable def component119Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (3/8), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component119Node6_sound : Sound component119Node6Box :=
  sound_of_literal_split component119Node6Box component119Node2Box component119Node5Box
    .chi (49/128) (by rfl) (by rfl)
    component119Node2_sound component119Node5_sound

private noncomputable def component119Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (3/8), chiHi := (49/128) }

set_option maxRecDepth 1000000 in
private theorem component119Node7_sound : Sound component119Node7Box :=
  sound_of_literal_split component119Node7Box leaf5917Box leaf5918Box
    .chi (97/256) (by rfl) (by rfl)
    leaf5917FlatSound leaf5918FlatSound

private noncomputable def component119Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (3/8), chiHi := (49/128) }

set_option maxRecDepth 1000000 in
private theorem component119Node8_sound : Sound component119Node8Box :=
  sound_of_literal_split component119Node8Box leaf5919Box leaf5920Box
    .chi (97/256) (by rfl) (by rfl)
    leaf5919FlatSound leaf5920FlatSound

private noncomputable def component119Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (3/8), chiHi := (49/128) }

set_option maxRecDepth 1000000 in
private theorem component119Node9_sound : Sound component119Node9Box :=
  sound_of_literal_split component119Node9Box component119Node7Box component119Node8Box
    .k (123/32) (by rfl) (by rfl)
    component119Node7_sound component119Node8_sound

private noncomputable def component119Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (49/128), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component119Node10_sound : Sound component119Node10Box :=
  sound_of_literal_split component119Node10Box leaf5921Box leaf5922Box
    .chi (99/256) (by rfl) (by rfl)
    leaf5921FlatSound leaf5922FlatSound

private noncomputable def component119Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (49/128), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component119Node11_sound : Sound component119Node11Box :=
  sound_of_literal_split component119Node11Box leaf5923Box leaf5924Box
    .chi (99/256) (by rfl) (by rfl)
    leaf5923FlatSound leaf5924FlatSound

private noncomputable def component119Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (49/128), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component119Node12_sound : Sound component119Node12Box :=
  sound_of_literal_split component119Node12Box component119Node10Box component119Node11Box
    .k (123/32) (by rfl) (by rfl)
    component119Node10_sound component119Node11_sound

private noncomputable def component119Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (3/8), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component119Node13_sound : Sound component119Node13Box :=
  sound_of_literal_split component119Node13Box component119Node9Box component119Node12Box
    .chi (49/128) (by rfl) (by rfl)
    component119Node9_sound component119Node12_sound

private noncomputable def component119Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (3/8), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component119Node14_sound : Sound component119Node14Box :=
  sound_of_literal_split component119Node14Box component119Node6Box component119Node13Box
    .k (61/16) (by rfl) (by rfl)
    component119Node6_sound component119Node13_sound

private noncomputable def component119Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (25/64), chiHi := (51/128) }

set_option maxRecDepth 1000000 in
private theorem component119Node15_sound : Sound component119Node15Box :=
  sound_of_literal_split component119Node15Box leaf5925Box leaf5926Box
    .chi (101/256) (by rfl) (by rfl)
    leaf5925FlatSound leaf5926FlatSound

private noncomputable def component119Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (25/64), chiHi := (51/128) }

set_option maxRecDepth 1000000 in
private theorem component119Node16_sound : Sound component119Node16Box :=
  sound_of_literal_split component119Node16Box leaf5927Box leaf5928Box
    .chi (101/256) (by rfl) (by rfl)
    leaf5927FlatSound leaf5928FlatSound

private noncomputable def component119Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (25/64), chiHi := (51/128) }

set_option maxRecDepth 1000000 in
private theorem component119Node17_sound : Sound component119Node17Box :=
  sound_of_literal_split component119Node17Box component119Node15Box component119Node16Box
    .k (121/32) (by rfl) (by rfl)
    component119Node15_sound component119Node16_sound

private noncomputable def component119Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (51/128), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component119Node18_sound : Sound component119Node18Box :=
  sound_of_literal_split component119Node18Box leaf5929Box leaf5930Box
    .chi (103/256) (by rfl) (by rfl)
    leaf5929FlatSound leaf5930FlatSound

private noncomputable def component119Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (51/128), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component119Node19_sound : Sound component119Node19Box :=
  sound_of_literal_split component119Node19Box leaf5931Box leaf5932Box
    .chi (103/256) (by rfl) (by rfl)
    leaf5931FlatSound leaf5932FlatSound

private noncomputable def component119Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (51/128), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component119Node20_sound : Sound component119Node20Box :=
  sound_of_literal_split component119Node20Box component119Node18Box component119Node19Box
    .k (121/32) (by rfl) (by rfl)
    component119Node18_sound component119Node19_sound

private noncomputable def component119Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (25/64), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component119Node21_sound : Sound component119Node21Box :=
  sound_of_literal_split component119Node21Box component119Node17Box component119Node20Box
    .chi (51/128) (by rfl) (by rfl)
    component119Node17_sound component119Node20_sound

private noncomputable def component119Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (25/64), chiHi := (51/128) }

set_option maxRecDepth 1000000 in
private theorem component119Node22_sound : Sound component119Node22Box :=
  sound_of_literal_split component119Node22Box leaf5933Box leaf5934Box
    .chi (101/256) (by rfl) (by rfl)
    leaf5933FlatSound leaf5934FlatSound

private noncomputable def component119Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (25/64), chiHi := (51/128) }

set_option maxRecDepth 1000000 in
private theorem component119Node23_sound : Sound component119Node23Box :=
  sound_of_literal_split component119Node23Box leaf5935Box leaf5936Box
    .chi (101/256) (by rfl) (by rfl)
    leaf5935FlatSound leaf5936FlatSound

private noncomputable def component119Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (25/64), chiHi := (51/128) }

set_option maxRecDepth 1000000 in
private theorem component119Node24_sound : Sound component119Node24Box :=
  sound_of_literal_split component119Node24Box component119Node22Box component119Node23Box
    .k (123/32) (by rfl) (by rfl)
    component119Node22_sound component119Node23_sound

private noncomputable def component119Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (51/128), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component119Node25_sound : Sound component119Node25Box :=
  sound_of_literal_split component119Node25Box leaf5937Box leaf5938Box
    .chi (103/256) (by rfl) (by rfl)
    leaf5937FlatSound leaf5938FlatSound

private noncomputable def component119Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (51/128), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component119Node26_sound : Sound component119Node26Box :=
  sound_of_literal_split component119Node26Box leaf5939Box leaf5940Box
    .chi (103/256) (by rfl) (by rfl)
    leaf5939FlatSound leaf5940FlatSound

private noncomputable def component119Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (51/128), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component119Node27_sound : Sound component119Node27Box :=
  sound_of_literal_split component119Node27Box component119Node25Box component119Node26Box
    .k (123/32) (by rfl) (by rfl)
    component119Node25_sound component119Node26_sound

private noncomputable def component119Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (25/64), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component119Node28_sound : Sound component119Node28Box :=
  sound_of_literal_split component119Node28Box component119Node24Box component119Node27Box
    .chi (51/128) (by rfl) (by rfl)
    component119Node24_sound component119Node27_sound

private noncomputable def component119Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (25/64), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component119Node29_sound : Sound component119Node29Box :=
  sound_of_literal_split component119Node29Box component119Node21Box component119Node28Box
    .k (61/16) (by rfl) (by rfl)
    component119Node21_sound component119Node28_sound

private noncomputable def component119Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (3/8), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component119Node30_sound : Sound component119Node30Box :=
  sound_of_literal_split component119Node30Box component119Node14Box component119Node29Box
    .chi (25/64) (by rfl) (by rfl)
    component119Node14_sound component119Node29_sound

private noncomputable def component119Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (3/8), chiHi := (49/128) }

set_option maxRecDepth 1000000 in
private theorem component119Node31_sound : Sound component119Node31Box :=
  sound_of_literal_split component119Node31Box leaf5941Box leaf5942Box
    .chi (97/256) (by rfl) (by rfl)
    leaf5941FlatSound leaf5942FlatSound

private noncomputable def component119Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (3/8), chiHi := (49/128) }

set_option maxRecDepth 1000000 in
private theorem component119Node32_sound : Sound component119Node32Box :=
  sound_of_literal_split component119Node32Box leaf5943Box leaf5944Box
    .chi (97/256) (by rfl) (by rfl)
    leaf5943FlatSound leaf5944FlatSound

private noncomputable def component119Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (3/8), chiHi := (49/128) }

set_option maxRecDepth 1000000 in
private theorem component119Node33_sound : Sound component119Node33Box :=
  sound_of_literal_split component119Node33Box component119Node31Box component119Node32Box
    .k (125/32) (by rfl) (by rfl)
    component119Node31_sound component119Node32_sound

private noncomputable def component119Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (49/128), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component119Node34_sound : Sound component119Node34Box :=
  sound_of_literal_split component119Node34Box leaf5945Box leaf5946Box
    .chi (99/256) (by rfl) (by rfl)
    leaf5945FlatSound leaf5946FlatSound

private noncomputable def component119Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (49/128), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component119Node35_sound : Sound component119Node35Box :=
  sound_of_literal_split component119Node35Box leaf5947Box leaf5948Box
    .chi (99/256) (by rfl) (by rfl)
    leaf5947FlatSound leaf5948FlatSound

private noncomputable def component119Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (49/128), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component119Node36_sound : Sound component119Node36Box :=
  sound_of_literal_split component119Node36Box component119Node34Box component119Node35Box
    .k (125/32) (by rfl) (by rfl)
    component119Node34_sound component119Node35_sound

private noncomputable def component119Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (3/8), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component119Node37_sound : Sound component119Node37Box :=
  sound_of_literal_split component119Node37Box component119Node33Box component119Node36Box
    .chi (49/128) (by rfl) (by rfl)
    component119Node33_sound component119Node36_sound

private noncomputable def component119Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (3/8), chiHi := (49/128) }

set_option maxRecDepth 1000000 in
private theorem component119Node38_sound : Sound component119Node38Box :=
  sound_of_literal_split component119Node38Box leaf5949Box leaf5950Box
    .chi (97/256) (by rfl) (by rfl)
    leaf5949FlatSound leaf5950FlatSound

private noncomputable def component119Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (3/8), chiHi := (49/128) }

set_option maxRecDepth 1000000 in
private theorem component119Node39_sound : Sound component119Node39Box :=
  sound_of_literal_split component119Node39Box leaf5951Box leaf5952Box
    .chi (97/256) (by rfl) (by rfl)
    leaf5951FlatSound leaf5952FlatSound

private noncomputable def component119Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (3/8), chiHi := (49/128) }

set_option maxRecDepth 1000000 in
private theorem component119Node40_sound : Sound component119Node40Box :=
  sound_of_literal_split component119Node40Box component119Node38Box component119Node39Box
    .k (127/32) (by rfl) (by rfl)
    component119Node38_sound component119Node39_sound

private noncomputable def component119Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (49/128), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component119Node41_sound : Sound component119Node41Box :=
  sound_of_literal_split component119Node41Box leaf5953Box leaf5954Box
    .chi (99/256) (by rfl) (by rfl)
    leaf5953FlatSound leaf5954FlatSound

private noncomputable def component119Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (49/128), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component119Node42_sound : Sound component119Node42Box :=
  sound_of_literal_split component119Node42Box leaf5955Box leaf5956Box
    .chi (99/256) (by rfl) (by rfl)
    leaf5955FlatSound leaf5956FlatSound

private noncomputable def component119Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (49/128), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component119Node43_sound : Sound component119Node43Box :=
  sound_of_literal_split component119Node43Box component119Node41Box component119Node42Box
    .k (127/32) (by rfl) (by rfl)
    component119Node41_sound component119Node42_sound

private noncomputable def component119Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (3/8), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component119Node44_sound : Sound component119Node44Box :=
  sound_of_literal_split component119Node44Box component119Node40Box component119Node43Box
    .chi (49/128) (by rfl) (by rfl)
    component119Node40_sound component119Node43_sound

private noncomputable def component119Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (3/8), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component119Node45_sound : Sound component119Node45Box :=
  sound_of_literal_split component119Node45Box component119Node37Box component119Node44Box
    .k (63/16) (by rfl) (by rfl)
    component119Node37_sound component119Node44_sound

private noncomputable def component119Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (25/64), chiHi := (51/128) }

set_option maxRecDepth 1000000 in
private theorem component119Node46_sound : Sound component119Node46Box :=
  sound_of_literal_split component119Node46Box leaf5957Box leaf5958Box
    .chi (101/256) (by rfl) (by rfl)
    leaf5957FlatSound leaf5958FlatSound

private noncomputable def component119Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (25/64), chiHi := (51/128) }

set_option maxRecDepth 1000000 in
private theorem component119Node47_sound : Sound component119Node47Box :=
  sound_of_literal_split component119Node47Box leaf5959Box leaf5960Box
    .chi (101/256) (by rfl) (by rfl)
    leaf5959FlatSound leaf5960FlatSound

private noncomputable def component119Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (25/64), chiHi := (51/128) }

set_option maxRecDepth 1000000 in
private theorem component119Node48_sound : Sound component119Node48Box :=
  sound_of_literal_split component119Node48Box component119Node46Box component119Node47Box
    .k (125/32) (by rfl) (by rfl)
    component119Node46_sound component119Node47_sound

private noncomputable def component119Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (51/128), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component119Node49_sound : Sound component119Node49Box :=
  sound_of_literal_split component119Node49Box leaf5961Box leaf5962Box
    .chi (103/256) (by rfl) (by rfl)
    leaf5961FlatSound leaf5962FlatSound

private noncomputable def component119Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (51/128), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component119Node50_sound : Sound component119Node50Box :=
  sound_of_literal_split component119Node50Box leaf5963Box leaf5964Box
    .chi (103/256) (by rfl) (by rfl)
    leaf5963FlatSound leaf5964FlatSound

private noncomputable def component119Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (51/128), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component119Node51_sound : Sound component119Node51Box :=
  sound_of_literal_split component119Node51Box component119Node49Box component119Node50Box
    .k (125/32) (by rfl) (by rfl)
    component119Node49_sound component119Node50_sound

private noncomputable def component119Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (25/64), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component119Node52_sound : Sound component119Node52Box :=
  sound_of_literal_split component119Node52Box component119Node48Box component119Node51Box
    .chi (51/128) (by rfl) (by rfl)
    component119Node48_sound component119Node51_sound

private noncomputable def component119Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (25/64), chiHi := (51/128) }

set_option maxRecDepth 1000000 in
private theorem component119Node53_sound : Sound component119Node53Box :=
  sound_of_literal_split component119Node53Box leaf5965Box leaf5966Box
    .chi (101/256) (by rfl) (by rfl)
    leaf5965FlatSound leaf5966FlatSound

private noncomputable def component119Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (25/64), chiHi := (51/128) }

set_option maxRecDepth 1000000 in
private theorem component119Node54_sound : Sound component119Node54Box :=
  sound_of_literal_split component119Node54Box leaf5967Box leaf5968Box
    .chi (101/256) (by rfl) (by rfl)
    leaf5967FlatSound leaf5968FlatSound

private noncomputable def component119Node55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (25/64), chiHi := (51/128) }

set_option maxRecDepth 1000000 in
private theorem component119Node55_sound : Sound component119Node55Box :=
  sound_of_literal_split component119Node55Box component119Node53Box component119Node54Box
    .k (127/32) (by rfl) (by rfl)
    component119Node53_sound component119Node54_sound

private noncomputable def component119Node56Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (51/128), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component119Node56_sound : Sound component119Node56Box :=
  sound_of_literal_split component119Node56Box leaf5969Box leaf5970Box
    .chi (103/256) (by rfl) (by rfl)
    leaf5969FlatSound leaf5970FlatSound

private noncomputable def component119Node57Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (51/128), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component119Node57_sound : Sound component119Node57Box :=
  sound_of_literal_split component119Node57Box leaf5971Box leaf5972Box
    .chi (103/256) (by rfl) (by rfl)
    leaf5971FlatSound leaf5972FlatSound

private noncomputable def component119Node58Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (51/128), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component119Node58_sound : Sound component119Node58Box :=
  sound_of_literal_split component119Node58Box component119Node56Box component119Node57Box
    .k (127/32) (by rfl) (by rfl)
    component119Node56_sound component119Node57_sound

private noncomputable def component119Node59Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (25/64), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component119Node59_sound : Sound component119Node59Box :=
  sound_of_literal_split component119Node59Box component119Node55Box component119Node58Box
    .chi (51/128) (by rfl) (by rfl)
    component119Node55_sound component119Node58_sound

private noncomputable def component119Node60Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (25/64), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component119Node60_sound : Sound component119Node60Box :=
  sound_of_literal_split component119Node60Box component119Node52Box component119Node59Box
    .k (63/16) (by rfl) (by rfl)
    component119Node52_sound component119Node59_sound

private noncomputable def component119Node61Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (3/8), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component119Node61_sound : Sound component119Node61Box :=
  sound_of_literal_split component119Node61Box component119Node45Box component119Node60Box
    .chi (25/64) (by rfl) (by rfl)
    component119Node45_sound component119Node60_sound

noncomputable def component119Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (4), chiLo := (3/8), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
theorem component119_sound : Sound component119Box :=
  sound_of_literal_split component119Box component119Node30Box component119Node61Box
    .k (31/8) (by rfl) (by rfl)
    component119Node30_sound component119Node61_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
