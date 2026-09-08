import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch7
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

private noncomputable def leaf4290Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (193/64), chiLo := (1/4), chiHi := (33/128) }

private noncomputable def leaf4290Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871363/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432431616) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (939466303/536870912) }, upper := { exponent := 0, mantissa := (14561/8192) } }, logOuter := sk185LogOuterCertificate, logK := sk185LogKCertificate, logChi := chi241LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869353471/274864863232) } }, logDArg := sk185LogDArgCertificate }

private noncomputable def leaf4290InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf4290LocalValidity :
    LeafFacts leaf4290Box leaf4290Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4290Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432431616) }) = true
      norm_num [leaf4290Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4290CertificateValid :
    WideCertificateValid leaf4290Box leaf4290Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk185ValidityFacts chi241ValidityFacts
    leaf4290LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4290CoverageChecked :
    coverageCheck (innerAD leaf4290Box) leaf4290InnerLog = true := by
  rfl'

private theorem leaf4290InnerLogValid :
    leaf4290InnerLog.Valid 8 (innerAD leaf4290Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf4290CoverageChecked

private noncomputable def leaf4290InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629355/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4290InputLogOnePlusV_eq :
    leaf4290InputLogOnePlusV = outerEnclosure 24
      (leaf4290Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4290RoundedFacts : LeafRoundedFacts 8
    leaf4290Certificate.logOnePlusV leaf4290InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4290InputLogOnePlusV_eq }

private noncomputable def leaf4290Inputs : Inputs :=
  inputsOfCaches globalInput sk185RoundedInputs
    chi241InputQChi innerPair66Input
    leaf4290InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4290LowerChecked :
    lowerCheck 24 leaf4290Box leaf4290Inputs = true := by
  rfl'

private theorem leaf4290CoversExact : CoversExact 8
    leaf4290Box leaf4290Certificate leaf4290InnerLog leaf4290Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk185RoundedFacts chi241RoundedFacts
    innerPair66RoundedFacts leaf4290RoundedFacts (by rfl)

private theorem leaf4290FlatSound : Sound leaf4290Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4290CertificateValid
    leaf4290InnerLogValid leaf4290CoversExact leaf4290LowerChecked

private noncomputable def leaf4291Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (193/64), kHi := (97/32), chiLo := (1/4), chiHi := (33/128) }

private noncomputable def leaf4291Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871365/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432397824) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (941563325/536870912) }, upper := { exponent := 0, mantissa := (7297/4096) } }, logOuter := sk186LogOuterCertificate, logK := sk186LogKCertificate, logChi := chi241LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869319679/274864795648) } }, logDArg := sk186LogDArgCertificate }

private noncomputable def leaf4291InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf4291LocalValidity :
    LeafFacts leaf4291Box leaf4291Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4291Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432397824) }) = true
      norm_num [leaf4291Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4291CertificateValid :
    WideCertificateValid leaf4291Box leaf4291Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk186ValidityFacts chi241ValidityFacts
    leaf4291LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4291CoverageChecked :
    coverageCheck (innerAD leaf4291Box) leaf4291InnerLog = true := by
  rfl'

private theorem leaf4291InnerLogValid :
    leaf4291InnerLog.Valid 8 (innerAD leaf4291Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf4291CoverageChecked

private noncomputable def leaf4291InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629357/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4291InputLogOnePlusV_eq :
    leaf4291InputLogOnePlusV = outerEnclosure 24
      (leaf4291Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4291RoundedFacts : LeafRoundedFacts 8
    leaf4291Certificate.logOnePlusV leaf4291InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4291InputLogOnePlusV_eq }

private noncomputable def leaf4291Inputs : Inputs :=
  inputsOfCaches globalInput sk186RoundedInputs
    chi241InputQChi innerPair71Input
    leaf4291InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4291LowerChecked :
    lowerCheck 24 leaf4291Box leaf4291Inputs = true := by
  rfl'

private theorem leaf4291CoversExact : CoversExact 8
    leaf4291Box leaf4291Certificate leaf4291InnerLog leaf4291Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk186RoundedFacts chi241RoundedFacts
    innerPair71RoundedFacts leaf4291RoundedFacts (by rfl)

private theorem leaf4291FlatSound : Sound leaf4291Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4291CertificateValid
    leaf4291InnerLogValid leaf4291CoversExact leaf4291LowerChecked

private noncomputable def leaf4292Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (195/64), chiLo := (1/4), chiHi := (33/128) }

private noncomputable def leaf4292Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871367/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432364032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (943660347/536870912) }, upper := { exponent := 0, mantissa := (14627/8192) } }, logOuter := sk187LogOuterCertificate, logK := sk187LogKCertificate, logChi := chi241LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869285887/274864728064) } }, logDArg := sk187LogDArgCertificate }

private noncomputable def leaf4292InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf4292LocalValidity :
    LeafFacts leaf4292Box leaf4292Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4292Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432364032) }) = true
      norm_num [leaf4292Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4292CertificateValid :
    WideCertificateValid leaf4292Box leaf4292Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk187ValidityFacts chi241ValidityFacts
    leaf4292LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4292CoverageChecked :
    coverageCheck (innerAD leaf4292Box) leaf4292InnerLog = true := by
  rfl'

private theorem leaf4292InnerLogValid :
    leaf4292InnerLog.Valid 8 (innerAD leaf4292Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf4292CoverageChecked

private noncomputable def leaf4292InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629359/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4292InputLogOnePlusV_eq :
    leaf4292InputLogOnePlusV = outerEnclosure 24
      (leaf4292Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4292RoundedFacts : LeafRoundedFacts 8
    leaf4292Certificate.logOnePlusV leaf4292InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4292InputLogOnePlusV_eq }

private noncomputable def leaf4292Inputs : Inputs :=
  inputsOfCaches globalInput sk187RoundedInputs
    chi241InputQChi innerPair71Input
    leaf4292InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4292LowerChecked :
    lowerCheck 24 leaf4292Box leaf4292Inputs = true := by
  rfl'

private theorem leaf4292CoversExact : CoversExact 8
    leaf4292Box leaf4292Certificate leaf4292InnerLog leaf4292Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk187RoundedFacts chi241RoundedFacts
    innerPair71RoundedFacts leaf4292RoundedFacts (by rfl)

private theorem leaf4292FlatSound : Sound leaf4292Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4292CertificateValid
    leaf4292InnerLogValid leaf4292CoversExact leaf4292LowerChecked

private noncomputable def leaf4293Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (195/64), kHi := (49/16), chiLo := (1/4), chiHi := (33/128) }

private noncomputable def leaf4293Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871369/536870912) }, vSqrt := { lower := (65529/65536), upper := (1616904963/1616850944) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (945757369/536870912) }, upper := { exponent := 0, mantissa := (3665/2048) } }, logOuter := sk188LogOuterCertificate, logK := sk188LogKCertificate, logChi := chi241LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (3233755907/3233701888) } }, logDArg := sk188LogDArgCertificate }

private noncomputable def leaf4293InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf4293LocalValidity :
    LeafFacts leaf4293Box leaf4293Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4293Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (1616904963/1616850944) }) = true
      norm_num [leaf4293Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4293CertificateValid :
    WideCertificateValid leaf4293Box leaf4293Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk188ValidityFacts chi241ValidityFacts
    leaf4293LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4293CoverageChecked :
    coverageCheck (innerAD leaf4293Box) leaf4293InnerLog = true := by
  rfl'

private theorem leaf4293InnerLogValid :
    leaf4293InnerLog.Valid 8 (innerAD leaf4293Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf4293CoverageChecked

private noncomputable def leaf4293InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629361/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4293InputLogOnePlusV_eq :
    leaf4293InputLogOnePlusV = outerEnclosure 24
      (leaf4293Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4293RoundedFacts : LeafRoundedFacts 8
    leaf4293Certificate.logOnePlusV leaf4293InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4293InputLogOnePlusV_eq }

private noncomputable def leaf4293Inputs : Inputs :=
  inputsOfCaches globalInput sk188RoundedInputs
    chi241InputQChi innerPair71Input
    leaf4293InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4293LowerChecked :
    lowerCheck 24 leaf4293Box leaf4293Inputs = true := by
  rfl'

private theorem leaf4293CoversExact : CoversExact 8
    leaf4293Box leaf4293Certificate leaf4293InnerLog leaf4293Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk188RoundedFacts chi241RoundedFacts
    innerPair71RoundedFacts leaf4293RoundedFacts (by rfl)

private theorem leaf4293FlatSound : Sound leaf4293Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4293CertificateValid
    leaf4293InnerLogValid leaf4293CoversExact leaf4293LowerChecked

private noncomputable def leaf4294Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (193/64), chiLo := (33/128), chiHi := (17/64) }

private noncomputable def leaf4294Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871365/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432233984) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (952048445/536870912) }, upper := { exponent := 0, mantissa := (7377/4096) } }, logOuter := sk185LogOuterCertificate, logK := sk185LogKCertificate, logChi := chi242LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869155839/274864467968) } }, logDArg := sk185LogDArgCertificate }

private noncomputable def leaf4294InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf4294LocalValidity :
    LeafFacts leaf4294Box leaf4294Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4294Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432233984) }) = true
      norm_num [leaf4294Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4294CertificateValid :
    WideCertificateValid leaf4294Box leaf4294Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk185ValidityFacts chi242ValidityFacts
    leaf4294LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4294CoverageChecked :
    coverageCheck (innerAD leaf4294Box) leaf4294InnerLog = true := by
  rfl'

private theorem leaf4294InnerLogValid :
    leaf4294InnerLog.Valid 8 (innerAD leaf4294Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf4294CoverageChecked

private noncomputable def leaf4294InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629367/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4294InputLogOnePlusV_eq :
    leaf4294InputLogOnePlusV = outerEnclosure 24
      (leaf4294Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4294RoundedFacts : LeafRoundedFacts 8
    leaf4294Certificate.logOnePlusV leaf4294InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4294InputLogOnePlusV_eq }

private noncomputable def leaf4294Inputs : Inputs :=
  inputsOfCaches globalInput sk185RoundedInputs
    chi242InputQChi innerPair71Input
    leaf4294InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4294LowerChecked :
    lowerCheck 24 leaf4294Box leaf4294Inputs = true := by
  rfl'

private theorem leaf4294CoversExact : CoversExact 8
    leaf4294Box leaf4294Certificate leaf4294InnerLog leaf4294Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk185RoundedFacts chi242RoundedFacts
    innerPair71RoundedFacts leaf4294RoundedFacts (by rfl)

private theorem leaf4294FlatSound : Sound leaf4294Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4294CertificateValid
    leaf4294InnerLogValid leaf4294CoversExact leaf4294LowerChecked

private noncomputable def leaf4295Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (193/64), kHi := (97/32), chiLo := (33/128), chiHi := (17/64) }

private noncomputable def leaf4295Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871367/536870912) }, vSqrt := { lower := (65529/65536), upper := (15270769095/15270244352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (954210999/536870912) }, upper := { exponent := 0, mantissa := (3697/2048) } }, logOuter := sk186LogOuterCertificate, logK := sk186LogKCertificate, logChi := chi242LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (30541013447/30540488704) } }, logDArg := sk186LogDArgCertificate }

private noncomputable def leaf4295InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf4295LocalValidity :
    LeafFacts leaf4295Box leaf4295Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4295Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (15270769095/15270244352) }) = true
      norm_num [leaf4295Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4295CertificateValid :
    WideCertificateValid leaf4295Box leaf4295Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk186ValidityFacts chi242ValidityFacts
    leaf4295LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4295CoverageChecked :
    coverageCheck (innerAD leaf4295Box) leaf4295InnerLog = true := by
  rfl'

private theorem leaf4295InnerLogValid :
    leaf4295InnerLog.Valid 8 (innerAD leaf4295Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf4295CoverageChecked

private noncomputable def leaf4295InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629369/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4295InputLogOnePlusV_eq :
    leaf4295InputLogOnePlusV = outerEnclosure 24
      (leaf4295Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4295RoundedFacts : LeafRoundedFacts 8
    leaf4295Certificate.logOnePlusV leaf4295InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4295InputLogOnePlusV_eq }

private noncomputable def leaf4295Inputs : Inputs :=
  inputsOfCaches globalInput sk186RoundedInputs
    chi242InputQChi innerPair71Input
    leaf4295InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4295LowerChecked :
    lowerCheck 24 leaf4295Box leaf4295Inputs = true := by
  rfl'

private theorem leaf4295CoversExact : CoversExact 8
    leaf4295Box leaf4295Certificate leaf4295InnerLog leaf4295Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk186RoundedFacts chi242RoundedFacts
    innerPair71RoundedFacts leaf4295RoundedFacts (by rfl)

private theorem leaf4295FlatSound : Sound leaf4295Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4295CertificateValid
    leaf4295InnerLogValid leaf4295CoversExact leaf4295LowerChecked

private noncomputable def leaf4296Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (33/128), chiHi := (67/256) }

private noncomputable def leaf4296Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871241/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905371648) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (956373681/536870912) }, upper := { exponent := 0, mantissa := (7379/4096) } }, logOuter := sk134LogOuterCertificate, logK := sk134LogKCertificate, logChi := chi275LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811536213/45810743296) } }, logDArg := sk134LogDArgCertificate }

private noncomputable def leaf4296InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf4296LocalValidity :
    LeafFacts leaf4296Box leaf4296Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4296Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905371648) }) = true
      norm_num [leaf4296Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4296CertificateValid :
    WideCertificateValid leaf4296Box leaf4296Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk134ValidityFacts chi275ValidityFacts
    leaf4296LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4296CoverageChecked :
    coverageCheck (innerAD leaf4296Box) leaf4296InnerLog = true := by
  rfl'

private theorem leaf4296InnerLogValid :
    leaf4296InnerLog.Valid 8 (innerAD leaf4296Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf4296CoverageChecked

private noncomputable def leaf4296InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629371/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4296InputLogOnePlusV_eq :
    leaf4296InputLogOnePlusV = outerEnclosure 24
      (leaf4296Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4296RoundedFacts : LeafRoundedFacts 8
    leaf4296Certificate.logOnePlusV leaf4296InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4296InputLogOnePlusV_eq }

private noncomputable def leaf4296Inputs : Inputs :=
  inputsOfCaches globalInput sk134RoundedInputs
    chi275InputQChi innerPair71Input
    leaf4296InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4296LowerChecked :
    lowerCheck 24 leaf4296Box leaf4296Inputs = true := by
  rfl'

private theorem leaf4296CoversExact : CoversExact 8
    leaf4296Box leaf4296Certificate leaf4296InnerLog leaf4296Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk134RoundedFacts chi275RoundedFacts
    innerPair71RoundedFacts leaf4296RoundedFacts (by rfl)

private theorem leaf4296FlatSound : Sound leaf4296Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4296CertificateValid
    leaf4296InnerLogValid leaf4296CoversExact leaf4296LowerChecked

private noncomputable def leaf4297Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (67/256), chiHi := (17/64) }

private noncomputable def leaf4297Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871243/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68716064768) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (962730283/536870912) }, upper := { exponent := 0, mantissa := (1857/1024) } }, logOuter := sk134LogOuterCertificate, logK := sk134LogKCertificate, logChi := chi276LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434558463/137432129536) } }, logDArg := sk134LogDArgCertificate }

private noncomputable def leaf4297InnerLog : WideLogData :=
  innerPair226Data

set_option maxRecDepth 1000000 in
private theorem leaf4297LocalValidity :
    LeafFacts leaf4297Box leaf4297Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4297Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68716064768) }) = true
      norm_num [leaf4297Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4297CertificateValid :
    WideCertificateValid leaf4297Box leaf4297Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk134ValidityFacts chi276ValidityFacts
    leaf4297LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4297CoverageChecked :
    coverageCheck (innerAD leaf4297Box) leaf4297InnerLog = true := by
  rfl'

private theorem leaf4297InnerLogValid :
    leaf4297InnerLog.Valid 8 (innerAD leaf4297Box) :=
  wideLogDataValid_of_cachedCheck endpoint68PositiveFacts
    endpoint64PositiveFacts.valid leaf4297CoverageChecked

private noncomputable def leaf4297InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629377/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4297InputLogOnePlusV_eq :
    leaf4297InputLogOnePlusV = outerEnclosure 24
      (leaf4297Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4297RoundedFacts : LeafRoundedFacts 8
    leaf4297Certificate.logOnePlusV leaf4297InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4297InputLogOnePlusV_eq }

private noncomputable def leaf4297Inputs : Inputs :=
  inputsOfCaches globalInput sk134RoundedInputs
    chi276InputQChi innerPair226Input
    leaf4297InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4297LowerChecked :
    lowerCheck 24 leaf4297Box leaf4297Inputs = true := by
  rfl'

private theorem leaf4297CoversExact : CoversExact 8
    leaf4297Box leaf4297Certificate leaf4297InnerLog leaf4297Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk134RoundedFacts chi276RoundedFacts
    innerPair226RoundedFacts leaf4297RoundedFacts (by rfl)

private theorem leaf4297FlatSound : Sound leaf4297Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4297CertificateValid
    leaf4297InnerLogValid leaf4297CoversExact leaf4297LowerChecked

private noncomputable def leaf4298Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (197/64), chiLo := (1/4), chiHi := (33/128) }

private noncomputable def leaf4298Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871371/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432296448) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (947854391/536870912) }, upper := { exponent := 0, mantissa := (14693/8192) } }, logOuter := sk189LogOuterCertificate, logK := sk189LogKCertificate, logChi := chi241LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869218303/274864592896) } }, logDArg := sk189LogDArgCertificate }

private noncomputable def leaf4298InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf4298LocalValidity :
    LeafFacts leaf4298Box leaf4298Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4298Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432296448) }) = true
      norm_num [leaf4298Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4298CertificateValid :
    WideCertificateValid leaf4298Box leaf4298Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk189ValidityFacts chi241ValidityFacts
    leaf4298LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4298CoverageChecked :
    coverageCheck (innerAD leaf4298Box) leaf4298InnerLog = true := by
  rfl'

private theorem leaf4298InnerLogValid :
    leaf4298InnerLog.Valid 8 (innerAD leaf4298Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf4298CoverageChecked

private noncomputable def leaf4298InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629363/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4298InputLogOnePlusV_eq :
    leaf4298InputLogOnePlusV = outerEnclosure 24
      (leaf4298Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4298RoundedFacts : LeafRoundedFacts 8
    leaf4298Certificate.logOnePlusV leaf4298InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4298InputLogOnePlusV_eq }

private noncomputable def leaf4298Inputs : Inputs :=
  inputsOfCaches globalInput sk189RoundedInputs
    chi241InputQChi innerPair71Input
    leaf4298InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4298LowerChecked :
    lowerCheck 24 leaf4298Box leaf4298Inputs = true := by
  rfl'

private theorem leaf4298CoversExact : CoversExact 8
    leaf4298Box leaf4298Certificate leaf4298InnerLog leaf4298Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk189RoundedFacts chi241RoundedFacts
    innerPair71RoundedFacts leaf4298RoundedFacts (by rfl)

private theorem leaf4298FlatSound : Sound leaf4298Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4298CertificateValid
    leaf4298InnerLogValid leaf4298CoversExact leaf4298LowerChecked

private noncomputable def leaf4299Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (197/64), kHi := (99/32), chiLo := (1/4), chiHi := (33/128) }

private noncomputable def leaf4299Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871373/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432262656) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (949951413/536870912) }, upper := { exponent := 0, mantissa := (7363/4096) } }, logOuter := sk190LogOuterCertificate, logK := sk190LogKCertificate, logChi := chi241LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869184511/274864525312) } }, logDArg := sk190LogDArgCertificate }

private noncomputable def leaf4299InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf4299LocalValidity :
    LeafFacts leaf4299Box leaf4299Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4299Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432262656) }) = true
      norm_num [leaf4299Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4299CertificateValid :
    WideCertificateValid leaf4299Box leaf4299Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk190ValidityFacts chi241ValidityFacts
    leaf4299LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4299CoverageChecked :
    coverageCheck (innerAD leaf4299Box) leaf4299InnerLog = true := by
  rfl'

private theorem leaf4299InnerLogValid :
    leaf4299InnerLog.Valid 8 (innerAD leaf4299Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf4299CoverageChecked

private noncomputable def leaf4299InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629365/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4299InputLogOnePlusV_eq :
    leaf4299InputLogOnePlusV = outerEnclosure 24
      (leaf4299Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4299RoundedFacts : LeafRoundedFacts 8
    leaf4299Certificate.logOnePlusV leaf4299InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4299InputLogOnePlusV_eq }

private noncomputable def leaf4299Inputs : Inputs :=
  inputsOfCaches globalInput sk190RoundedInputs
    chi241InputQChi innerPair71Input
    leaf4299InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4299LowerChecked :
    lowerCheck 24 leaf4299Box leaf4299Inputs = true := by
  rfl'

private theorem leaf4299CoversExact : CoversExact 8
    leaf4299Box leaf4299Certificate leaf4299InnerLog leaf4299Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk190RoundedFacts chi241RoundedFacts
    innerPair71RoundedFacts leaf4299RoundedFacts (by rfl)

private theorem leaf4299FlatSound : Sound leaf4299Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4299CertificateValid
    leaf4299InnerLogValid leaf4299CoversExact leaf4299LowerChecked

private noncomputable def leaf4300Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (1/4), chiHi := (65/256) }

private noncomputable def leaf4300Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871241/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905382912) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (952048569/536870912) }, upper := { exponent := 0, mantissa := (3673/2048) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi277LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811547477/45810765824) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf4300InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf4300LocalValidity :
    LeafFacts leaf4300Box leaf4300Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4300Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905382912) }) = true
      norm_num [leaf4300Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4300CertificateValid :
    WideCertificateValid leaf4300Box leaf4300Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi277ValidityFacts
    leaf4300LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4300CoverageChecked :
    coverageCheck (innerAD leaf4300Box) leaf4300InnerLog = true := by
  rfl'

private theorem leaf4300InnerLogValid :
    leaf4300InnerLog.Valid 8 (innerAD leaf4300Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf4300CoverageChecked

private noncomputable def leaf4300InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629367/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4300InputLogOnePlusV_eq :
    leaf4300InputLogOnePlusV = outerEnclosure 24
      (leaf4300Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4300RoundedFacts : LeafRoundedFacts 8
    leaf4300Certificate.logOnePlusV leaf4300InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4300InputLogOnePlusV_eq }

private noncomputable def leaf4300Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi277InputQChi innerPair71Input
    leaf4300InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4300LowerChecked :
    lowerCheck 24 leaf4300Box leaf4300Inputs = true := by
  rfl'

private theorem leaf4300CoversExact : CoversExact 8
    leaf4300Box leaf4300Certificate leaf4300InnerLog leaf4300Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi277RoundedFacts
    innerPair71RoundedFacts leaf4300RoundedFacts (by rfl)

private theorem leaf4300FlatSound : Sound leaf4300Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4300CertificateValid
    leaf4300InnerLogValid leaf4300CoversExact leaf4300LowerChecked

private noncomputable def leaf4301Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (65/256), chiHi := (33/128) }

private noncomputable def leaf4301Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871243/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68716097536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (958536235/536870912) }, upper := { exponent := 0, mantissa := (1849/1024) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi278LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434591231/137432195072) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf4301InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf4301LocalValidity :
    LeafFacts leaf4301Box leaf4301Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4301Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68716097536) }) = true
      norm_num [leaf4301Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4301CertificateValid :
    WideCertificateValid leaf4301Box leaf4301Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi278ValidityFacts
    leaf4301LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4301CoverageChecked :
    coverageCheck (innerAD leaf4301Box) leaf4301InnerLog = true := by
  rfl'

private theorem leaf4301InnerLogValid :
    leaf4301InnerLog.Valid 8 (innerAD leaf4301Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf4301CoverageChecked

private noncomputable def leaf4301InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629373/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4301InputLogOnePlusV_eq :
    leaf4301InputLogOnePlusV = outerEnclosure 24
      (leaf4301Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4301RoundedFacts : LeafRoundedFacts 8
    leaf4301Certificate.logOnePlusV leaf4301InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4301InputLogOnePlusV_eq }

private noncomputable def leaf4301Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi278InputQChi innerPair71Input
    leaf4301InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4301LowerChecked :
    lowerCheck 24 leaf4301Box leaf4301Inputs = true := by
  rfl'

private theorem leaf4301CoversExact : CoversExact 8
    leaf4301Box leaf4301Certificate leaf4301InnerLog leaf4301Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi278RoundedFacts
    innerPair71RoundedFacts leaf4301RoundedFacts (by rfl)

private theorem leaf4301FlatSound : Sound leaf4301Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4301CertificateValid
    leaf4301InnerLogValid leaf4301CoversExact leaf4301LowerChecked

private noncomputable def leaf4302Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (33/128), chiHi := (67/256) }

private noncomputable def leaf4302Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871243/536870912) }, vSqrt := { lower := (65529/65536), upper := (13743698739/13743216128) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (960698791/536870912) }, upper := { exponent := 0, mantissa := (14825/8192) } }, logOuter := sk135LogOuterCertificate, logK := sk135LogKCertificate, logChi := chi275LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (27486914867/27486432256) } }, logDArg := sk135LogDArgCertificate }

private noncomputable def leaf4302InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf4302LocalValidity :
    LeafFacts leaf4302Box leaf4302Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4302Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (13743698739/13743216128) }) = true
      norm_num [leaf4302Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4302CertificateValid :
    WideCertificateValid leaf4302Box leaf4302Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk135ValidityFacts chi275ValidityFacts
    leaf4302LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4302CoverageChecked :
    coverageCheck (innerAD leaf4302Box) leaf4302InnerLog = true := by
  rfl'

private theorem leaf4302InnerLogValid :
    leaf4302InnerLog.Valid 8 (innerAD leaf4302Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf4302CoverageChecked

private noncomputable def leaf4302InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629375/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4302InputLogOnePlusV_eq :
    leaf4302InputLogOnePlusV = outerEnclosure 24
      (leaf4302Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4302RoundedFacts : LeafRoundedFacts 8
    leaf4302Certificate.logOnePlusV leaf4302InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4302InputLogOnePlusV_eq }

private noncomputable def leaf4302Inputs : Inputs :=
  inputsOfCaches globalInput sk135RoundedInputs
    chi275InputQChi innerPair71Input
    leaf4302InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4302LowerChecked :
    lowerCheck 24 leaf4302Box leaf4302Inputs = true := by
  rfl'

private theorem leaf4302CoversExact : CoversExact 8
    leaf4302Box leaf4302Certificate leaf4302InnerLog leaf4302Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk135RoundedFacts chi275RoundedFacts
    innerPair71RoundedFacts leaf4302RoundedFacts (by rfl)

private theorem leaf4302FlatSound : Sound leaf4302Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4302CertificateValid
    leaf4302InnerLogValid leaf4302CoversExact leaf4302LowerChecked

private noncomputable def leaf4303Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (67/256), chiHi := (17/64) }

private noncomputable def leaf4303Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871245/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68716029952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (967120925/536870912) }, upper := { exponent := 0, mantissa := (3731/2048) } }, logOuter := sk135LogOuterCertificate, logK := sk135LogKCertificate, logChi := chi276LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434523647/137432059904) } }, logDArg := sk135LogDArgCertificate }

private noncomputable def leaf4303InnerLog : WideLogData :=
  innerPair221Data

set_option maxRecDepth 1000000 in
private theorem leaf4303LocalValidity :
    LeafFacts leaf4303Box leaf4303Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4303Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68716029952) }) = true
      norm_num [leaf4303Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4303CertificateValid :
    WideCertificateValid leaf4303Box leaf4303Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk135ValidityFacts chi276ValidityFacts
    leaf4303LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4303CoverageChecked :
    coverageCheck (innerAD leaf4303Box) leaf4303InnerLog = true := by
  rfl'

private theorem leaf4303InnerLogValid :
    leaf4303InnerLog.Valid 8 (innerAD leaf4303Box) :=
  wideLogDataValid_of_cachedCheck endpoint67PositiveFacts
    endpoint64PositiveFacts.valid leaf4303CoverageChecked

private noncomputable def leaf4303InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814691/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4303InputLogOnePlusV_eq :
    leaf4303InputLogOnePlusV = outerEnclosure 24
      (leaf4303Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4303RoundedFacts : LeafRoundedFacts 8
    leaf4303Certificate.logOnePlusV leaf4303InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4303InputLogOnePlusV_eq }

private noncomputable def leaf4303Inputs : Inputs :=
  inputsOfCaches globalInput sk135RoundedInputs
    chi276InputQChi innerPair221Input
    leaf4303InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4303LowerChecked :
    lowerCheck 24 leaf4303Box leaf4303Inputs = true := by
  rfl'

private theorem leaf4303CoversExact : CoversExact 8
    leaf4303Box leaf4303Certificate leaf4303InnerLog leaf4303Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk135RoundedFacts chi276RoundedFacts
    innerPair221RoundedFacts leaf4303RoundedFacts (by rfl)

private theorem leaf4303FlatSound : Sound leaf4303Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4303CertificateValid
    leaf4303InnerLogValid leaf4303CoversExact leaf4303LowerChecked

private noncomputable def leaf4304Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (33/128), chiHi := (67/256) }

private noncomputable def leaf4304Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871245/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68716046336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (965023901/536870912) }, upper := { exponent := 0, mantissa := (3723/2048) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi275LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434540031/137432092672) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf4304InnerLog : WideLogData :=
  innerPair221Data

set_option maxRecDepth 1000000 in
private theorem leaf4304LocalValidity :
    LeafFacts leaf4304Box leaf4304Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4304Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68716046336) }) = true
      norm_num [leaf4304Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4304CertificateValid :
    WideCertificateValid leaf4304Box leaf4304Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi275ValidityFacts
    leaf4304LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4304CoverageChecked :
    coverageCheck (innerAD leaf4304Box) leaf4304InnerLog = true := by
  rfl'

private theorem leaf4304InnerLogValid :
    leaf4304InnerLog.Valid 8 (innerAD leaf4304Box) :=
  wideLogDataValid_of_cachedCheck endpoint67PositiveFacts
    endpoint64PositiveFacts.valid leaf4304CoverageChecked

private noncomputable def leaf4304InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907345/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4304InputLogOnePlusV_eq :
    leaf4304InputLogOnePlusV = outerEnclosure 24
      (leaf4304Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4304RoundedFacts : LeafRoundedFacts 8
    leaf4304Certificate.logOnePlusV leaf4304InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4304InputLogOnePlusV_eq }

private noncomputable def leaf4304Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi275InputQChi innerPair221Input
    leaf4304InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4304LowerChecked :
    lowerCheck 24 leaf4304Box leaf4304Inputs = true := by
  rfl'

private theorem leaf4304CoversExact : CoversExact 8
    leaf4304Box leaf4304Certificate leaf4304InnerLog leaf4304Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi275RoundedFacts
    innerPair221RoundedFacts leaf4304RoundedFacts (by rfl)

private theorem leaf4304FlatSound : Sound leaf4304Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4304CertificateValid
    leaf4304InnerLogValid leaf4304CoversExact leaf4304LowerChecked

private noncomputable def leaf4305Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (67/256), chiHi := (17/64) }

private noncomputable def leaf4305Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871247/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905331712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (971511567/536870912) }, upper := { exponent := 0, mantissa := (937/512) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi276LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811496277/45810663424) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf4305InnerLog : WideLogData :=
  innerPair220Data

set_option maxRecDepth 1000000 in
private theorem leaf4305LocalValidity :
    LeafFacts leaf4305Box leaf4305Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4305Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905331712) }) = true
      norm_num [leaf4305Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4305CertificateValid :
    WideCertificateValid leaf4305Box leaf4305Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi276ValidityFacts
    leaf4305LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4305CoverageChecked :
    coverageCheck (innerAD leaf4305Box) leaf4305InnerLog = true := by
  rfl'

private theorem leaf4305InnerLogValid :
    leaf4305InnerLog.Valid 8 (innerAD leaf4305Box) :=
  wideLogDataValid_of_cachedCheck endpoint67PositiveFacts
    endpoint61PositiveFacts.valid leaf4305CoverageChecked

private noncomputable def leaf4305InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814693/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4305InputLogOnePlusV_eq :
    leaf4305InputLogOnePlusV = outerEnclosure 24
      (leaf4305Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4305RoundedFacts : LeafRoundedFacts 8
    leaf4305Certificate.logOnePlusV leaf4305InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4305InputLogOnePlusV_eq }

private noncomputable def leaf4305Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi276InputQChi innerPair220Input
    leaf4305InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4305LowerChecked :
    lowerCheck 24 leaf4305Box leaf4305Inputs = true := by
  rfl'

private theorem leaf4305CoversExact : CoversExact 8
    leaf4305Box leaf4305Certificate leaf4305InnerLog leaf4305Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi276RoundedFacts
    innerPair220RoundedFacts leaf4305RoundedFacts (by rfl)

private theorem leaf4305FlatSound : Sound leaf4305Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4305CertificateValid
    leaf4305InnerLogValid leaf4305CoversExact leaf4305LowerChecked

private noncomputable def leaf4306Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (17/64), chiHi := (69/256) }

private noncomputable def leaf4306Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871243/536870912) }, vSqrt := { lower := (65529/65536), upper := (13743698739/13743209984) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (964630711/536870912) }, upper := { exponent := 0, mantissa := (14885/8192) } }, logOuter := sk133LogOuterCertificate, logK := sk133LogKCertificate, logChi := chi257LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (27486908723/27486419968) } }, logDArg := sk133LogDArgCertificate }

private noncomputable def leaf4306InnerLog : WideLogData :=
  innerPair226Data

set_option maxRecDepth 1000000 in
private theorem leaf4306LocalValidity :
    LeafFacts leaf4306Box leaf4306Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4306Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (13743698739/13743209984) }) = true
      norm_num [leaf4306Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4306CertificateValid :
    WideCertificateValid leaf4306Box leaf4306Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk133ValidityFacts chi257ValidityFacts
    leaf4306LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4306CoverageChecked :
    coverageCheck (innerAD leaf4306Box) leaf4306InnerLog = true := by
  rfl'

private theorem leaf4306InnerLogValid :
    leaf4306InnerLog.Valid 8 (innerAD leaf4306Box) :=
  wideLogDataValid_of_cachedCheck endpoint68PositiveFacts
    endpoint64PositiveFacts.valid leaf4306CoverageChecked

private noncomputable def leaf4306InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629379/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4306InputLogOnePlusV_eq :
    leaf4306InputLogOnePlusV = outerEnclosure 24
      (leaf4306Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4306RoundedFacts : LeafRoundedFacts 8
    leaf4306Certificate.logOnePlusV leaf4306InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4306InputLogOnePlusV_eq }

private noncomputable def leaf4306Inputs : Inputs :=
  inputsOfCaches globalInput sk133RoundedInputs
    chi257InputQChi innerPair226Input
    leaf4306InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4306LowerChecked :
    lowerCheck 24 leaf4306Box leaf4306Inputs = true := by
  rfl'

private theorem leaf4306CoversExact : CoversExact 8
    leaf4306Box leaf4306Certificate leaf4306InnerLog leaf4306Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk133RoundedFacts chi257RoundedFacts
    innerPair226RoundedFacts leaf4306RoundedFacts (by rfl)

private theorem leaf4306FlatSound : Sound leaf4306Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4306CertificateValid
    leaf4306InnerLogValid leaf4306CoversExact leaf4306LowerChecked

private noncomputable def leaf4307Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (69/256), chiHi := (35/128) }

private noncomputable def leaf4307Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871245/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68716000256) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (970921781/536870912) }, upper := { exponent := 0, mantissa := (7491/4096) } }, logOuter := sk133LogOuterCertificate, logK := sk133LogKCertificate, logChi := chi258LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434493951/137432000512) } }, logDArg := sk133LogDArgCertificate }

private noncomputable def leaf4307InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf4307LocalValidity :
    LeafFacts leaf4307Box leaf4307Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4307Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68716000256) }) = true
      norm_num [leaf4307Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4307CertificateValid :
    WideCertificateValid leaf4307Box leaf4307Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk133ValidityFacts chi258ValidityFacts
    leaf4307LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4307CoverageChecked :
    coverageCheck (innerAD leaf4307Box) leaf4307InnerLog = true := by
  rfl'

private theorem leaf4307InnerLogValid :
    leaf4307InnerLog.Valid 8 (innerAD leaf4307Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf4307CoverageChecked

private noncomputable def leaf4307InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629385/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4307InputLogOnePlusV_eq :
    leaf4307InputLogOnePlusV = outerEnclosure 24
      (leaf4307Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4307RoundedFacts : LeafRoundedFacts 8
    leaf4307Certificate.logOnePlusV leaf4307InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4307InputLogOnePlusV_eq }

private noncomputable def leaf4307Inputs : Inputs :=
  inputsOfCaches globalInput sk133RoundedInputs
    chi258InputQChi innerPair72Input
    leaf4307InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4307LowerChecked :
    lowerCheck 24 leaf4307Box leaf4307Inputs = true := by
  rfl'

private theorem leaf4307CoversExact : CoversExact 8
    leaf4307Box leaf4307Certificate leaf4307InnerLog leaf4307Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk133RoundedFacts chi258RoundedFacts
    innerPair72RoundedFacts leaf4307RoundedFacts (by rfl)

private theorem leaf4307FlatSound : Sound leaf4307Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4307CertificateValid
    leaf4307InnerLogValid leaf4307CoversExact leaf4307LowerChecked

private noncomputable def leaf4308Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (17/64), chiHi := (69/256) }

private noncomputable def leaf4308Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871245/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68716014592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (969086885/536870912) }, upper := { exponent := 0, mantissa := (7477/4096) } }, logOuter := sk134LogOuterCertificate, logK := sk134LogKCertificate, logChi := chi257LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434508287/137432029184) } }, logDArg := sk134LogDArgCertificate }

private noncomputable def leaf4308InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf4308LocalValidity :
    LeafFacts leaf4308Box leaf4308Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4308Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68716014592) }) = true
      norm_num [leaf4308Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4308CertificateValid :
    WideCertificateValid leaf4308Box leaf4308Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk134ValidityFacts chi257ValidityFacts
    leaf4308LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4308CoverageChecked :
    coverageCheck (innerAD leaf4308Box) leaf4308InnerLog = true := by
  rfl'

private theorem leaf4308InnerLogValid :
    leaf4308InnerLog.Valid 8 (innerAD leaf4308Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf4308CoverageChecked

private noncomputable def leaf4308InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629383/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4308InputLogOnePlusV_eq :
    leaf4308InputLogOnePlusV = outerEnclosure 24
      (leaf4308Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4308RoundedFacts : LeafRoundedFacts 8
    leaf4308Certificate.logOnePlusV leaf4308InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4308InputLogOnePlusV_eq }

private noncomputable def leaf4308Inputs : Inputs :=
  inputsOfCaches globalInput sk134RoundedInputs
    chi257InputQChi innerPair72Input
    leaf4308InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4308LowerChecked :
    lowerCheck 24 leaf4308Box leaf4308Inputs = true := by
  rfl'

private theorem leaf4308CoversExact : CoversExact 8
    leaf4308Box leaf4308Certificate leaf4308InnerLog leaf4308Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk134RoundedFacts chi257RoundedFacts
    innerPair72RoundedFacts leaf4308RoundedFacts (by rfl)

private theorem leaf4308FlatSound : Sound leaf4308Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4308CertificateValid
    leaf4308InnerLogValid leaf4308CoversExact leaf4308LowerChecked

private noncomputable def leaf4309Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (69/256), chiHi := (35/128) }

private noncomputable def leaf4309Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871247/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905321472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (975443487/536870912) }, upper := { exponent := 0, mantissa := (3763/2048) } }, logOuter := sk134LogOuterCertificate, logK := sk134LogKCertificate, logChi := chi258LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811486037/45810642944) } }, logDArg := sk134LogDArgCertificate }

private noncomputable def leaf4309InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf4309LocalValidity :
    LeafFacts leaf4309Box leaf4309Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4309Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905321472) }) = true
      norm_num [leaf4309Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4309CertificateValid :
    WideCertificateValid leaf4309Box leaf4309Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk134ValidityFacts chi258ValidityFacts
    leaf4309LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4309CoverageChecked :
    coverageCheck (innerAD leaf4309Box) leaf4309InnerLog = true := by
  rfl'

private theorem leaf4309InnerLogValid :
    leaf4309InnerLog.Valid 8 (innerAD leaf4309Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf4309CoverageChecked

private noncomputable def leaf4309InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814695/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4309InputLogOnePlusV_eq :
    leaf4309InputLogOnePlusV = outerEnclosure 24
      (leaf4309Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4309RoundedFacts : LeafRoundedFacts 8
    leaf4309Certificate.logOnePlusV leaf4309InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4309InputLogOnePlusV_eq }

private noncomputable def leaf4309Inputs : Inputs :=
  inputsOfCaches globalInput sk134RoundedInputs
    chi258InputQChi innerPair91Input
    leaf4309InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4309LowerChecked :
    lowerCheck 24 leaf4309Box leaf4309Inputs = true := by
  rfl'

private theorem leaf4309CoversExact : CoversExact 8
    leaf4309Box leaf4309Certificate leaf4309InnerLog leaf4309Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk134RoundedFacts chi258RoundedFacts
    innerPair91RoundedFacts leaf4309RoundedFacts (by rfl)

private theorem leaf4309FlatSound : Sound leaf4309Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4309CertificateValid
    leaf4309InnerLogValid leaf4309CoversExact leaf4309LowerChecked

private noncomputable def leaf4310Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (35/128), chiHi := (71/256) }

private noncomputable def leaf4310Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871247/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905316864) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (977212851/536870912) }, upper := { exponent := 0, mantissa := (15079/8192) } }, logOuter := sk133LogOuterCertificate, logK := sk133LogKCertificate, logChi := chi279LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811481429/45810633728) } }, logDArg := sk133LogDArgCertificate }

private noncomputable def leaf4310InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf4310LocalValidity :
    LeafFacts leaf4310Box leaf4310Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4310Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905316864) }) = true
      norm_num [leaf4310Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4310CertificateValid :
    WideCertificateValid leaf4310Box leaf4310Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk133ValidityFacts chi279ValidityFacts
    leaf4310LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4310CoverageChecked :
    coverageCheck (innerAD leaf4310Box) leaf4310InnerLog = true := by
  rfl'

private theorem leaf4310InnerLogValid :
    leaf4310InnerLog.Valid 8 (innerAD leaf4310Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf4310CoverageChecked

private noncomputable def leaf4310InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629391/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4310InputLogOnePlusV_eq :
    leaf4310InputLogOnePlusV = outerEnclosure 24
      (leaf4310Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4310RoundedFacts : LeafRoundedFacts 8
    leaf4310Certificate.logOnePlusV leaf4310InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4310InputLogOnePlusV_eq }

private noncomputable def leaf4310Inputs : Inputs :=
  inputsOfCaches globalInput sk133RoundedInputs
    chi279InputQChi innerPair91Input
    leaf4310InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4310LowerChecked :
    lowerCheck 24 leaf4310Box leaf4310Inputs = true := by
  rfl'

private theorem leaf4310CoversExact : CoversExact 8
    leaf4310Box leaf4310Certificate leaf4310InnerLog leaf4310Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk133RoundedFacts chi279RoundedFacts
    innerPair91RoundedFacts leaf4310RoundedFacts (by rfl)

private theorem leaf4310FlatSound : Sound leaf4310Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4310CertificateValid
    leaf4310InnerLogValid leaf4310CoversExact leaf4310LowerChecked

private noncomputable def leaf4311Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (71/256), chiHi := (9/32) }

private noncomputable def leaf4311Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871249/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715900928) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (983503921/536870912) }, upper := { exponent := 0, mantissa := (1897/1024) } }, logOuter := sk133LogOuterCertificate, logK := sk133LogKCertificate, logChi := chi280LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434394623/137431801856) } }, logDArg := sk133LogDArgCertificate }

private noncomputable def leaf4311InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf4311LocalValidity :
    LeafFacts leaf4311Box leaf4311Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4311Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715900928) }) = true
      norm_num [leaf4311Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4311CertificateValid :
    WideCertificateValid leaf4311Box leaf4311Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk133ValidityFacts chi280ValidityFacts
    leaf4311LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4311CoverageChecked :
    coverageCheck (innerAD leaf4311Box) leaf4311InnerLog = true := by
  rfl'

private theorem leaf4311InnerLogValid :
    leaf4311InnerLog.Valid 8 (innerAD leaf4311Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf4311CoverageChecked

private noncomputable def leaf4311InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629397/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4311InputLogOnePlusV_eq :
    leaf4311InputLogOnePlusV = outerEnclosure 24
      (leaf4311Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4311RoundedFacts : LeafRoundedFacts 8
    leaf4311Certificate.logOnePlusV leaf4311InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4311InputLogOnePlusV_eq }

private noncomputable def leaf4311Inputs : Inputs :=
  inputsOfCaches globalInput sk133RoundedInputs
    chi280InputQChi innerPair91Input
    leaf4311InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4311LowerChecked :
    lowerCheck 24 leaf4311Box leaf4311Inputs = true := by
  rfl'

private theorem leaf4311CoversExact : CoversExact 8
    leaf4311Box leaf4311Certificate leaf4311InnerLog leaf4311Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk133RoundedFacts chi280RoundedFacts
    innerPair91RoundedFacts leaf4311RoundedFacts (by rfl)

private theorem leaf4311FlatSound : Sound leaf4311Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4311CertificateValid
    leaf4311InnerLogValid leaf4311CoversExact leaf4311LowerChecked

private noncomputable def leaf4312Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (35/128), chiHi := (71/256) }

private noncomputable def leaf4312Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871249/536870912) }, vSqrt := { lower := (65529/65536), upper := (13743698739/13743182848) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (981800089/536870912) }, upper := { exponent := 0, mantissa := (7575/4096) } }, logOuter := sk134LogOuterCertificate, logK := sk134LogKCertificate, logChi := chi279LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (27486881587/27486365696) } }, logDArg := sk134LogDArgCertificate }

private noncomputable def leaf4312InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf4312LocalValidity :
    LeafFacts leaf4312Box leaf4312Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4312Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (13743698739/13743182848) }) = true
      norm_num [leaf4312Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4312CertificateValid :
    WideCertificateValid leaf4312Box leaf4312Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk134ValidityFacts chi279ValidityFacts
    leaf4312LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4312CoverageChecked :
    coverageCheck (innerAD leaf4312Box) leaf4312InnerLog = true := by
  rfl'

private theorem leaf4312InnerLogValid :
    leaf4312InnerLog.Valid 8 (innerAD leaf4312Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf4312CoverageChecked

private noncomputable def leaf4312InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907349/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4312InputLogOnePlusV_eq :
    leaf4312InputLogOnePlusV = outerEnclosure 24
      (leaf4312Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4312RoundedFacts : LeafRoundedFacts 8
    leaf4312Certificate.logOnePlusV leaf4312InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4312InputLogOnePlusV_eq }

private noncomputable def leaf4312Inputs : Inputs :=
  inputsOfCaches globalInput sk134RoundedInputs
    chi279InputQChi innerPair91Input
    leaf4312InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4312LowerChecked :
    lowerCheck 24 leaf4312Box leaf4312Inputs = true := by
  rfl'

private theorem leaf4312CoversExact : CoversExact 8
    leaf4312Box leaf4312Certificate leaf4312InnerLog leaf4312Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk134RoundedFacts chi279RoundedFacts
    innerPair91RoundedFacts leaf4312RoundedFacts (by rfl)

private theorem leaf4312FlatSound : Sound leaf4312Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4312CertificateValid
    leaf4312InnerLogValid leaf4312CoversExact leaf4312LowerChecked

private noncomputable def leaf4313Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (71/256), chiHi := (9/32) }

private noncomputable def leaf4313Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871251/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715864064) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (988156691/536870912) }, upper := { exponent := 0, mantissa := (953/512) } }, logOuter := sk134LogOuterCertificate, logK := sk134LogKCertificate, logChi := chi280LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434357759/137431728128) } }, logDArg := sk134LogDArgCertificate }

private noncomputable def leaf4313InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf4313LocalValidity :
    LeafFacts leaf4313Box leaf4313Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4313Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715864064) }) = true
      norm_num [leaf4313Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4313CertificateValid :
    WideCertificateValid leaf4313Box leaf4313Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk134ValidityFacts chi280ValidityFacts
    leaf4313LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4313CoverageChecked :
    coverageCheck (innerAD leaf4313Box) leaf4313InnerLog = true := by
  rfl'

private theorem leaf4313InnerLogValid :
    leaf4313InnerLog.Valid 8 (innerAD leaf4313Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf4313CoverageChecked

private noncomputable def leaf4313InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814701/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4313InputLogOnePlusV_eq :
    leaf4313InputLogOnePlusV = outerEnclosure 24
      (leaf4313Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4313RoundedFacts : LeafRoundedFacts 8
    leaf4313Certificate.logOnePlusV leaf4313InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4313InputLogOnePlusV_eq }

private noncomputable def leaf4313Inputs : Inputs :=
  inputsOfCaches globalInput sk134RoundedInputs
    chi280InputQChi innerPair91Input
    leaf4313InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4313LowerChecked :
    lowerCheck 24 leaf4313Box leaf4313Inputs = true := by
  rfl'

private theorem leaf4313CoversExact : CoversExact 8
    leaf4313Box leaf4313Certificate leaf4313InnerLog leaf4313Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk134RoundedFacts chi280RoundedFacts
    innerPair91RoundedFacts leaf4313RoundedFacts (by rfl)

private theorem leaf4313FlatSound : Sound leaf4313Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4313CertificateValid
    leaf4313InnerLogValid leaf4313CoversExact leaf4313LowerChecked

private noncomputable def leaf4314Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (17/64), chiHi := (69/256) }

private noncomputable def leaf4314Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871247/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715979264) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (973543059/536870912) }, upper := { exponent := 0, mantissa := (15023/8192) } }, logOuter := sk135LogOuterCertificate, logK := sk135LogKCertificate, logChi := chi257LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434472959/137431958528) } }, logDArg := sk135LogDArgCertificate }

private noncomputable def leaf4314InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf4314LocalValidity :
    LeafFacts leaf4314Box leaf4314Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4314Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715979264) }) = true
      norm_num [leaf4314Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4314CertificateValid :
    WideCertificateValid leaf4314Box leaf4314Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk135ValidityFacts chi257ValidityFacts
    leaf4314LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4314CoverageChecked :
    coverageCheck (innerAD leaf4314Box) leaf4314InnerLog = true := by
  rfl'

private theorem leaf4314InnerLogValid :
    leaf4314InnerLog.Valid 8 (innerAD leaf4314Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf4314CoverageChecked

private noncomputable def leaf4314InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907347/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4314InputLogOnePlusV_eq :
    leaf4314InputLogOnePlusV = outerEnclosure 24
      (leaf4314Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4314RoundedFacts : LeafRoundedFacts 8
    leaf4314Certificate.logOnePlusV leaf4314InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4314InputLogOnePlusV_eq }

private noncomputable def leaf4314Inputs : Inputs :=
  inputsOfCaches globalInput sk135RoundedInputs
    chi257InputQChi innerPair91Input
    leaf4314InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4314LowerChecked :
    lowerCheck 24 leaf4314Box leaf4314Inputs = true := by
  rfl'

private theorem leaf4314CoversExact : CoversExact 8
    leaf4314Box leaf4314Certificate leaf4314InnerLog leaf4314Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk135RoundedFacts chi257RoundedFacts
    innerPair91RoundedFacts leaf4314RoundedFacts (by rfl)

private theorem leaf4314FlatSound : Sound leaf4314Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4314CertificateValid
    leaf4314InnerLogValid leaf4314CoversExact leaf4314LowerChecked

private noncomputable def leaf4315Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (69/256), chiHi := (35/128) }

private noncomputable def leaf4315Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871249/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715928576) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (979965193/536870912) }, upper := { exponent := 0, mantissa := (7561/4096) } }, logOuter := sk135LogOuterCertificate, logK := sk135LogKCertificate, logChi := chi258LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434422271/137431857152) } }, logDArg := sk135LogDArgCertificate }

private noncomputable def leaf4315InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf4315LocalValidity :
    LeafFacts leaf4315Box leaf4315Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4315Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715928576) }) = true
      norm_num [leaf4315Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4315CertificateValid :
    WideCertificateValid leaf4315Box leaf4315Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk135ValidityFacts chi258ValidityFacts
    leaf4315LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4315CoverageChecked :
    coverageCheck (innerAD leaf4315Box) leaf4315InnerLog = true := by
  rfl'

private theorem leaf4315InnerLogValid :
    leaf4315InnerLog.Valid 8 (innerAD leaf4315Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf4315CoverageChecked

private noncomputable def leaf4315InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814697/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4315InputLogOnePlusV_eq :
    leaf4315InputLogOnePlusV = outerEnclosure 24
      (leaf4315Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4315RoundedFacts : LeafRoundedFacts 8
    leaf4315Certificate.logOnePlusV leaf4315InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4315InputLogOnePlusV_eq }

private noncomputable def leaf4315Inputs : Inputs :=
  inputsOfCaches globalInput sk135RoundedInputs
    chi258InputQChi innerPair91Input
    leaf4315InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4315LowerChecked :
    lowerCheck 24 leaf4315Box leaf4315Inputs = true := by
  rfl'

private theorem leaf4315CoversExact : CoversExact 8
    leaf4315Box leaf4315Certificate leaf4315InnerLog leaf4315Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk135RoundedFacts chi258RoundedFacts
    innerPair91RoundedFacts leaf4315RoundedFacts (by rfl)

private theorem leaf4315FlatSound : Sound leaf4315Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4315CertificateValid
    leaf4315InnerLogValid leaf4315CoversExact leaf4315LowerChecked

private noncomputable def leaf4316Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (17/64), chiHi := (69/256) }

private noncomputable def leaf4316Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871249/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715943936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (977999233/536870912) }, upper := { exponent := 0, mantissa := (3773/2048) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi257LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434437631/137431887872) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf4316InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf4316LocalValidity :
    LeafFacts leaf4316Box leaf4316Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4316Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715943936) }) = true
      norm_num [leaf4316Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4316CertificateValid :
    WideCertificateValid leaf4316Box leaf4316Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi257ValidityFacts
    leaf4316LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4316CoverageChecked :
    coverageCheck (innerAD leaf4316Box) leaf4316InnerLog = true := by
  rfl'

private theorem leaf4316InnerLogValid :
    leaf4316InnerLog.Valid 8 (innerAD leaf4316Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf4316CoverageChecked

private noncomputable def leaf4316InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (726837/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf4316InputLogOnePlusV_eq :
    leaf4316InputLogOnePlusV = outerEnclosure 24
      (leaf4316Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4316RoundedFacts : LeafRoundedFacts 8
    leaf4316Certificate.logOnePlusV leaf4316InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4316InputLogOnePlusV_eq }

private noncomputable def leaf4316Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi257InputQChi innerPair91Input
    leaf4316InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4316LowerChecked :
    lowerCheck 24 leaf4316Box leaf4316Inputs = true := by
  rfl'

private theorem leaf4316CoversExact : CoversExact 8
    leaf4316Box leaf4316Certificate leaf4316InnerLog leaf4316Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi257RoundedFacts
    innerPair91RoundedFacts leaf4316RoundedFacts (by rfl)

private theorem leaf4316FlatSound : Sound leaf4316Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4316CertificateValid
    leaf4316InnerLogValid leaf4316CoversExact leaf4316LowerChecked

private noncomputable def leaf4317Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (69/256), chiHi := (35/128) }

private noncomputable def leaf4317Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871251/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715892736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (984486899/536870912) }, upper := { exponent := 0, mantissa := (1899/1024) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi258LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434386431/137431785472) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf4317InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf4317LocalValidity :
    LeafFacts leaf4317Box leaf4317Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4317Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715892736) }) = true
      norm_num [leaf4317Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4317CertificateValid :
    WideCertificateValid leaf4317Box leaf4317Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi258ValidityFacts
    leaf4317LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4317CoverageChecked :
    coverageCheck (innerAD leaf4317Box) leaf4317InnerLog = true := by
  rfl'

private theorem leaf4317InnerLogValid :
    leaf4317InnerLog.Valid 8 (innerAD leaf4317Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf4317CoverageChecked

private noncomputable def leaf4317InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814699/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4317InputLogOnePlusV_eq :
    leaf4317InputLogOnePlusV = outerEnclosure 24
      (leaf4317Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4317RoundedFacts : LeafRoundedFacts 8
    leaf4317Certificate.logOnePlusV leaf4317InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4317InputLogOnePlusV_eq }

private noncomputable def leaf4317Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi258InputQChi innerPair91Input
    leaf4317InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4317LowerChecked :
    lowerCheck 24 leaf4317Box leaf4317Inputs = true := by
  rfl'

private theorem leaf4317CoversExact : CoversExact 8
    leaf4317Box leaf4317Certificate leaf4317InnerLog leaf4317Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi258RoundedFacts
    innerPair91RoundedFacts leaf4317RoundedFacts (by rfl)

private theorem leaf4317FlatSound : Sound leaf4317Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4317CertificateValid
    leaf4317InnerLogValid leaf4317CoversExact leaf4317LowerChecked

private noncomputable def leaf4318Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (35/128), chiHi := (71/256) }

private noncomputable def leaf4318Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871251/536870912) }, vSqrt := { lower := (65529/65536), upper := (4042264335/4042110464) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (986387327/536870912) }, upper := { exponent := 0, mantissa := (15221/8192) } }, logOuter := sk135LogOuterCertificate, logK := sk135LogKCertificate, logChi := chi279LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (8084374799/8084220928) } }, logDArg := sk135LogDArgCertificate }

private noncomputable def leaf4318InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf4318LocalValidity :
    LeafFacts leaf4318Box leaf4318Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4318Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4042264335/4042110464) }) = true
      norm_num [leaf4318Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4318CertificateValid :
    WideCertificateValid leaf4318Box leaf4318Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk135ValidityFacts chi279ValidityFacts
    leaf4318LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4318CoverageChecked :
    coverageCheck (innerAD leaf4318Box) leaf4318InnerLog = true := by
  rfl'

private theorem leaf4318InnerLogValid :
    leaf4318InnerLog.Valid 8 (innerAD leaf4318Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf4318CoverageChecked

private noncomputable def leaf4318InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453675/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf4318InputLogOnePlusV_eq :
    leaf4318InputLogOnePlusV = outerEnclosure 24
      (leaf4318Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4318RoundedFacts : LeafRoundedFacts 8
    leaf4318Certificate.logOnePlusV leaf4318InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4318InputLogOnePlusV_eq }

private noncomputable def leaf4318Inputs : Inputs :=
  inputsOfCaches globalInput sk135RoundedInputs
    chi279InputQChi innerPair91Input
    leaf4318InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4318LowerChecked :
    lowerCheck 24 leaf4318Box leaf4318Inputs = true := by
  rfl'

private theorem leaf4318CoversExact : CoversExact 8
    leaf4318Box leaf4318Certificate leaf4318InnerLog leaf4318Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk135RoundedFacts chi279RoundedFacts
    innerPair91RoundedFacts leaf4318RoundedFacts (by rfl)

private theorem leaf4318FlatSound : Sound leaf4318Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4318CertificateValid
    leaf4318InnerLogValid leaf4318CoversExact leaf4318LowerChecked

private noncomputable def leaf4319Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (71/256), chiHi := (9/32) }

private noncomputable def leaf4319Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871253/536870912) }, vSqrt := { lower := (65529/65536), upper := (13743698739/13743165440) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (992809461/536870912) }, upper := { exponent := 0, mantissa := (1915/1024) } }, logOuter := sk135LogOuterCertificate, logK := sk135LogKCertificate, logChi := chi280LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (27486864179/27486330880) } }, logDArg := sk135LogDArgCertificate }

private noncomputable def leaf4319InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf4319LocalValidity :
    LeafFacts leaf4319Box leaf4319Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4319Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (13743698739/13743165440) }) = true
      norm_num [leaf4319Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4319CertificateValid :
    WideCertificateValid leaf4319Box leaf4319Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk135ValidityFacts chi280ValidityFacts
    leaf4319LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4319CoverageChecked :
    coverageCheck (innerAD leaf4319Box) leaf4319InnerLog = true := by
  rfl'

private theorem leaf4319InnerLogValid :
    leaf4319InnerLog.Valid 8 (innerAD leaf4319Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf4319CoverageChecked

private noncomputable def leaf4319InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814703/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4319InputLogOnePlusV_eq :
    leaf4319InputLogOnePlusV = outerEnclosure 24
      (leaf4319Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4319RoundedFacts : LeafRoundedFacts 8
    leaf4319Certificate.logOnePlusV leaf4319InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4319InputLogOnePlusV_eq }

private noncomputable def leaf4319Inputs : Inputs :=
  inputsOfCaches globalInput sk135RoundedInputs
    chi280InputQChi innerPair91Input
    leaf4319InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4319LowerChecked :
    lowerCheck 24 leaf4319Box leaf4319Inputs = true := by
  rfl'

private theorem leaf4319CoversExact : CoversExact 8
    leaf4319Box leaf4319Certificate leaf4319InnerLog leaf4319Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk135RoundedFacts chi280RoundedFacts
    innerPair91RoundedFacts leaf4319RoundedFacts (by rfl)

private theorem leaf4319FlatSound : Sound leaf4319Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4319CertificateValid
    leaf4319InnerLogValid leaf4319CoversExact leaf4319LowerChecked

private noncomputable def leaf4320Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (35/128), chiHi := (71/256) }

private noncomputable def leaf4320Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871253/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905280512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (990974565/536870912) }, upper := { exponent := 0, mantissa := (3823/2048) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi279LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811445077/45810561024) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf4320InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf4320LocalValidity :
    LeafFacts leaf4320Box leaf4320Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4320Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905280512) }) = true
      norm_num [leaf4320Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4320CertificateValid :
    WideCertificateValid leaf4320Box leaf4320Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi279ValidityFacts
    leaf4320LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4320CoverageChecked :
    coverageCheck (innerAD leaf4320Box) leaf4320InnerLog = true := by
  rfl'

private theorem leaf4320InnerLogValid :
    leaf4320InnerLog.Valid 8 (innerAD leaf4320Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf4320CoverageChecked

private noncomputable def leaf4320InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629405/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4320InputLogOnePlusV_eq :
    leaf4320InputLogOnePlusV = outerEnclosure 24
      (leaf4320Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4320RoundedFacts : LeafRoundedFacts 8
    leaf4320Certificate.logOnePlusV leaf4320InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4320InputLogOnePlusV_eq }

private noncomputable def leaf4320Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi279InputQChi innerPair91Input
    leaf4320InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4320LowerChecked :
    lowerCheck 24 leaf4320Box leaf4320Inputs = true := by
  rfl'

private theorem leaf4320CoversExact : CoversExact 8
    leaf4320Box leaf4320Certificate leaf4320InnerLog leaf4320Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi279RoundedFacts
    innerPair91RoundedFacts leaf4320RoundedFacts (by rfl)

private theorem leaf4320FlatSound : Sound leaf4320Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4320CertificateValid
    leaf4320InnerLogValid leaf4320CoversExact leaf4320LowerChecked

private noncomputable def leaf4321Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (71/256), chiHi := (9/32) }

private noncomputable def leaf4321Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871255/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715790336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (997462231/536870912) }, upper := { exponent := 0, mantissa := (481/256) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi280LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434284031/137431580672) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf4321InnerLog : WideLogData :=
  innerPair199Data

set_option maxRecDepth 1000000 in
private theorem leaf4321LocalValidity :
    LeafFacts leaf4321Box leaf4321Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4321Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715790336) }) = true
      norm_num [leaf4321Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4321CertificateValid :
    WideCertificateValid leaf4321Box leaf4321Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi280ValidityFacts
    leaf4321LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4321CoverageChecked :
    coverageCheck (innerAD leaf4321Box) leaf4321InnerLog = true := by
  rfl'

private theorem leaf4321InnerLogValid :
    leaf4321InnerLog.Valid 8 (innerAD leaf4321Box) :=
  wideLogDataValid_of_cachedCheck endpoint61PositiveFacts
    endpoint69PositiveFacts.valid leaf4321CoverageChecked

private noncomputable def leaf4321InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629411/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4321InputLogOnePlusV_eq :
    leaf4321InputLogOnePlusV = outerEnclosure 24
      (leaf4321Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4321RoundedFacts : LeafRoundedFacts 8
    leaf4321Certificate.logOnePlusV leaf4321InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4321InputLogOnePlusV_eq }

private noncomputable def leaf4321Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi280InputQChi innerPair199Input
    leaf4321InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4321LowerChecked :
    lowerCheck 24 leaf4321Box leaf4321Inputs = true := by
  rfl'

private theorem leaf4321CoversExact : CoversExact 8
    leaf4321Box leaf4321Certificate leaf4321InnerLog leaf4321Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi280RoundedFacts
    innerPair199RoundedFacts leaf4321RoundedFacts (by rfl)

private theorem leaf4321FlatSound : Sound leaf4321Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4321CertificateValid
    leaf4321InnerLogValid leaf4321CoversExact leaf4321LowerChecked

private noncomputable def leaf4322Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (1/4), chiHi := (65/256) }

private noncomputable def leaf4322Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871243/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68716115456) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (956242615/536870912) }, upper := { exponent := 0, mantissa := (14757/8192) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi277LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434609151/137432230912) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf4322InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf4322LocalValidity :
    LeafFacts leaf4322Box leaf4322Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4322Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68716115456) }) = true
      norm_num [leaf4322Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4322CertificateValid :
    WideCertificateValid leaf4322Box leaf4322Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi277ValidityFacts
    leaf4322LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4322CoverageChecked :
    coverageCheck (innerAD leaf4322Box) leaf4322InnerLog = true := by
  rfl'

private theorem leaf4322InnerLogValid :
    leaf4322InnerLog.Valid 8 (innerAD leaf4322Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf4322CoverageChecked

private noncomputable def leaf4322InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629371/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4322InputLogOnePlusV_eq :
    leaf4322InputLogOnePlusV = outerEnclosure 24
      (leaf4322Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4322RoundedFacts : LeafRoundedFacts 8
    leaf4322Certificate.logOnePlusV leaf4322InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4322InputLogOnePlusV_eq }

private noncomputable def leaf4322Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi277InputQChi innerPair71Input
    leaf4322InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4322LowerChecked :
    lowerCheck 24 leaf4322Box leaf4322Inputs = true := by
  rfl'

private theorem leaf4322CoversExact : CoversExact 8
    leaf4322Box leaf4322Certificate leaf4322InnerLog leaf4322Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi277RoundedFacts
    innerPair71RoundedFacts leaf4322RoundedFacts (by rfl)

private theorem leaf4322FlatSound : Sound leaf4322Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4322CertificateValid
    leaf4322InnerLogValid leaf4322CoversExact leaf4322LowerChecked

private noncomputable def leaf4323Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (65/256), chiHi := (33/128) }

private noncomputable def leaf4323Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871245/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68716063744) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (962795813/536870912) }, upper := { exponent := 0, mantissa := (7429/4096) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi278LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434557439/137432127488) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf4323InnerLog : WideLogData :=
  innerPair226Data

set_option maxRecDepth 1000000 in
private theorem leaf4323LocalValidity :
    LeafFacts leaf4323Box leaf4323Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4323Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68716063744) }) = true
      norm_num [leaf4323Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4323CertificateValid :
    WideCertificateValid leaf4323Box leaf4323Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi278ValidityFacts
    leaf4323LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4323CoverageChecked :
    coverageCheck (innerAD leaf4323Box) leaf4323InnerLog = true := by
  rfl'

private theorem leaf4323InnerLogValid :
    leaf4323InnerLog.Valid 8 (innerAD leaf4323Box) :=
  wideLogDataValid_of_cachedCheck endpoint68PositiveFacts
    endpoint64PositiveFacts.valid leaf4323CoverageChecked

private noncomputable def leaf4323InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629377/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4323InputLogOnePlusV_eq :
    leaf4323InputLogOnePlusV = outerEnclosure 24
      (leaf4323Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4323RoundedFacts : LeafRoundedFacts 8
    leaf4323Certificate.logOnePlusV leaf4323InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4323InputLogOnePlusV_eq }

private noncomputable def leaf4323Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi278InputQChi innerPair226Input
    leaf4323InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4323LowerChecked :
    lowerCheck 24 leaf4323Box leaf4323Inputs = true := by
  rfl'

private theorem leaf4323CoversExact : CoversExact 8
    leaf4323Box leaf4323Certificate leaf4323InnerLog leaf4323Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi278RoundedFacts
    innerPair226RoundedFacts leaf4323RoundedFacts (by rfl)

private theorem leaf4323FlatSound : Sound leaf4323Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4323CertificateValid
    leaf4323InnerLogValid leaf4323CoversExact leaf4323LowerChecked

private noncomputable def leaf4324Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (1/4), chiHi := (65/256) }

private noncomputable def leaf4324Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871245/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68716082176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (960436661/536870912) }, upper := { exponent := 0, mantissa := (7411/4096) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi277LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434575871/137432164352) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf4324InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf4324LocalValidity :
    LeafFacts leaf4324Box leaf4324Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4324Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68716082176) }) = true
      norm_num [leaf4324Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4324CertificateValid :
    WideCertificateValid leaf4324Box leaf4324Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi277ValidityFacts
    leaf4324LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4324CoverageChecked :
    coverageCheck (innerAD leaf4324Box) leaf4324InnerLog = true := by
  rfl'

private theorem leaf4324InnerLogValid :
    leaf4324InnerLog.Valid 8 (innerAD leaf4324Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf4324CoverageChecked

private noncomputable def leaf4324InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629375/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4324InputLogOnePlusV_eq :
    leaf4324InputLogOnePlusV = outerEnclosure 24
      (leaf4324Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4324RoundedFacts : LeafRoundedFacts 8
    leaf4324Certificate.logOnePlusV leaf4324InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4324InputLogOnePlusV_eq }

private noncomputable def leaf4324Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi277InputQChi innerPair71Input
    leaf4324InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4324LowerChecked :
    lowerCheck 24 leaf4324Box leaf4324Inputs = true := by
  rfl'

private theorem leaf4324CoversExact : CoversExact 8
    leaf4324Box leaf4324Certificate leaf4324InnerLog leaf4324Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi277RoundedFacts
    innerPair71RoundedFacts leaf4324RoundedFacts (by rfl)

private theorem leaf4324FlatSound : Sound leaf4324Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4324CertificateValid
    leaf4324InnerLogValid leaf4324CoversExact leaf4324LowerChecked

private noncomputable def leaf4325Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (65/256), chiHi := (33/128) }

private noncomputable def leaf4325Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871247/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68716029952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (967055391/536870912) }, upper := { exponent := 0, mantissa := (3731/2048) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi278LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434523647/137432059904) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf4325InnerLog : WideLogData :=
  innerPair221Data

set_option maxRecDepth 1000000 in
private theorem leaf4325LocalValidity :
    LeafFacts leaf4325Box leaf4325Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4325Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68716029952) }) = true
      norm_num [leaf4325Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4325CertificateValid :
    WideCertificateValid leaf4325Box leaf4325Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi278ValidityFacts
    leaf4325LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4325CoverageChecked :
    coverageCheck (innerAD leaf4325Box) leaf4325InnerLog = true := by
  rfl'

private theorem leaf4325InnerLogValid :
    leaf4325InnerLog.Valid 8 (innerAD leaf4325Box) :=
  wideLogDataValid_of_cachedCheck endpoint67PositiveFacts
    endpoint64PositiveFacts.valid leaf4325CoverageChecked

private noncomputable def leaf4325InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814691/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4325InputLogOnePlusV_eq :
    leaf4325InputLogOnePlusV = outerEnclosure 24
      (leaf4325Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4325RoundedFacts : LeafRoundedFacts 8
    leaf4325Certificate.logOnePlusV leaf4325InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4325InputLogOnePlusV_eq }

private noncomputable def leaf4325Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi278InputQChi innerPair221Input
    leaf4325InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4325LowerChecked :
    lowerCheck 24 leaf4325Box leaf4325Inputs = true := by
  rfl'

private theorem leaf4325CoversExact : CoversExact 8
    leaf4325Box leaf4325Certificate leaf4325InnerLog leaf4325Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi278RoundedFacts
    innerPair221RoundedFacts leaf4325RoundedFacts (by rfl)

private theorem leaf4325FlatSound : Sound leaf4325Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4325CertificateValid
    leaf4325InnerLogValid leaf4325CoversExact leaf4325LowerChecked

private noncomputable def leaf4326Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (33/128), chiHi := (67/256) }

private noncomputable def leaf4326Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871247/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905337344) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (969349011/536870912) }, upper := { exponent := 0, mantissa := (14959/8192) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi275LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811501909/45810674688) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf4326InnerLog : WideLogData :=
  innerPair221Data

set_option maxRecDepth 1000000 in
private theorem leaf4326LocalValidity :
    LeafFacts leaf4326Box leaf4326Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4326Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905337344) }) = true
      norm_num [leaf4326Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4326CertificateValid :
    WideCertificateValid leaf4326Box leaf4326Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi275ValidityFacts
    leaf4326LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4326CoverageChecked :
    coverageCheck (innerAD leaf4326Box) leaf4326InnerLog = true := by
  rfl'

private theorem leaf4326InnerLogValid :
    leaf4326InnerLog.Valid 8 (innerAD leaf4326Box) :=
  wideLogDataValid_of_cachedCheck endpoint67PositiveFacts
    endpoint64PositiveFacts.valid leaf4326CoverageChecked

private noncomputable def leaf4326InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453673/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf4326InputLogOnePlusV_eq :
    leaf4326InputLogOnePlusV = outerEnclosure 24
      (leaf4326Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4326RoundedFacts : LeafRoundedFacts 8
    leaf4326Certificate.logOnePlusV leaf4326InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4326InputLogOnePlusV_eq }

private noncomputable def leaf4326Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi275InputQChi innerPair221Input
    leaf4326InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4326LowerChecked :
    lowerCheck 24 leaf4326Box leaf4326Inputs = true := by
  rfl'

private theorem leaf4326CoversExact : CoversExact 8
    leaf4326Box leaf4326Certificate leaf4326InnerLog leaf4326Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi275RoundedFacts
    innerPair221RoundedFacts leaf4326RoundedFacts (by rfl)

private theorem leaf4326FlatSound : Sound leaf4326Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4326CertificateValid
    leaf4326InnerLogValid leaf4326CoversExact leaf4326LowerChecked

private noncomputable def leaf4327Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (67/256), chiHi := (17/64) }

private noncomputable def leaf4327Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871249/536870912) }, vSqrt := { lower := (65529/65536), upper := (13743698739/13743192064) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (975902209/536870912) }, upper := { exponent := 0, mantissa := (3765/2048) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi276LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (27486890803/27486384128) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf4327InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf4327LocalValidity :
    LeafFacts leaf4327Box leaf4327Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4327Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (13743698739/13743192064) }) = true
      norm_num [leaf4327Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4327CertificateValid :
    WideCertificateValid leaf4327Box leaf4327Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi276ValidityFacts
    leaf4327LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4327CoverageChecked :
    coverageCheck (innerAD leaf4327Box) leaf4327InnerLog = true := by
  rfl'

private theorem leaf4327InnerLogValid :
    leaf4327InnerLog.Valid 8 (innerAD leaf4327Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf4327CoverageChecked

private noncomputable def leaf4327InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814695/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4327InputLogOnePlusV_eq :
    leaf4327InputLogOnePlusV = outerEnclosure 24
      (leaf4327Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4327RoundedFacts : LeafRoundedFacts 8
    leaf4327Certificate.logOnePlusV leaf4327InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4327InputLogOnePlusV_eq }

private noncomputable def leaf4327Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi276InputQChi innerPair91Input
    leaf4327InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4327LowerChecked :
    lowerCheck 24 leaf4327Box leaf4327Inputs = true := by
  rfl'

private theorem leaf4327CoversExact : CoversExact 8
    leaf4327Box leaf4327Certificate leaf4327InnerLog leaf4327Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi276RoundedFacts
    innerPair91RoundedFacts leaf4327RoundedFacts (by rfl)

private theorem leaf4327FlatSound : Sound leaf4327Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4327CertificateValid
    leaf4327InnerLogValid leaf4327CoversExact leaf4327LowerChecked

private noncomputable def leaf4328Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (33/128), chiHi := (67/256) }

private noncomputable def leaf4328Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871249/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715977728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (973674121/536870912) }, upper := { exponent := 0, mantissa := (7513/4096) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi275LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434471423/137431955456) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf4328InnerLog : WideLogData :=
  innerPair94Data

set_option maxRecDepth 1000000 in
private theorem leaf4328LocalValidity :
    LeafFacts leaf4328Box leaf4328Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4328Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715977728) }) = true
      norm_num [leaf4328Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4328CertificateValid :
    WideCertificateValid leaf4328Box leaf4328Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi275ValidityFacts
    leaf4328LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4328CoverageChecked :
    coverageCheck (innerAD leaf4328Box) leaf4328InnerLog = true := by
  rfl'

private theorem leaf4328InnerLogValid :
    leaf4328InnerLog.Valid 8 (innerAD leaf4328Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint61PositiveFacts.valid leaf4328CoverageChecked

private noncomputable def leaf4328InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907347/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4328InputLogOnePlusV_eq :
    leaf4328InputLogOnePlusV = outerEnclosure 24
      (leaf4328Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4328RoundedFacts : LeafRoundedFacts 8
    leaf4328Certificate.logOnePlusV leaf4328InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4328InputLogOnePlusV_eq }

private noncomputable def leaf4328Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi275InputQChi innerPair94Input
    leaf4328InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4328LowerChecked :
    lowerCheck 24 leaf4328Box leaf4328Inputs = true := by
  rfl'

private theorem leaf4328CoversExact : CoversExact 8
    leaf4328Box leaf4328Certificate leaf4328InnerLog leaf4328Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi275RoundedFacts
    innerPair94RoundedFacts leaf4328RoundedFacts (by rfl)

private theorem leaf4328FlatSound : Sound leaf4328Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4328CertificateValid
    leaf4328InnerLogValid leaf4328CoversExact leaf4328LowerChecked

private noncomputable def leaf4329Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (67/256), chiHi := (17/64) }

private noncomputable def leaf4329Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871251/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715925504) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (980292851/536870912) }, upper := { exponent := 0, mantissa := (1891/1024) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi276LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434419199/137431851008) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf4329InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf4329LocalValidity :
    LeafFacts leaf4329Box leaf4329Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4329Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715925504) }) = true
      norm_num [leaf4329Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4329CertificateValid :
    WideCertificateValid leaf4329Box leaf4329Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi276ValidityFacts
    leaf4329LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4329CoverageChecked :
    coverageCheck (innerAD leaf4329Box) leaf4329InnerLog = true := by
  rfl'

private theorem leaf4329InnerLogValid :
    leaf4329InnerLog.Valid 8 (innerAD leaf4329Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf4329CoverageChecked

private noncomputable def leaf4329InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814697/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4329InputLogOnePlusV_eq :
    leaf4329InputLogOnePlusV = outerEnclosure 24
      (leaf4329Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4329RoundedFacts : LeafRoundedFacts 8
    leaf4329Certificate.logOnePlusV leaf4329InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4329InputLogOnePlusV_eq }

private noncomputable def leaf4329Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi276InputQChi innerPair91Input
    leaf4329InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4329LowerChecked :
    lowerCheck 24 leaf4329Box leaf4329Inputs = true := by
  rfl'

private theorem leaf4329CoversExact : CoversExact 8
    leaf4329Box leaf4329Certificate leaf4329InnerLog leaf4329Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi276RoundedFacts
    innerPair91RoundedFacts leaf4329RoundedFacts (by rfl)

private theorem leaf4329FlatSound : Sound leaf4329Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4329CertificateValid
    leaf4329InnerLogValid leaf4329CoversExact leaf4329LowerChecked

private noncomputable def leaf4330Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (1/4), chiHi := (65/256) }

private noncomputable def leaf4330Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871247/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905349632) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (964630707/536870912) }, upper := { exponent := 0, mantissa := (14887/8192) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi277LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811514197/45810699264) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf4330InnerLog : WideLogData :=
  innerPair226Data

set_option maxRecDepth 1000000 in
private theorem leaf4330LocalValidity :
    LeafFacts leaf4330Box leaf4330Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4330Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905349632) }) = true
      norm_num [leaf4330Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4330CertificateValid :
    WideCertificateValid leaf4330Box leaf4330Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi277ValidityFacts
    leaf4330LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4330CoverageChecked :
    coverageCheck (innerAD leaf4330Box) leaf4330InnerLog = true := by
  rfl'

private theorem leaf4330InnerLogValid :
    leaf4330InnerLog.Valid 8 (innerAD leaf4330Box) :=
  wideLogDataValid_of_cachedCheck endpoint68PositiveFacts
    endpoint64PositiveFacts.valid leaf4330CoverageChecked

private noncomputable def leaf4330InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629379/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4330InputLogOnePlusV_eq :
    leaf4330InputLogOnePlusV = outerEnclosure 24
      (leaf4330Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4330RoundedFacts : LeafRoundedFacts 8
    leaf4330Certificate.logOnePlusV leaf4330InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4330InputLogOnePlusV_eq }

private noncomputable def leaf4330Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi277InputQChi innerPair226Input
    leaf4330InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4330LowerChecked :
    lowerCheck 24 leaf4330Box leaf4330Inputs = true := by
  rfl'

private theorem leaf4330CoversExact : CoversExact 8
    leaf4330Box leaf4330Certificate leaf4330InnerLog leaf4330Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi277RoundedFacts
    innerPair226RoundedFacts leaf4330RoundedFacts (by rfl)

private theorem leaf4330FlatSound : Sound leaf4330Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4330CertificateValid
    leaf4330InnerLogValid leaf4330CoversExact leaf4330LowerChecked

private noncomputable def leaf4331Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (65/256), chiHi := (33/128) }

private noncomputable def leaf4331Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871249/536870912) }, vSqrt := { lower := (65529/65536), upper := (13743698739/13743199232) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (971314969/536870912) }, upper := { exponent := 0, mantissa := (7495/4096) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi278LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (27486897971/27486398464) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf4331InnerLog : WideLogData :=
  innerPair220Data

set_option maxRecDepth 1000000 in
private theorem leaf4331LocalValidity :
    LeafFacts leaf4331Box leaf4331Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4331Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (13743698739/13743199232) }) = true
      norm_num [leaf4331Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4331CertificateValid :
    WideCertificateValid leaf4331Box leaf4331Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi278ValidityFacts
    leaf4331LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4331CoverageChecked :
    coverageCheck (innerAD leaf4331Box) leaf4331InnerLog = true := by
  rfl'

private theorem leaf4331InnerLogValid :
    leaf4331InnerLog.Valid 8 (innerAD leaf4331Box) :=
  wideLogDataValid_of_cachedCheck endpoint67PositiveFacts
    endpoint61PositiveFacts.valid leaf4331CoverageChecked

private noncomputable def leaf4331InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814693/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4331InputLogOnePlusV_eq :
    leaf4331InputLogOnePlusV = outerEnclosure 24
      (leaf4331Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4331RoundedFacts : LeafRoundedFacts 8
    leaf4331Certificate.logOnePlusV leaf4331InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4331InputLogOnePlusV_eq }

private noncomputable def leaf4331Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi278InputQChi innerPair220Input
    leaf4331InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4331LowerChecked :
    lowerCheck 24 leaf4331Box leaf4331Inputs = true := by
  rfl'

private theorem leaf4331CoversExact : CoversExact 8
    leaf4331Box leaf4331Certificate leaf4331InnerLog leaf4331Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi278RoundedFacts
    innerPair220RoundedFacts leaf4331RoundedFacts (by rfl)

private theorem leaf4331FlatSound : Sound leaf4331Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4331CertificateValid
    leaf4331InnerLogValid leaf4331CoversExact leaf4331LowerChecked

private noncomputable def leaf4332Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (1/4), chiHi := (65/256) }

private noncomputable def leaf4332Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871249/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68716015616) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (968824753/536870912) }, upper := { exponent := 0, mantissa := (1869/1024) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi277LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434509311/137432031232) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf4332InnerLog : WideLogData :=
  innerPair221Data

set_option maxRecDepth 1000000 in
private theorem leaf4332LocalValidity :
    LeafFacts leaf4332Box leaf4332Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4332Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68716015616) }) = true
      norm_num [leaf4332Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4332CertificateValid :
    WideCertificateValid leaf4332Box leaf4332Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi277ValidityFacts
    leaf4332LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4332CoverageChecked :
    coverageCheck (innerAD leaf4332Box) leaf4332InnerLog = true := by
  rfl'

private theorem leaf4332InnerLogValid :
    leaf4332InnerLog.Valid 8 (innerAD leaf4332Box) :=
  wideLogDataValid_of_cachedCheck endpoint67PositiveFacts
    endpoint64PositiveFacts.valid leaf4332CoverageChecked

private noncomputable def leaf4332InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629383/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4332InputLogOnePlusV_eq :
    leaf4332InputLogOnePlusV = outerEnclosure 24
      (leaf4332Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4332RoundedFacts : LeafRoundedFacts 8
    leaf4332Certificate.logOnePlusV leaf4332InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4332InputLogOnePlusV_eq }

private noncomputable def leaf4332Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi277InputQChi innerPair221Input
    leaf4332InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4332LowerChecked :
    lowerCheck 24 leaf4332Box leaf4332Inputs = true := by
  rfl'

private theorem leaf4332CoversExact : CoversExact 8
    leaf4332Box leaf4332Certificate leaf4332InnerLog leaf4332Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi277RoundedFacts
    innerPair221RoundedFacts leaf4332RoundedFacts (by rfl)

private theorem leaf4332FlatSound : Sound leaf4332Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4332CertificateValid
    leaf4332InnerLogValid leaf4332CoversExact leaf4332LowerChecked

private noncomputable def leaf4333Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (65/256), chiHi := (33/128) }

private noncomputable def leaf4333Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871251/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715962368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (975574547/536870912) }, upper := { exponent := 0, mantissa := (941/512) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi278LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434456063/137431924736) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf4333InnerLog : WideLogData :=
  innerPair94Data

set_option maxRecDepth 1000000 in
private theorem leaf4333LocalValidity :
    LeafFacts leaf4333Box leaf4333Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4333Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715962368) }) = true
      norm_num [leaf4333Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4333CertificateValid :
    WideCertificateValid leaf4333Box leaf4333Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi278ValidityFacts
    leaf4333LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4333CoverageChecked :
    coverageCheck (innerAD leaf4333Box) leaf4333InnerLog = true := by
  rfl'

private theorem leaf4333InnerLogValid :
    leaf4333InnerLog.Valid 8 (innerAD leaf4333Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint61PositiveFacts.valid leaf4333CoverageChecked

private noncomputable def leaf4333InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814695/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4333InputLogOnePlusV_eq :
    leaf4333InputLogOnePlusV = outerEnclosure 24
      (leaf4333Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4333RoundedFacts : LeafRoundedFacts 8
    leaf4333Certificate.logOnePlusV leaf4333InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4333InputLogOnePlusV_eq }

private noncomputable def leaf4333Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi278InputQChi innerPair94Input
    leaf4333InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4333LowerChecked :
    lowerCheck 24 leaf4333Box leaf4333Inputs = true := by
  rfl'

private theorem leaf4333CoversExact : CoversExact 8
    leaf4333Box leaf4333Certificate leaf4333InnerLog leaf4333Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi278RoundedFacts
    innerPair94RoundedFacts leaf4333RoundedFacts (by rfl)

private theorem leaf4333FlatSound : Sound leaf4333Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4333CertificateValid
    leaf4333InnerLogValid leaf4333CoversExact leaf4333LowerChecked

private noncomputable def leaf4334Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (33/128), chiHi := (67/256) }

private noncomputable def leaf4334Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871251/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715943424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (977999231/536870912) }, upper := { exponent := 0, mantissa := (15093/8192) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi275LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434437119/137431886848) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf4334InnerLog : WideLogData :=
  innerPair94Data

set_option maxRecDepth 1000000 in
private theorem leaf4334LocalValidity :
    LeafFacts leaf4334Box leaf4334Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4334Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715943424) }) = true
      norm_num [leaf4334Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4334CertificateValid :
    WideCertificateValid leaf4334Box leaf4334Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi275ValidityFacts
    leaf4334LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4334CoverageChecked :
    coverageCheck (innerAD leaf4334Box) leaf4334InnerLog = true := by
  rfl'

private theorem leaf4334InnerLogValid :
    leaf4334InnerLog.Valid 8 (innerAD leaf4334Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint61PositiveFacts.valid leaf4334CoverageChecked

private noncomputable def leaf4334InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (726837/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf4334InputLogOnePlusV_eq :
    leaf4334InputLogOnePlusV = outerEnclosure 24
      (leaf4334Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4334RoundedFacts : LeafRoundedFacts 8
    leaf4334Certificate.logOnePlusV leaf4334InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4334InputLogOnePlusV_eq }

private noncomputable def leaf4334Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi275InputQChi innerPair94Input
    leaf4334InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4334LowerChecked :
    lowerCheck 24 leaf4334Box leaf4334Inputs = true := by
  rfl'

private theorem leaf4334CoversExact : CoversExact 8
    leaf4334Box leaf4334Certificate leaf4334InnerLog leaf4334Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi275RoundedFacts
    innerPair94RoundedFacts leaf4334RoundedFacts (by rfl)

private theorem leaf4334FlatSound : Sound leaf4334Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4334CertificateValid
    leaf4334InnerLogValid leaf4334CoversExact leaf4334LowerChecked

private noncomputable def leaf4335Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (67/256), chiHi := (17/64) }

private noncomputable def leaf4335Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871253/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905296896) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (984683493/536870912) }, upper := { exponent := 0, mantissa := (3799/2048) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi276LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811461461/45810593792) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf4335InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf4335LocalValidity :
    LeafFacts leaf4335Box leaf4335Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4335Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905296896) }) = true
      norm_num [leaf4335Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4335CertificateValid :
    WideCertificateValid leaf4335Box leaf4335Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi276ValidityFacts
    leaf4335LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4335CoverageChecked :
    coverageCheck (innerAD leaf4335Box) leaf4335InnerLog = true := by
  rfl'

private theorem leaf4335InnerLogValid :
    leaf4335InnerLog.Valid 8 (innerAD leaf4335Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf4335CoverageChecked

private noncomputable def leaf4335InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629399/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4335InputLogOnePlusV_eq :
    leaf4335InputLogOnePlusV = outerEnclosure 24
      (leaf4335Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4335RoundedFacts : LeafRoundedFacts 8
    leaf4335Certificate.logOnePlusV leaf4335InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4335InputLogOnePlusV_eq }

private noncomputable def leaf4335Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi276InputQChi innerPair91Input
    leaf4335InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4335LowerChecked :
    lowerCheck 24 leaf4335Box leaf4335Inputs = true := by
  rfl'

private theorem leaf4335CoversExact : CoversExact 8
    leaf4335Box leaf4335Certificate leaf4335InnerLog leaf4335Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi276RoundedFacts
    innerPair91RoundedFacts leaf4335RoundedFacts (by rfl)

private theorem leaf4335FlatSound : Sound leaf4335Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4335CertificateValid
    leaf4335InnerLogValid leaf4335CoversExact leaf4335LowerChecked

private noncomputable def leaf4336Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (33/128), chiHi := (67/256) }

private noncomputable def leaf4336Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871253/536870912) }, vSqrt := { lower := (65529/65536), upper := (4581232913/4581060608) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (982324341/536870912) }, upper := { exponent := 0, mantissa := (1895/1024) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi275LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9162293521/9162121216) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf4336InnerLog : WideLogData :=
  innerPair214Data

set_option maxRecDepth 1000000 in
private theorem leaf4336LocalValidity :
    LeafFacts leaf4336Box leaf4336Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4336Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4581232913/4581060608) }) = true
      norm_num [leaf4336Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4336CertificateValid :
    WideCertificateValid leaf4336Box leaf4336Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi275ValidityFacts
    leaf4336LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4336CoverageChecked :
    coverageCheck (innerAD leaf4336Box) leaf4336InnerLog = true := by
  rfl'

private theorem leaf4336InnerLogValid :
    leaf4336InnerLog.Valid 8 (innerAD leaf4336Box) :=
  wideLogDataValid_of_cachedCheck endpoint64PositiveFacts
    endpoint211PositiveFacts.valid leaf4336CoverageChecked

private noncomputable def leaf4336InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907349/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4336InputLogOnePlusV_eq :
    leaf4336InputLogOnePlusV = outerEnclosure 24
      (leaf4336Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4336RoundedFacts : LeafRoundedFacts 8
    leaf4336Certificate.logOnePlusV leaf4336InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4336InputLogOnePlusV_eq }

private noncomputable def leaf4336Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi275InputQChi innerPair214Input
    leaf4336InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4336LowerChecked :
    lowerCheck 24 leaf4336Box leaf4336Inputs = true := by
  rfl'

private theorem leaf4336CoversExact : CoversExact 8
    leaf4336Box leaf4336Certificate leaf4336InnerLog leaf4336Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi275RoundedFacts
    innerPair214RoundedFacts leaf4336RoundedFacts (by rfl)

private theorem leaf4336FlatSound : Sound leaf4336Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4336CertificateValid
    leaf4336InnerLogValid leaf4336CoversExact leaf4336LowerChecked

private noncomputable def leaf4337Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (67/256), chiHi := (17/64) }

private noncomputable def leaf4337Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871255/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715855872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (989074135/536870912) }, upper := { exponent := 0, mantissa := (477/256) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi276LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434349567/137431711744) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf4337InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf4337LocalValidity :
    LeafFacts leaf4337Box leaf4337Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4337Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715855872) }) = true
      norm_num [leaf4337Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4337CertificateValid :
    WideCertificateValid leaf4337Box leaf4337Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi276ValidityFacts
    leaf4337LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4337CoverageChecked :
    coverageCheck (innerAD leaf4337Box) leaf4337InnerLog = true := by
  rfl'

private theorem leaf4337InnerLogValid :
    leaf4337InnerLog.Valid 8 (innerAD leaf4337Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf4337CoverageChecked

private noncomputable def leaf4337InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629403/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4337InputLogOnePlusV_eq :
    leaf4337InputLogOnePlusV = outerEnclosure 24
      (leaf4337Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4337RoundedFacts : LeafRoundedFacts 8
    leaf4337Certificate.logOnePlusV leaf4337InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4337InputLogOnePlusV_eq }

private noncomputable def leaf4337Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi276InputQChi innerPair91Input
    leaf4337InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4337LowerChecked :
    lowerCheck 24 leaf4337Box leaf4337Inputs = true := by
  rfl'

private theorem leaf4337CoversExact : CoversExact 8
    leaf4337Box leaf4337Certificate leaf4337InnerLog leaf4337Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi276RoundedFacts
    innerPair91RoundedFacts leaf4337RoundedFacts (by rfl)

private theorem leaf4337FlatSound : Sound leaf4337Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4337CertificateValid
    leaf4337InnerLogValid leaf4337CoversExact leaf4337LowerChecked

private noncomputable def leaf4338Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (17/64), chiHi := (69/256) }

private noncomputable def leaf4338Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871251/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715908608) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (982455407/536870912) }, upper := { exponent := 0, mantissa := (15161/8192) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi257LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434402303/137431817216) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf4338InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf4338LocalValidity :
    LeafFacts leaf4338Box leaf4338Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4338Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715908608) }) = true
      norm_num [leaf4338Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4338CertificateValid :
    WideCertificateValid leaf4338Box leaf4338Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi257ValidityFacts
    leaf4338LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4338CoverageChecked :
    coverageCheck (innerAD leaf4338Box) leaf4338InnerLog = true := by
  rfl'

private theorem leaf4338InnerLogValid :
    leaf4338InnerLog.Valid 8 (innerAD leaf4338Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf4338CoverageChecked

private noncomputable def leaf4338InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907349/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4338InputLogOnePlusV_eq :
    leaf4338InputLogOnePlusV = outerEnclosure 24
      (leaf4338Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4338RoundedFacts : LeafRoundedFacts 8
    leaf4338Certificate.logOnePlusV leaf4338InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4338InputLogOnePlusV_eq }

private noncomputable def leaf4338Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi257InputQChi innerPair91Input
    leaf4338InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4338LowerChecked :
    lowerCheck 24 leaf4338Box leaf4338Inputs = true := by
  rfl'

private theorem leaf4338CoversExact : CoversExact 8
    leaf4338Box leaf4338Certificate leaf4338InnerLog leaf4338Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi257RoundedFacts
    innerPair91RoundedFacts leaf4338RoundedFacts (by rfl)

private theorem leaf4338FlatSound : Sound leaf4338Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4338CertificateValid
    leaf4338InnerLogValid leaf4338CoversExact leaf4338LowerChecked

private noncomputable def leaf4339Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (69/256), chiHi := (35/128) }

private noncomputable def leaf4339Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871253/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905285632) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (989008605/536870912) }, upper := { exponent := 0, mantissa := (7631/4096) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi258LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811450197/45810571264) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf4339InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf4339LocalValidity :
    LeafFacts leaf4339Box leaf4339Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4339Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905285632) }) = true
      norm_num [leaf4339Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4339CertificateValid :
    WideCertificateValid leaf4339Box leaf4339Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi258ValidityFacts
    leaf4339LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4339CoverageChecked :
    coverageCheck (innerAD leaf4339Box) leaf4339InnerLog = true := by
  rfl'

private theorem leaf4339InnerLogValid :
    leaf4339InnerLog.Valid 8 (innerAD leaf4339Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf4339CoverageChecked

private noncomputable def leaf4339InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629403/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4339InputLogOnePlusV_eq :
    leaf4339InputLogOnePlusV = outerEnclosure 24
      (leaf4339Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4339RoundedFacts : LeafRoundedFacts 8
    leaf4339Certificate.logOnePlusV leaf4339InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4339InputLogOnePlusV_eq }

private noncomputable def leaf4339Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi258InputQChi innerPair91Input
    leaf4339InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4339LowerChecked :
    lowerCheck 24 leaf4339Box leaf4339Inputs = true := by
  rfl'

private theorem leaf4339CoversExact : CoversExact 8
    leaf4339Box leaf4339Certificate leaf4339InnerLog leaf4339Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi258RoundedFacts
    innerPair91RoundedFacts leaf4339RoundedFacts (by rfl)

private theorem leaf4339FlatSound : Sound leaf4339Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4339CertificateValid
    leaf4339InnerLogValid leaf4339CoversExact leaf4339LowerChecked

private noncomputable def leaf4340Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (17/64), chiHi := (69/256) }

private noncomputable def leaf4340Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871253/536870912) }, vSqrt := { lower := (65529/65536), upper := (13743698739/13743174656) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (986911581/536870912) }, upper := { exponent := 0, mantissa := (7615/4096) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi257LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (27486873395/27486349312) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf4340InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf4340LocalValidity :
    LeafFacts leaf4340Box leaf4340Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4340Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (13743698739/13743174656) }) = true
      norm_num [leaf4340Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4340CertificateValid :
    WideCertificateValid leaf4340Box leaf4340Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi257ValidityFacts
    leaf4340LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4340CoverageChecked :
    coverageCheck (innerAD leaf4340Box) leaf4340InnerLog = true := by
  rfl'

private theorem leaf4340InnerLogValid :
    leaf4340InnerLog.Valid 8 (innerAD leaf4340Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf4340CoverageChecked

private noncomputable def leaf4340InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629401/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4340InputLogOnePlusV_eq :
    leaf4340InputLogOnePlusV = outerEnclosure 24
      (leaf4340Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4340RoundedFacts : LeafRoundedFacts 8
    leaf4340Certificate.logOnePlusV leaf4340InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4340InputLogOnePlusV_eq }

private noncomputable def leaf4340Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi257InputQChi innerPair91Input
    leaf4340InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4340LowerChecked :
    lowerCheck 24 leaf4340Box leaf4340Inputs = true := by
  rfl'

private theorem leaf4340CoversExact : CoversExact 8
    leaf4340Box leaf4340Certificate leaf4340InnerLog leaf4340Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi257RoundedFacts
    innerPair91RoundedFacts leaf4340RoundedFacts (by rfl)

private theorem leaf4340FlatSound : Sound leaf4340Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4340CertificateValid
    leaf4340InnerLogValid leaf4340CoversExact leaf4340LowerChecked

private noncomputable def leaf4341Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (69/256), chiHi := (35/128) }

private noncomputable def leaf4341Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871255/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715821056) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (993530311/536870912) }, upper := { exponent := 0, mantissa := (3833/2048) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi258LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434314751/137431642112) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf4341InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf4341LocalValidity :
    LeafFacts leaf4341Box leaf4341Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4341Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715821056) }) = true
      norm_num [leaf4341Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4341CertificateValid :
    WideCertificateValid leaf4341Box leaf4341Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi258ValidityFacts
    leaf4341LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4341CoverageChecked :
    coverageCheck (innerAD leaf4341Box) leaf4341InnerLog = true := by
  rfl'

private theorem leaf4341InnerLogValid :
    leaf4341InnerLog.Valid 8 (innerAD leaf4341Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf4341CoverageChecked

private noncomputable def leaf4341InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629407/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4341InputLogOnePlusV_eq :
    leaf4341InputLogOnePlusV = outerEnclosure 24
      (leaf4341Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4341RoundedFacts : LeafRoundedFacts 8
    leaf4341Certificate.logOnePlusV leaf4341InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4341InputLogOnePlusV_eq }

private noncomputable def leaf4341Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi258InputQChi innerPair91Input
    leaf4341InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4341LowerChecked :
    lowerCheck 24 leaf4341Box leaf4341Inputs = true := by
  rfl'

private theorem leaf4341CoversExact : CoversExact 8
    leaf4341Box leaf4341Certificate leaf4341InnerLog leaf4341Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi258RoundedFacts
    innerPair91RoundedFacts leaf4341RoundedFacts (by rfl)

private theorem leaf4341FlatSound : Sound leaf4341Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4341CertificateValid
    leaf4341InnerLogValid leaf4341CoversExact leaf4341LowerChecked

private noncomputable def leaf4342Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (35/128), chiHi := (71/256) }

private noncomputable def leaf4342Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871255/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715805184) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (995561803/536870912) }, upper := { exponent := 0, mantissa := (15363/8192) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi279LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434298879/137431610368) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf4342InnerLog : WideLogData :=
  innerPair199Data

set_option maxRecDepth 1000000 in
private theorem leaf4342LocalValidity :
    LeafFacts leaf4342Box leaf4342Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4342Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715805184) }) = true
      norm_num [leaf4342Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4342CertificateValid :
    WideCertificateValid leaf4342Box leaf4342Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi279ValidityFacts
    leaf4342LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4342CoverageChecked :
    coverageCheck (innerAD leaf4342Box) leaf4342InnerLog = true := by
  rfl'

private theorem leaf4342InnerLogValid :
    leaf4342InnerLog.Valid 8 (innerAD leaf4342Box) :=
  wideLogDataValid_of_cachedCheck endpoint61PositiveFacts
    endpoint69PositiveFacts.valid leaf4342CoverageChecked

private noncomputable def leaf4342InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629409/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4342InputLogOnePlusV_eq :
    leaf4342InputLogOnePlusV = outerEnclosure 24
      (leaf4342Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4342RoundedFacts : LeafRoundedFacts 8
    leaf4342Certificate.logOnePlusV leaf4342InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4342InputLogOnePlusV_eq }

private noncomputable def leaf4342Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi279InputQChi innerPair199Input
    leaf4342InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4342LowerChecked :
    lowerCheck 24 leaf4342Box leaf4342Inputs = true := by
  rfl'

private theorem leaf4342CoversExact : CoversExact 8
    leaf4342Box leaf4342Certificate leaf4342InnerLog leaf4342Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi279RoundedFacts
    innerPair199RoundedFacts leaf4342RoundedFacts (by rfl)

private theorem leaf4342FlatSound : Sound leaf4342Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4342CertificateValid
    leaf4342InnerLogValid leaf4342CoversExact leaf4342LowerChecked

private noncomputable def leaf4343Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (71/256), chiHi := (9/32) }

private noncomputable def leaf4343Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871257/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715753472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1002115001/536870912) }, upper := { exponent := 0, mantissa := (1933/1024) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi280LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434247167/137431506944) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf4343InnerLog : WideLogData :=
  innerPair482Data

set_option maxRecDepth 1000000 in
private theorem leaf4343LocalValidity :
    LeafFacts leaf4343Box leaf4343Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4343Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715753472) }) = true
      norm_num [leaf4343Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4343CertificateValid :
    WideCertificateValid leaf4343Box leaf4343Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi280ValidityFacts
    leaf4343LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4343CoverageChecked :
    coverageCheck (innerAD leaf4343Box) leaf4343InnerLog = true := by
  rfl'

private theorem leaf4343InnerLogValid :
    leaf4343InnerLog.Valid 8 (innerAD leaf4343Box) :=
  wideLogDataValid_of_cachedCheck endpoint211PositiveFacts
    endpoint69PositiveFacts.valid leaf4343CoverageChecked

private noncomputable def leaf4343InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629415/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4343InputLogOnePlusV_eq :
    leaf4343InputLogOnePlusV = outerEnclosure 24
      (leaf4343Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4343RoundedFacts : LeafRoundedFacts 8
    leaf4343Certificate.logOnePlusV leaf4343InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4343InputLogOnePlusV_eq }

private noncomputable def leaf4343Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi280InputQChi innerPair482Input
    leaf4343InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4343LowerChecked :
    lowerCheck 24 leaf4343Box leaf4343Inputs = true := by
  rfl'

private theorem leaf4343CoversExact : CoversExact 8
    leaf4343Box leaf4343Certificate leaf4343InnerLog leaf4343Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi280RoundedFacts
    innerPair482RoundedFacts leaf4343RoundedFacts (by rfl)

private theorem leaf4343FlatSound : Sound leaf4343Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4343CertificateValid
    leaf4343InnerLogValid leaf4343CoversExact leaf4343LowerChecked

private noncomputable def leaf4344Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (35/128), chiHi := (71/256) }

private noncomputable def leaf4344Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871257/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715768832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1000149041/536870912) }, upper := { exponent := 0, mantissa := (7717/4096) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi279LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434262527/137431537664) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf4344InnerLog : WideLogData :=
  innerPair482Data

set_option maxRecDepth 1000000 in
private theorem leaf4344LocalValidity :
    LeafFacts leaf4344Box leaf4344Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4344Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715768832) }) = true
      norm_num [leaf4344Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4344CertificateValid :
    WideCertificateValid leaf4344Box leaf4344Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi279ValidityFacts
    leaf4344LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4344CoverageChecked :
    coverageCheck (innerAD leaf4344Box) leaf4344InnerLog = true := by
  rfl'

private theorem leaf4344InnerLogValid :
    leaf4344InnerLog.Valid 8 (innerAD leaf4344Box) :=
  wideLogDataValid_of_cachedCheck endpoint211PositiveFacts
    endpoint69PositiveFacts.valid leaf4344CoverageChecked

private noncomputable def leaf4344InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629413/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4344InputLogOnePlusV_eq :
    leaf4344InputLogOnePlusV = outerEnclosure 24
      (leaf4344Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4344RoundedFacts : LeafRoundedFacts 8
    leaf4344Certificate.logOnePlusV leaf4344InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4344InputLogOnePlusV_eq }

private noncomputable def leaf4344Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi279InputQChi innerPair482Input
    leaf4344InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4344LowerChecked :
    lowerCheck 24 leaf4344Box leaf4344Inputs = true := by
  rfl'

private theorem leaf4344CoversExact : CoversExact 8
    leaf4344Box leaf4344Certificate leaf4344InnerLog leaf4344Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi279RoundedFacts
    innerPair482RoundedFacts leaf4344RoundedFacts (by rfl)

private theorem leaf4344FlatSound : Sound leaf4344Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4344CertificateValid
    leaf4344InnerLogValid leaf4344CoversExact leaf4344LowerChecked

private noncomputable def leaf4345Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (71/256), chiHi := (9/32) }

private noncomputable def leaf4345Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871259/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715716608) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1006767771/536870912) }, upper := { exponent := 0, mantissa := (971/512) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi280LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434210303/137431433216) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf4345InnerLog : WideLogData :=
  innerPair103Data

set_option maxRecDepth 1000000 in
private theorem leaf4345LocalValidity :
    LeafFacts leaf4345Box leaf4345Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4345Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715716608) }) = true
      norm_num [leaf4345Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4345CertificateValid :
    WideCertificateValid leaf4345Box leaf4345Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi280ValidityFacts
    leaf4345LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4345CoverageChecked :
    coverageCheck (innerAD leaf4345Box) leaf4345InnerLog = true := by
  rfl'

private theorem leaf4345InnerLogValid :
    leaf4345InnerLog.Valid 8 (innerAD leaf4345Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint70PositiveFacts.valid leaf4345CoverageChecked

private noncomputable def leaf4345InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907355/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4345InputLogOnePlusV_eq :
    leaf4345InputLogOnePlusV = outerEnclosure 24
      (leaf4345Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4345RoundedFacts : LeafRoundedFacts 8
    leaf4345Certificate.logOnePlusV leaf4345InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4345InputLogOnePlusV_eq }

private noncomputable def leaf4345Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi280InputQChi innerPair103Input
    leaf4345InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4345LowerChecked :
    lowerCheck 24 leaf4345Box leaf4345Inputs = true := by
  rfl'

private theorem leaf4345CoversExact : CoversExact 8
    leaf4345Box leaf4345Certificate leaf4345InnerLog leaf4345Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi280RoundedFacts
    innerPair103RoundedFacts leaf4345RoundedFacts (by rfl)

private theorem leaf4345FlatSound : Sound leaf4345Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4345CertificateValid
    leaf4345InnerLogValid leaf4345CoversExact leaf4345LowerChecked

private noncomputable def leaf4346Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (17/64), chiHi := (69/256) }

private noncomputable def leaf4346Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871255/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715837952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (991367755/536870912) }, upper := { exponent := 0, mantissa := (15299/8192) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi257LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434331647/137431675904) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf4346InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf4346LocalValidity :
    LeafFacts leaf4346Box leaf4346Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4346Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715837952) }) = true
      norm_num [leaf4346Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4346CertificateValid :
    WideCertificateValid leaf4346Box leaf4346Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi257ValidityFacts
    leaf4346LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4346CoverageChecked :
    coverageCheck (innerAD leaf4346Box) leaf4346InnerLog = true := by
  rfl'

private theorem leaf4346InnerLogValid :
    leaf4346InnerLog.Valid 8 (innerAD leaf4346Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf4346CoverageChecked

private noncomputable def leaf4346InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629405/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4346InputLogOnePlusV_eq :
    leaf4346InputLogOnePlusV = outerEnclosure 24
      (leaf4346Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4346RoundedFacts : LeafRoundedFacts 8
    leaf4346Certificate.logOnePlusV leaf4346InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4346InputLogOnePlusV_eq }

private noncomputable def leaf4346Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi257InputQChi innerPair91Input
    leaf4346InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4346LowerChecked :
    lowerCheck 24 leaf4346Box leaf4346Inputs = true := by
  rfl'

private theorem leaf4346CoversExact : CoversExact 8
    leaf4346Box leaf4346Certificate leaf4346InnerLog leaf4346Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi257RoundedFacts
    innerPair91RoundedFacts leaf4346RoundedFacts (by rfl)

private theorem leaf4346FlatSound : Sound leaf4346Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4346CertificateValid
    leaf4346InnerLogValid leaf4346CoversExact leaf4346LowerChecked

private noncomputable def leaf4347Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (69/256), chiHi := (35/128) }

private noncomputable def leaf4347Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871257/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715785216) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (998052017/536870912) }, upper := { exponent := 0, mantissa := (7701/4096) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi258LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434278911/137431570432) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf4347InnerLog : WideLogData :=
  innerPair199Data

set_option maxRecDepth 1000000 in
private theorem leaf4347LocalValidity :
    LeafFacts leaf4347Box leaf4347Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4347Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715785216) }) = true
      norm_num [leaf4347Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4347CertificateValid :
    WideCertificateValid leaf4347Box leaf4347Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi258ValidityFacts
    leaf4347LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4347CoverageChecked :
    coverageCheck (innerAD leaf4347Box) leaf4347InnerLog = true := by
  rfl'

private theorem leaf4347InnerLogValid :
    leaf4347InnerLog.Valid 8 (innerAD leaf4347Box) :=
  wideLogDataValid_of_cachedCheck endpoint61PositiveFacts
    endpoint69PositiveFacts.valid leaf4347CoverageChecked

private noncomputable def leaf4347InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629411/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4347InputLogOnePlusV_eq :
    leaf4347InputLogOnePlusV = outerEnclosure 24
      (leaf4347Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4347RoundedFacts : LeafRoundedFacts 8
    leaf4347Certificate.logOnePlusV leaf4347InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4347InputLogOnePlusV_eq }

private noncomputable def leaf4347Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi258InputQChi innerPair199Input
    leaf4347InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4347LowerChecked :
    lowerCheck 24 leaf4347Box leaf4347Inputs = true := by
  rfl'

private theorem leaf4347CoversExact : CoversExact 8
    leaf4347Box leaf4347Certificate leaf4347InnerLog leaf4347Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi258RoundedFacts
    innerPair199RoundedFacts leaf4347RoundedFacts (by rfl)

private theorem leaf4347FlatSound : Sound leaf4347Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4347CertificateValid
    leaf4347InnerLogValid leaf4347CoversExact leaf4347LowerChecked

private noncomputable def leaf4348Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (17/64), chiHi := (69/256) }

private noncomputable def leaf4348Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871257/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715802624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (995823929/536870912) }, upper := { exponent := 0, mantissa := (1921/1024) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi257LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434296319/137431605248) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf4348InnerLog : WideLogData :=
  innerPair199Data

set_option maxRecDepth 1000000 in
private theorem leaf4348LocalValidity :
    LeafFacts leaf4348Box leaf4348Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4348Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715802624) }) = true
      norm_num [leaf4348Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4348CertificateValid :
    WideCertificateValid leaf4348Box leaf4348Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi257ValidityFacts
    leaf4348LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4348CoverageChecked :
    coverageCheck (innerAD leaf4348Box) leaf4348InnerLog = true := by
  rfl'

private theorem leaf4348InnerLogValid :
    leaf4348InnerLog.Valid 8 (innerAD leaf4348Box) :=
  wideLogDataValid_of_cachedCheck endpoint61PositiveFacts
    endpoint69PositiveFacts.valid leaf4348CoverageChecked

private noncomputable def leaf4348InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629409/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4348InputLogOnePlusV_eq :
    leaf4348InputLogOnePlusV = outerEnclosure 24
      (leaf4348Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4348RoundedFacts : LeafRoundedFacts 8
    leaf4348Certificate.logOnePlusV leaf4348InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4348InputLogOnePlusV_eq }

private noncomputable def leaf4348Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi257InputQChi innerPair199Input
    leaf4348InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4348LowerChecked :
    lowerCheck 24 leaf4348Box leaf4348Inputs = true := by
  rfl'

private theorem leaf4348CoversExact : CoversExact 8
    leaf4348Box leaf4348Certificate leaf4348InnerLog leaf4348Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi257RoundedFacts
    innerPair199RoundedFacts leaf4348RoundedFacts (by rfl)

private theorem leaf4348FlatSound : Sound leaf4348Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4348CertificateValid
    leaf4348InnerLogValid leaf4348CoversExact leaf4348LowerChecked

private noncomputable def leaf4349Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (69/256), chiHi := (35/128) }

private noncomputable def leaf4349Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871259/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905249792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1002573723/536870912) }, upper := { exponent := 0, mantissa := (967/512) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi258LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811414357/45810499584) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf4349InnerLog : WideLogData :=
  innerPair482Data

set_option maxRecDepth 1000000 in
private theorem leaf4349LocalValidity :
    LeafFacts leaf4349Box leaf4349Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4349Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905249792) }) = true
      norm_num [leaf4349Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4349CertificateValid :
    WideCertificateValid leaf4349Box leaf4349Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi258ValidityFacts
    leaf4349LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4349CoverageChecked :
    coverageCheck (innerAD leaf4349Box) leaf4349InnerLog = true := by
  rfl'

private theorem leaf4349InnerLogValid :
    leaf4349InnerLog.Valid 8 (innerAD leaf4349Box) :=
  wideLogDataValid_of_cachedCheck endpoint211PositiveFacts
    endpoint69PositiveFacts.valid leaf4349CoverageChecked

private noncomputable def leaf4349InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453677/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf4349InputLogOnePlusV_eq :
    leaf4349InputLogOnePlusV = outerEnclosure 24
      (leaf4349Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4349RoundedFacts : LeafRoundedFacts 8
    leaf4349Certificate.logOnePlusV leaf4349InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4349InputLogOnePlusV_eq }

private noncomputable def leaf4349Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi258InputQChi innerPair482Input
    leaf4349InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4349LowerChecked :
    lowerCheck 24 leaf4349Box leaf4349Inputs = true := by
  rfl'

private theorem leaf4349CoversExact : CoversExact 8
    leaf4349Box leaf4349Certificate leaf4349InnerLog leaf4349Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi258RoundedFacts
    innerPair482RoundedFacts leaf4349RoundedFacts (by rfl)

private theorem leaf4349FlatSound : Sound leaf4349Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4349CertificateValid
    leaf4349InnerLogValid leaf4349CoversExact leaf4349LowerChecked

private noncomputable def leaf4350Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (35/128), chiHi := (71/256) }

private noncomputable def leaf4350Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871259/536870912) }, vSqrt := { lower := (65529/65536), upper := (4581232913/4581048832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1004736279/536870912) }, upper := { exponent := 0, mantissa := (15505/8192) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi279LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9162281745/9162097664) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf4350InnerLog : WideLogData :=
  innerPair483Data

set_option maxRecDepth 1000000 in
private theorem leaf4350LocalValidity :
    LeafFacts leaf4350Box leaf4350Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4350Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4581232913/4581048832) }) = true
      norm_num [leaf4350Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4350CertificateValid :
    WideCertificateValid leaf4350Box leaf4350Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi279ValidityFacts
    leaf4350LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4350CoverageChecked :
    coverageCheck (innerAD leaf4350Box) leaf4350InnerLog = true := by
  rfl'

private theorem leaf4350InnerLogValid :
    leaf4350InnerLog.Valid 8 (innerAD leaf4350Box) :=
  wideLogDataValid_of_cachedCheck endpoint211PositiveFacts
    endpoint70PositiveFacts.valid leaf4350CoverageChecked

private noncomputable def leaf4350InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814709/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4350InputLogOnePlusV_eq :
    leaf4350InputLogOnePlusV = outerEnclosure 24
      (leaf4350Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4350RoundedFacts : LeafRoundedFacts 8
    leaf4350Certificate.logOnePlusV leaf4350InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4350InputLogOnePlusV_eq }

private noncomputable def leaf4350Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi279InputQChi innerPair483Input
    leaf4350InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4350LowerChecked :
    lowerCheck 24 leaf4350Box leaf4350Inputs = true := by
  rfl'

private theorem leaf4350CoversExact : CoversExact 8
    leaf4350Box leaf4350Certificate leaf4350InnerLog leaf4350Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi279RoundedFacts
    innerPair483RoundedFacts leaf4350RoundedFacts (by rfl)

private theorem leaf4350FlatSound : Sound leaf4350Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4350CertificateValid
    leaf4350InnerLogValid leaf4350CoversExact leaf4350LowerChecked

private noncomputable def leaf4351Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (71/256), chiHi := (9/32) }

private noncomputable def leaf4351Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871261/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715679744) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1011420541/536870912) }, upper := { exponent := 0, mantissa := (1951/1024) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi280LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434173439/137431359488) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf4351InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4351LocalValidity :
    LeafFacts leaf4351Box leaf4351Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4351Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715679744) }) = true
      norm_num [leaf4351Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4351CertificateValid :
    WideCertificateValid leaf4351Box leaf4351Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi280ValidityFacts
    leaf4351LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4351CoverageChecked :
    coverageCheck (innerAD leaf4351Box) leaf4351InnerLog = true := by
  rfl'

private theorem leaf4351InnerLogValid :
    leaf4351InnerLog.Valid 8 (innerAD leaf4351Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4351CoverageChecked

private noncomputable def leaf4351InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (726839/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf4351InputLogOnePlusV_eq :
    leaf4351InputLogOnePlusV = outerEnclosure 24
      (leaf4351Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4351RoundedFacts : LeafRoundedFacts 8
    leaf4351Certificate.logOnePlusV leaf4351InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4351InputLogOnePlusV_eq }

private noncomputable def leaf4351Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi280InputQChi innerPair100Input
    leaf4351InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4351LowerChecked :
    lowerCheck 24 leaf4351Box leaf4351Inputs = true := by
  rfl'

private theorem leaf4351CoversExact : CoversExact 8
    leaf4351Box leaf4351Certificate leaf4351InnerLog leaf4351Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi280RoundedFacts
    innerPair100RoundedFacts leaf4351RoundedFacts (by rfl)

private theorem leaf4351FlatSound : Sound leaf4351Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4351CertificateValid
    leaf4351InnerLogValid leaf4351CoversExact leaf4351LowerChecked

private noncomputable def leaf4352Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (35/128), chiHi := (71/256) }

private noncomputable def leaf4352Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871261/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715696128) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1009323517/536870912) }, upper := { exponent := 0, mantissa := (1947/1024) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi279LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434189823/137431392256) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf4352InnerLog : WideLogData :=
  innerPair103Data

set_option maxRecDepth 1000000 in
private theorem leaf4352LocalValidity :
    LeafFacts leaf4352Box leaf4352Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4352Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715696128) }) = true
      norm_num [leaf4352Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4352CertificateValid :
    WideCertificateValid leaf4352Box leaf4352Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi279ValidityFacts
    leaf4352LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4352CoverageChecked :
    coverageCheck (innerAD leaf4352Box) leaf4352InnerLog = true := by
  rfl'

private theorem leaf4352InnerLogValid :
    leaf4352InnerLog.Valid 8 (innerAD leaf4352Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint70PositiveFacts.valid leaf4352CoverageChecked

private noncomputable def leaf4352InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814711/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4352InputLogOnePlusV_eq :
    leaf4352InputLogOnePlusV = outerEnclosure 24
      (leaf4352Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4352RoundedFacts : LeafRoundedFacts 8
    leaf4352Certificate.logOnePlusV leaf4352InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4352InputLogOnePlusV_eq }

private noncomputable def leaf4352Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi279InputQChi innerPair103Input
    leaf4352InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4352LowerChecked :
    lowerCheck 24 leaf4352Box leaf4352Inputs = true := by
  rfl'

private theorem leaf4352CoversExact : CoversExact 8
    leaf4352Box leaf4352Certificate leaf4352InnerLog leaf4352Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi279RoundedFacts
    innerPair103RoundedFacts leaf4352RoundedFacts (by rfl)

private theorem leaf4352FlatSound : Sound leaf4352Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4352CertificateValid
    leaf4352InnerLogValid leaf4352CoversExact leaf4352LowerChecked

private noncomputable def leaf4353Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (71/256), chiHi := (9/32) }

private noncomputable def leaf4353Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871263/536870912) }, vSqrt := { lower := (65529/65536), upper := (808452867/808419328) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1016073311/536870912) }, upper := { exponent := 0, mantissa := (245/128) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi280LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (1616872195/1616838656) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf4353InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4353LocalValidity :
    LeafFacts leaf4353Box leaf4353Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4353Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (808452867/808419328) }) = true
      norm_num [leaf4353Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4353CertificateValid :
    WideCertificateValid leaf4353Box leaf4353Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi280ValidityFacts
    leaf4353LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4353CoverageChecked :
    coverageCheck (innerAD leaf4353Box) leaf4353InnerLog = true := by
  rfl'

private theorem leaf4353InnerLogValid :
    leaf4353InnerLog.Valid 8 (innerAD leaf4353Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4353CoverageChecked

private noncomputable def leaf4353InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629429/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4353InputLogOnePlusV_eq :
    leaf4353InputLogOnePlusV = outerEnclosure 24
      (leaf4353Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4353RoundedFacts : LeafRoundedFacts 8
    leaf4353Certificate.logOnePlusV leaf4353InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4353InputLogOnePlusV_eq }

private noncomputable def leaf4353Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi280InputQChi innerPair100Input
    leaf4353InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4353LowerChecked :
    lowerCheck 24 leaf4353Box leaf4353Inputs = true := by
  rfl'

private theorem leaf4353CoversExact : CoversExact 8
    leaf4353Box leaf4353Certificate leaf4353InnerLog leaf4353Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi280RoundedFacts
    innerPair100RoundedFacts leaf4353RoundedFacts (by rfl)

private theorem leaf4353FlatSound : Sound leaf4353Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4353CertificateValid
    leaf4353InnerLogValid leaf4353CoversExact leaf4353LowerChecked

private noncomputable def component88Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (1/4), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component88Node0_sound : Sound component88Node0Box :=
  sound_of_literal_split component88Node0Box leaf4290Box leaf4291Box
    .k (193/64) (by rfl) (by rfl)
    leaf4290FlatSound leaf4291FlatSound

private noncomputable def component88Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (1/4), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component88Node1_sound : Sound component88Node1Box :=
  sound_of_literal_split component88Node1Box leaf4292Box leaf4293Box
    .k (195/64) (by rfl) (by rfl)
    leaf4292FlatSound leaf4293FlatSound

private noncomputable def component88Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (1/4), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component88Node2_sound : Sound component88Node2Box :=
  sound_of_literal_split component88Node2Box component88Node0Box component88Node1Box
    .k (97/32) (by rfl) (by rfl)
    component88Node0_sound component88Node1_sound

private noncomputable def component88Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (33/128), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component88Node3_sound : Sound component88Node3Box :=
  sound_of_literal_split component88Node3Box leaf4294Box leaf4295Box
    .k (193/64) (by rfl) (by rfl)
    leaf4294FlatSound leaf4295FlatSound

private noncomputable def component88Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (33/128), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component88Node4_sound : Sound component88Node4Box :=
  sound_of_literal_split component88Node4Box leaf4296Box leaf4297Box
    .chi (67/256) (by rfl) (by rfl)
    leaf4296FlatSound leaf4297FlatSound

private noncomputable def component88Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (33/128), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component88Node5_sound : Sound component88Node5Box :=
  sound_of_literal_split component88Node5Box component88Node3Box component88Node4Box
    .k (97/32) (by rfl) (by rfl)
    component88Node3_sound component88Node4_sound

private noncomputable def component88Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component88Node6_sound : Sound component88Node6Box :=
  sound_of_literal_split component88Node6Box component88Node2Box component88Node5Box
    .chi (33/128) (by rfl) (by rfl)
    component88Node2_sound component88Node5_sound

private noncomputable def component88Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (1/4), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component88Node7_sound : Sound component88Node7Box :=
  sound_of_literal_split component88Node7Box leaf4298Box leaf4299Box
    .k (197/64) (by rfl) (by rfl)
    leaf4298FlatSound leaf4299FlatSound

private noncomputable def component88Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (1/4), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component88Node8_sound : Sound component88Node8Box :=
  sound_of_literal_split component88Node8Box leaf4300Box leaf4301Box
    .chi (65/256) (by rfl) (by rfl)
    leaf4300FlatSound leaf4301FlatSound

private noncomputable def component88Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (1/4), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component88Node9_sound : Sound component88Node9Box :=
  sound_of_literal_split component88Node9Box component88Node7Box component88Node8Box
    .k (99/32) (by rfl) (by rfl)
    component88Node7_sound component88Node8_sound

private noncomputable def component88Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (33/128), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component88Node10_sound : Sound component88Node10Box :=
  sound_of_literal_split component88Node10Box leaf4302Box leaf4303Box
    .chi (67/256) (by rfl) (by rfl)
    leaf4302FlatSound leaf4303FlatSound

private noncomputable def component88Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (33/128), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component88Node11_sound : Sound component88Node11Box :=
  sound_of_literal_split component88Node11Box leaf4304Box leaf4305Box
    .chi (67/256) (by rfl) (by rfl)
    leaf4304FlatSound leaf4305FlatSound

private noncomputable def component88Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (33/128), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component88Node12_sound : Sound component88Node12Box :=
  sound_of_literal_split component88Node12Box component88Node10Box component88Node11Box
    .k (99/32) (by rfl) (by rfl)
    component88Node10_sound component88Node11_sound

private noncomputable def component88Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component88Node13_sound : Sound component88Node13Box :=
  sound_of_literal_split component88Node13Box component88Node9Box component88Node12Box
    .chi (33/128) (by rfl) (by rfl)
    component88Node9_sound component88Node12_sound

private noncomputable def component88Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component88Node14_sound : Sound component88Node14Box :=
  sound_of_literal_split component88Node14Box component88Node6Box component88Node13Box
    .k (49/16) (by rfl) (by rfl)
    component88Node6_sound component88Node13_sound

private noncomputable def component88Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (17/64), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component88Node15_sound : Sound component88Node15Box :=
  sound_of_literal_split component88Node15Box leaf4306Box leaf4307Box
    .chi (69/256) (by rfl) (by rfl)
    leaf4306FlatSound leaf4307FlatSound

private noncomputable def component88Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (17/64), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component88Node16_sound : Sound component88Node16Box :=
  sound_of_literal_split component88Node16Box leaf4308Box leaf4309Box
    .chi (69/256) (by rfl) (by rfl)
    leaf4308FlatSound leaf4309FlatSound

private noncomputable def component88Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (17/64), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component88Node17_sound : Sound component88Node17Box :=
  sound_of_literal_split component88Node17Box component88Node15Box component88Node16Box
    .k (97/32) (by rfl) (by rfl)
    component88Node15_sound component88Node16_sound

private noncomputable def component88Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (35/128), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component88Node18_sound : Sound component88Node18Box :=
  sound_of_literal_split component88Node18Box leaf4310Box leaf4311Box
    .chi (71/256) (by rfl) (by rfl)
    leaf4310FlatSound leaf4311FlatSound

private noncomputable def component88Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (35/128), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component88Node19_sound : Sound component88Node19Box :=
  sound_of_literal_split component88Node19Box leaf4312Box leaf4313Box
    .chi (71/256) (by rfl) (by rfl)
    leaf4312FlatSound leaf4313FlatSound

private noncomputable def component88Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (35/128), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component88Node20_sound : Sound component88Node20Box :=
  sound_of_literal_split component88Node20Box component88Node18Box component88Node19Box
    .k (97/32) (by rfl) (by rfl)
    component88Node18_sound component88Node19_sound

private noncomputable def component88Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component88Node21_sound : Sound component88Node21Box :=
  sound_of_literal_split component88Node21Box component88Node17Box component88Node20Box
    .chi (35/128) (by rfl) (by rfl)
    component88Node17_sound component88Node20_sound

private noncomputable def component88Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (17/64), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component88Node22_sound : Sound component88Node22Box :=
  sound_of_literal_split component88Node22Box leaf4314Box leaf4315Box
    .chi (69/256) (by rfl) (by rfl)
    leaf4314FlatSound leaf4315FlatSound

private noncomputable def component88Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (17/64), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component88Node23_sound : Sound component88Node23Box :=
  sound_of_literal_split component88Node23Box leaf4316Box leaf4317Box
    .chi (69/256) (by rfl) (by rfl)
    leaf4316FlatSound leaf4317FlatSound

private noncomputable def component88Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (17/64), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component88Node24_sound : Sound component88Node24Box :=
  sound_of_literal_split component88Node24Box component88Node22Box component88Node23Box
    .k (99/32) (by rfl) (by rfl)
    component88Node22_sound component88Node23_sound

private noncomputable def component88Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (35/128), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component88Node25_sound : Sound component88Node25Box :=
  sound_of_literal_split component88Node25Box leaf4318Box leaf4319Box
    .chi (71/256) (by rfl) (by rfl)
    leaf4318FlatSound leaf4319FlatSound

private noncomputable def component88Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (35/128), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component88Node26_sound : Sound component88Node26Box :=
  sound_of_literal_split component88Node26Box leaf4320Box leaf4321Box
    .chi (71/256) (by rfl) (by rfl)
    leaf4320FlatSound leaf4321FlatSound

private noncomputable def component88Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (35/128), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component88Node27_sound : Sound component88Node27Box :=
  sound_of_literal_split component88Node27Box component88Node25Box component88Node26Box
    .k (99/32) (by rfl) (by rfl)
    component88Node25_sound component88Node26_sound

private noncomputable def component88Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component88Node28_sound : Sound component88Node28Box :=
  sound_of_literal_split component88Node28Box component88Node24Box component88Node27Box
    .chi (35/128) (by rfl) (by rfl)
    component88Node24_sound component88Node27_sound

private noncomputable def component88Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component88Node29_sound : Sound component88Node29Box :=
  sound_of_literal_split component88Node29Box component88Node21Box component88Node28Box
    .k (49/16) (by rfl) (by rfl)
    component88Node21_sound component88Node28_sound

private noncomputable def component88Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (1/4), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component88Node30_sound : Sound component88Node30Box :=
  sound_of_literal_split component88Node30Box component88Node14Box component88Node29Box
    .chi (17/64) (by rfl) (by rfl)
    component88Node14_sound component88Node29_sound

private noncomputable def component88Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (1/4), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component88Node31_sound : Sound component88Node31Box :=
  sound_of_literal_split component88Node31Box leaf4322Box leaf4323Box
    .chi (65/256) (by rfl) (by rfl)
    leaf4322FlatSound leaf4323FlatSound

private noncomputable def component88Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (1/4), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component88Node32_sound : Sound component88Node32Box :=
  sound_of_literal_split component88Node32Box leaf4324Box leaf4325Box
    .chi (65/256) (by rfl) (by rfl)
    leaf4324FlatSound leaf4325FlatSound

private noncomputable def component88Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (1/4), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component88Node33_sound : Sound component88Node33Box :=
  sound_of_literal_split component88Node33Box component88Node31Box component88Node32Box
    .k (101/32) (by rfl) (by rfl)
    component88Node31_sound component88Node32_sound

private noncomputable def component88Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (33/128), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component88Node34_sound : Sound component88Node34Box :=
  sound_of_literal_split component88Node34Box leaf4326Box leaf4327Box
    .chi (67/256) (by rfl) (by rfl)
    leaf4326FlatSound leaf4327FlatSound

private noncomputable def component88Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (33/128), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component88Node35_sound : Sound component88Node35Box :=
  sound_of_literal_split component88Node35Box leaf4328Box leaf4329Box
    .chi (67/256) (by rfl) (by rfl)
    leaf4328FlatSound leaf4329FlatSound

private noncomputable def component88Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (33/128), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component88Node36_sound : Sound component88Node36Box :=
  sound_of_literal_split component88Node36Box component88Node34Box component88Node35Box
    .k (101/32) (by rfl) (by rfl)
    component88Node34_sound component88Node35_sound

private noncomputable def component88Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component88Node37_sound : Sound component88Node37Box :=
  sound_of_literal_split component88Node37Box component88Node33Box component88Node36Box
    .chi (33/128) (by rfl) (by rfl)
    component88Node33_sound component88Node36_sound

private noncomputable def component88Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (1/4), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component88Node38_sound : Sound component88Node38Box :=
  sound_of_literal_split component88Node38Box leaf4330Box leaf4331Box
    .chi (65/256) (by rfl) (by rfl)
    leaf4330FlatSound leaf4331FlatSound

private noncomputable def component88Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (1/4), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component88Node39_sound : Sound component88Node39Box :=
  sound_of_literal_split component88Node39Box leaf4332Box leaf4333Box
    .chi (65/256) (by rfl) (by rfl)
    leaf4332FlatSound leaf4333FlatSound

private noncomputable def component88Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (1/4), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component88Node40_sound : Sound component88Node40Box :=
  sound_of_literal_split component88Node40Box component88Node38Box component88Node39Box
    .k (103/32) (by rfl) (by rfl)
    component88Node38_sound component88Node39_sound

private noncomputable def component88Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (33/128), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component88Node41_sound : Sound component88Node41Box :=
  sound_of_literal_split component88Node41Box leaf4334Box leaf4335Box
    .chi (67/256) (by rfl) (by rfl)
    leaf4334FlatSound leaf4335FlatSound

private noncomputable def component88Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (33/128), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component88Node42_sound : Sound component88Node42Box :=
  sound_of_literal_split component88Node42Box leaf4336Box leaf4337Box
    .chi (67/256) (by rfl) (by rfl)
    leaf4336FlatSound leaf4337FlatSound

private noncomputable def component88Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (33/128), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component88Node43_sound : Sound component88Node43Box :=
  sound_of_literal_split component88Node43Box component88Node41Box component88Node42Box
    .k (103/32) (by rfl) (by rfl)
    component88Node41_sound component88Node42_sound

private noncomputable def component88Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component88Node44_sound : Sound component88Node44Box :=
  sound_of_literal_split component88Node44Box component88Node40Box component88Node43Box
    .chi (33/128) (by rfl) (by rfl)
    component88Node40_sound component88Node43_sound

private noncomputable def component88Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component88Node45_sound : Sound component88Node45Box :=
  sound_of_literal_split component88Node45Box component88Node37Box component88Node44Box
    .k (51/16) (by rfl) (by rfl)
    component88Node37_sound component88Node44_sound

private noncomputable def component88Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (17/64), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component88Node46_sound : Sound component88Node46Box :=
  sound_of_literal_split component88Node46Box leaf4338Box leaf4339Box
    .chi (69/256) (by rfl) (by rfl)
    leaf4338FlatSound leaf4339FlatSound

private noncomputable def component88Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (17/64), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component88Node47_sound : Sound component88Node47Box :=
  sound_of_literal_split component88Node47Box leaf4340Box leaf4341Box
    .chi (69/256) (by rfl) (by rfl)
    leaf4340FlatSound leaf4341FlatSound

private noncomputable def component88Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (17/64), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component88Node48_sound : Sound component88Node48Box :=
  sound_of_literal_split component88Node48Box component88Node46Box component88Node47Box
    .k (101/32) (by rfl) (by rfl)
    component88Node46_sound component88Node47_sound

private noncomputable def component88Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (35/128), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component88Node49_sound : Sound component88Node49Box :=
  sound_of_literal_split component88Node49Box leaf4342Box leaf4343Box
    .chi (71/256) (by rfl) (by rfl)
    leaf4342FlatSound leaf4343FlatSound

private noncomputable def component88Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (35/128), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component88Node50_sound : Sound component88Node50Box :=
  sound_of_literal_split component88Node50Box leaf4344Box leaf4345Box
    .chi (71/256) (by rfl) (by rfl)
    leaf4344FlatSound leaf4345FlatSound

private noncomputable def component88Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (35/128), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component88Node51_sound : Sound component88Node51Box :=
  sound_of_literal_split component88Node51Box component88Node49Box component88Node50Box
    .k (101/32) (by rfl) (by rfl)
    component88Node49_sound component88Node50_sound

private noncomputable def component88Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component88Node52_sound : Sound component88Node52Box :=
  sound_of_literal_split component88Node52Box component88Node48Box component88Node51Box
    .chi (35/128) (by rfl) (by rfl)
    component88Node48_sound component88Node51_sound

private noncomputable def component88Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (17/64), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component88Node53_sound : Sound component88Node53Box :=
  sound_of_literal_split component88Node53Box leaf4346Box leaf4347Box
    .chi (69/256) (by rfl) (by rfl)
    leaf4346FlatSound leaf4347FlatSound

private noncomputable def component88Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (17/64), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component88Node54_sound : Sound component88Node54Box :=
  sound_of_literal_split component88Node54Box leaf4348Box leaf4349Box
    .chi (69/256) (by rfl) (by rfl)
    leaf4348FlatSound leaf4349FlatSound

private noncomputable def component88Node55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (17/64), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component88Node55_sound : Sound component88Node55Box :=
  sound_of_literal_split component88Node55Box component88Node53Box component88Node54Box
    .k (103/32) (by rfl) (by rfl)
    component88Node53_sound component88Node54_sound

private noncomputable def component88Node56Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (35/128), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component88Node56_sound : Sound component88Node56Box :=
  sound_of_literal_split component88Node56Box leaf4350Box leaf4351Box
    .chi (71/256) (by rfl) (by rfl)
    leaf4350FlatSound leaf4351FlatSound

private noncomputable def component88Node57Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (35/128), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component88Node57_sound : Sound component88Node57Box :=
  sound_of_literal_split component88Node57Box leaf4352Box leaf4353Box
    .chi (71/256) (by rfl) (by rfl)
    leaf4352FlatSound leaf4353FlatSound

private noncomputable def component88Node58Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (35/128), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component88Node58_sound : Sound component88Node58Box :=
  sound_of_literal_split component88Node58Box component88Node56Box component88Node57Box
    .k (103/32) (by rfl) (by rfl)
    component88Node56_sound component88Node57_sound

private noncomputable def component88Node59Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component88Node59_sound : Sound component88Node59Box :=
  sound_of_literal_split component88Node59Box component88Node55Box component88Node58Box
    .chi (35/128) (by rfl) (by rfl)
    component88Node55_sound component88Node58_sound

private noncomputable def component88Node60Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component88Node60_sound : Sound component88Node60Box :=
  sound_of_literal_split component88Node60Box component88Node52Box component88Node59Box
    .k (51/16) (by rfl) (by rfl)
    component88Node52_sound component88Node59_sound

private noncomputable def component88Node61Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (1/4), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component88Node61_sound : Sound component88Node61Box :=
  sound_of_literal_split component88Node61Box component88Node45Box component88Node60Box
    .chi (17/64) (by rfl) (by rfl)
    component88Node45_sound component88Node60_sound

noncomputable def component88Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (13/4), chiLo := (1/4), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
theorem component88_sound : Sound component88Box :=
  sound_of_literal_split component88Box component88Node30Box component88Node61Box
    .k (25/8) (by rfl) (by rfl)
    component88Node30_sound component88Node61_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
