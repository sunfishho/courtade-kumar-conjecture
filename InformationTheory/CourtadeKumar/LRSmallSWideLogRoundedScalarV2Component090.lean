import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch7
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch8
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

private noncomputable def leaf4412Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (1/4), chiHi := (65/256) }

private noncomputable def leaf4412Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871251/536870912) }, vSqrt := { lower := (65529/65536), upper := (4042264335/4042116608) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (973018799/536870912) }, upper := { exponent := 0, mantissa := (15017/8192) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi277LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (8084380943/8084233216) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf4412InnerLog : WideLogData :=
  innerPair220Data

set_option maxRecDepth 1000000 in
private theorem leaf4412LocalValidity :
    LeafFacts leaf4412Box leaf4412Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4412Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4042264335/4042116608) }) = true
      norm_num [leaf4412Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4412CertificateValid :
    WideCertificateValid leaf4412Box leaf4412Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi277ValidityFacts
    leaf4412LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4412CoverageChecked :
    coverageCheck (innerAD leaf4412Box) leaf4412InnerLog = true := by
  rfl'

private theorem leaf4412InnerLogValid :
    leaf4412InnerLog.Valid 8 (innerAD leaf4412Box) :=
  wideLogDataValid_of_cachedCheck endpoint67PositiveFacts
    endpoint61PositiveFacts.valid leaf4412CoverageChecked

private noncomputable def leaf4412InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629387/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4412InputLogOnePlusV_eq :
    leaf4412InputLogOnePlusV = outerEnclosure 24
      (leaf4412Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4412RoundedFacts : LeafRoundedFacts 8
    leaf4412Certificate.logOnePlusV leaf4412InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4412InputLogOnePlusV_eq }

private noncomputable def leaf4412Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi277InputQChi innerPair220Input
    leaf4412InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4412LowerChecked :
    lowerCheck 24 leaf4412Box leaf4412Inputs = true := by
  rfl'

private theorem leaf4412CoversExact : CoversExact 8
    leaf4412Box leaf4412Certificate leaf4412InnerLog leaf4412Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi277RoundedFacts
    innerPair220RoundedFacts leaf4412RoundedFacts (by rfl)

private theorem leaf4412FlatSound : Sound leaf4412Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4412CertificateValid
    leaf4412InnerLogValid leaf4412CoversExact leaf4412LowerChecked

private noncomputable def leaf4413Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (65/256), chiHi := (33/128) }

private noncomputable def leaf4413Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871253/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715928576) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (979834125/536870912) }, upper := { exponent := 0, mantissa := (7561/4096) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi278LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434422271/137431857152) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf4413InnerLog : WideLogData :=
  innerPair99Data

set_option maxRecDepth 1000000 in
private theorem leaf4413LocalValidity :
    LeafFacts leaf4413Box leaf4413Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4413Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715928576) }) = true
      norm_num [leaf4413Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4413CertificateValid :
    WideCertificateValid leaf4413Box leaf4413Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi278ValidityFacts
    leaf4413LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4413CoverageChecked :
    coverageCheck (innerAD leaf4413Box) leaf4413InnerLog = true := by
  rfl'

private theorem leaf4413InnerLogValid :
    leaf4413InnerLog.Valid 8 (innerAD leaf4413Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint211PositiveFacts.valid leaf4413CoverageChecked

private noncomputable def leaf4413InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814697/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4413InputLogOnePlusV_eq :
    leaf4413InputLogOnePlusV = outerEnclosure 24
      (leaf4413Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4413RoundedFacts : LeafRoundedFacts 8
    leaf4413Certificate.logOnePlusV leaf4413InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4413InputLogOnePlusV_eq }

private noncomputable def leaf4413Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi278InputQChi innerPair99Input
    leaf4413InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4413LowerChecked :
    lowerCheck 24 leaf4413Box leaf4413Inputs = true := by
  rfl'

private theorem leaf4413CoversExact : CoversExact 8
    leaf4413Box leaf4413Certificate leaf4413InnerLog leaf4413Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi278RoundedFacts
    innerPair99RoundedFacts leaf4413RoundedFacts (by rfl)

private theorem leaf4413FlatSound : Sound leaf4413Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4413CertificateValid
    leaf4413InnerLogValid leaf4413CoversExact leaf4413LowerChecked

private noncomputable def leaf4414Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (1/4), chiHi := (65/256) }

private noncomputable def leaf4414Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871253/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905316352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (977212845/536870912) }, upper := { exponent := 0, mantissa := (7541/4096) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi277LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811480917/45810632704) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf4414InnerLog : WideLogData :=
  innerPair94Data

set_option maxRecDepth 1000000 in
private theorem leaf4414LocalValidity :
    LeafFacts leaf4414Box leaf4414Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4414Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905316352) }) = true
      norm_num [leaf4414Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4414CertificateValid :
    WideCertificateValid leaf4414Box leaf4414Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi277ValidityFacts
    leaf4414LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4414CoverageChecked :
    coverageCheck (innerAD leaf4414Box) leaf4414InnerLog = true := by
  rfl'

private theorem leaf4414InnerLogValid :
    leaf4414InnerLog.Valid 8 (innerAD leaf4414Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint61PositiveFacts.valid leaf4414CoverageChecked

private noncomputable def leaf4414InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629391/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4414InputLogOnePlusV_eq :
    leaf4414InputLogOnePlusV = outerEnclosure 24
      (leaf4414Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4414RoundedFacts : LeafRoundedFacts 8
    leaf4414Certificate.logOnePlusV leaf4414InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4414InputLogOnePlusV_eq }

private noncomputable def leaf4414Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi277InputQChi innerPair94Input
    leaf4414InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4414LowerChecked :
    lowerCheck 24 leaf4414Box leaf4414Inputs = true := by
  rfl'

private theorem leaf4414CoversExact : CoversExact 8
    leaf4414Box leaf4414Certificate leaf4414InnerLog leaf4414Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi277RoundedFacts
    innerPair94RoundedFacts leaf4414RoundedFacts (by rfl)

private theorem leaf4414FlatSound : Sound leaf4414Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4414CertificateValid
    leaf4414InnerLogValid leaf4414CoversExact leaf4414LowerChecked

private noncomputable def leaf4415Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (65/256), chiHi := (33/128) }

private noncomputable def leaf4415Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871255/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715894784) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (984093703/536870912) }, upper := { exponent := 0, mantissa := (3797/2048) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi278LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434388479/137431789568) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf4415InnerLog : WideLogData :=
  innerPair214Data

set_option maxRecDepth 1000000 in
private theorem leaf4415LocalValidity :
    LeafFacts leaf4415Box leaf4415Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4415Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715894784) }) = true
      norm_num [leaf4415Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4415CertificateValid :
    WideCertificateValid leaf4415Box leaf4415Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi278ValidityFacts
    leaf4415LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4415CoverageChecked :
    coverageCheck (innerAD leaf4415Box) leaf4415InnerLog = true := by
  rfl'

private theorem leaf4415InnerLogValid :
    leaf4415InnerLog.Valid 8 (innerAD leaf4415Box) :=
  wideLogDataValid_of_cachedCheck endpoint64PositiveFacts
    endpoint211PositiveFacts.valid leaf4415CoverageChecked

private noncomputable def leaf4415InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814699/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4415InputLogOnePlusV_eq :
    leaf4415InputLogOnePlusV = outerEnclosure 24
      (leaf4415Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4415RoundedFacts : LeafRoundedFacts 8
    leaf4415Certificate.logOnePlusV leaf4415InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4415InputLogOnePlusV_eq }

private noncomputable def leaf4415Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi278InputQChi innerPair214Input
    leaf4415InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4415LowerChecked :
    lowerCheck 24 leaf4415Box leaf4415Inputs = true := by
  rfl'

private theorem leaf4415CoversExact : CoversExact 8
    leaf4415Box leaf4415Certificate leaf4415InnerLog leaf4415Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi278RoundedFacts
    innerPair214RoundedFacts leaf4415RoundedFacts (by rfl)

private theorem leaf4415FlatSound : Sound leaf4415Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4415CertificateValid
    leaf4415InnerLogValid leaf4415CoversExact leaf4415LowerChecked

private noncomputable def leaf4416Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (33/128), chiHi := (67/256) }

private noncomputable def leaf4416Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871255/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715874816) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (986649451/536870912) }, upper := { exponent := 0, mantissa := (15227/8192) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi275LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434368511/137431749632) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf4416InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf4416LocalValidity :
    LeafFacts leaf4416Box leaf4416Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4416Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715874816) }) = true
      norm_num [leaf4416Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4416CertificateValid :
    WideCertificateValid leaf4416Box leaf4416Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi275ValidityFacts
    leaf4416LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4416CoverageChecked :
    coverageCheck (innerAD leaf4416Box) leaf4416InnerLog = true := by
  rfl'

private theorem leaf4416InnerLogValid :
    leaf4416InnerLog.Valid 8 (innerAD leaf4416Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf4416CoverageChecked

private noncomputable def leaf4416InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453675/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf4416InputLogOnePlusV_eq :
    leaf4416InputLogOnePlusV = outerEnclosure 24
      (leaf4416Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4416RoundedFacts : LeafRoundedFacts 8
    leaf4416Certificate.logOnePlusV leaf4416InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4416InputLogOnePlusV_eq }

private noncomputable def leaf4416Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi275InputQChi innerPair91Input
    leaf4416InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4416LowerChecked :
    lowerCheck 24 leaf4416Box leaf4416Inputs = true := by
  rfl'

private theorem leaf4416CoversExact : CoversExact 8
    leaf4416Box leaf4416Certificate leaf4416InnerLog leaf4416Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi275RoundedFacts
    innerPair91RoundedFacts leaf4416RoundedFacts (by rfl)

private theorem leaf4416FlatSound : Sound leaf4416Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4416CertificateValid
    leaf4416InnerLogValid leaf4416CoversExact leaf4416LowerChecked

private noncomputable def leaf4417Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (67/256), chiHi := (17/64) }

private noncomputable def leaf4417Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871257/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715821056) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (993464777/536870912) }, upper := { exponent := 0, mantissa := (3833/2048) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi276LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434314751/137431642112) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf4417InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf4417LocalValidity :
    LeafFacts leaf4417Box leaf4417Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4417Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715821056) }) = true
      norm_num [leaf4417Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4417CertificateValid :
    WideCertificateValid leaf4417Box leaf4417Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi276ValidityFacts
    leaf4417LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4417CoverageChecked :
    coverageCheck (innerAD leaf4417Box) leaf4417InnerLog = true := by
  rfl'

private theorem leaf4417InnerLogValid :
    leaf4417InnerLog.Valid 8 (innerAD leaf4417Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf4417CoverageChecked

private noncomputable def leaf4417InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629407/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4417InputLogOnePlusV_eq :
    leaf4417InputLogOnePlusV = outerEnclosure 24
      (leaf4417Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4417RoundedFacts : LeafRoundedFacts 8
    leaf4417Certificate.logOnePlusV leaf4417InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4417InputLogOnePlusV_eq }

private noncomputable def leaf4417Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi276InputQChi innerPair91Input
    leaf4417InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4417LowerChecked :
    lowerCheck 24 leaf4417Box leaf4417Inputs = true := by
  rfl'

private theorem leaf4417CoversExact : CoversExact 8
    leaf4417Box leaf4417Certificate leaf4417InnerLog leaf4417Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi276RoundedFacts
    innerPair91RoundedFacts leaf4417RoundedFacts (by rfl)

private theorem leaf4417FlatSound : Sound leaf4417Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4417CertificateValid
    leaf4417InnerLogValid leaf4417CoversExact leaf4417LowerChecked

private noncomputable def leaf4418Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (33/128), chiHi := (67/256) }

private noncomputable def leaf4418Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871257/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715840512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (990974561/536870912) }, upper := { exponent := 0, mantissa := (7647/4096) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi275LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434334207/137431681024) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf4418InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf4418LocalValidity :
    LeafFacts leaf4418Box leaf4418Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4418Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715840512) }) = true
      norm_num [leaf4418Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4418CertificateValid :
    WideCertificateValid leaf4418Box leaf4418Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi275ValidityFacts
    leaf4418LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4418CoverageChecked :
    coverageCheck (innerAD leaf4418Box) leaf4418InnerLog = true := by
  rfl'

private theorem leaf4418InnerLogValid :
    leaf4418InnerLog.Valid 8 (innerAD leaf4418Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf4418CoverageChecked

private noncomputable def leaf4418InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629405/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4418InputLogOnePlusV_eq :
    leaf4418InputLogOnePlusV = outerEnclosure 24
      (leaf4418Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4418RoundedFacts : LeafRoundedFacts 8
    leaf4418Certificate.logOnePlusV leaf4418InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4418InputLogOnePlusV_eq }

private noncomputable def leaf4418Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi275InputQChi innerPair91Input
    leaf4418InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4418LowerChecked :
    lowerCheck 24 leaf4418Box leaf4418Inputs = true := by
  rfl'

private theorem leaf4418CoversExact : CoversExact 8
    leaf4418Box leaf4418Certificate leaf4418InnerLog leaf4418Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi275RoundedFacts
    innerPair91RoundedFacts leaf4418RoundedFacts (by rfl)

private theorem leaf4418FlatSound : Sound leaf4418Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4418CertificateValid
    leaf4418InnerLogValid leaf4418CoversExact leaf4418LowerChecked

private noncomputable def leaf4419Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (67/256), chiHi := (17/64) }

private noncomputable def leaf4419Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871259/536870912) }, vSqrt := { lower := (65529/65536), upper := (4581232913/4581052416) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (997855419/536870912) }, upper := { exponent := 0, mantissa := (1925/1024) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi276LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9162285329/9162104832) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf4419InnerLog : WideLogData :=
  innerPair199Data

set_option maxRecDepth 1000000 in
private theorem leaf4419LocalValidity :
    LeafFacts leaf4419Box leaf4419Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4419Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4581232913/4581052416) }) = true
      norm_num [leaf4419Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4419CertificateValid :
    WideCertificateValid leaf4419Box leaf4419Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi276ValidityFacts
    leaf4419LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4419CoverageChecked :
    coverageCheck (innerAD leaf4419Box) leaf4419InnerLog = true := by
  rfl'

private theorem leaf4419InnerLogValid :
    leaf4419InnerLog.Valid 8 (innerAD leaf4419Box) :=
  wideLogDataValid_of_cachedCheck endpoint61PositiveFacts
    endpoint69PositiveFacts.valid leaf4419CoverageChecked

private noncomputable def leaf4419InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629411/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4419InputLogOnePlusV_eq :
    leaf4419InputLogOnePlusV = outerEnclosure 24
      (leaf4419Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4419RoundedFacts : LeafRoundedFacts 8
    leaf4419Certificate.logOnePlusV leaf4419InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4419InputLogOnePlusV_eq }

private noncomputable def leaf4419Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi276InputQChi innerPair199Input
    leaf4419InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4419LowerChecked :
    lowerCheck 24 leaf4419Box leaf4419Inputs = true := by
  rfl'

private theorem leaf4419CoversExact : CoversExact 8
    leaf4419Box leaf4419Certificate leaf4419InnerLog leaf4419Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi276RoundedFacts
    innerPair199RoundedFacts leaf4419RoundedFacts (by rfl)

private theorem leaf4419FlatSound : Sound leaf4419Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4419CertificateValid
    leaf4419InnerLogValid leaf4419CoversExact leaf4419LowerChecked

private noncomputable def leaf4420Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (1/4), chiHi := (65/256) }

private noncomputable def leaf4420Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871255/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715915776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (981406891/536870912) }, upper := { exponent := 0, mantissa := (15147/8192) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi277LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434409471/137431831552) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf4420InnerLog : WideLogData :=
  innerPair471Data

set_option maxRecDepth 1000000 in
private theorem leaf4420LocalValidity :
    LeafFacts leaf4420Box leaf4420Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4420Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715915776) }) = true
      norm_num [leaf4420Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4420CertificateValid :
    WideCertificateValid leaf4420Box leaf4420Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi277ValidityFacts
    leaf4420LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4420CoverageChecked :
    coverageCheck (innerAD leaf4420Box) leaf4420InnerLog = true := by
  rfl'

private theorem leaf4420InnerLogValid :
    leaf4420InnerLog.Valid 8 (innerAD leaf4420Box) :=
  wideLogDataValid_of_cachedCheck endpoint188PositiveFacts
    endpoint237PositiveFacts.valid leaf4420CoverageChecked

private noncomputable def leaf4420InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629395/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4420InputLogOnePlusV_eq :
    leaf4420InputLogOnePlusV = outerEnclosure 24
      (leaf4420Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4420RoundedFacts : LeafRoundedFacts 8
    leaf4420Certificate.logOnePlusV leaf4420InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4420InputLogOnePlusV_eq }

private noncomputable def leaf4420Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi277InputQChi innerPair471Input
    leaf4420InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4420LowerChecked :
    lowerCheck 24 leaf4420Box leaf4420Inputs = true := by
  rfl'

private theorem leaf4420CoversExact : CoversExact 8
    leaf4420Box leaf4420Certificate leaf4420InnerLog leaf4420Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi277RoundedFacts
    innerPair471RoundedFacts leaf4420RoundedFacts (by rfl)

private theorem leaf4420FlatSound : Sound leaf4420Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4420CertificateValid
    leaf4420InnerLogValid leaf4420CoversExact leaf4420LowerChecked

private noncomputable def leaf4421Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (65/256), chiHi := (33/128) }

private noncomputable def leaf4421Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871257/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715860992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (988353281/536870912) }, upper := { exponent := 0, mantissa := (7627/4096) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi278LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434354687/137431721984) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf4421InnerLog : WideLogData :=
  innerPair507Data

set_option maxRecDepth 1000000 in
private theorem leaf4421LocalValidity :
    LeafFacts leaf4421Box leaf4421Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4421Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715860992) }) = true
      norm_num [leaf4421Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4421CertificateValid :
    WideCertificateValid leaf4421Box leaf4421Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi278ValidityFacts
    leaf4421LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4421CoverageChecked :
    coverageCheck (innerAD leaf4421Box) leaf4421InnerLog = true := by
  rfl'

private theorem leaf4421InnerLogValid :
    leaf4421InnerLog.Valid 8 (innerAD leaf4421Box) :=
  wideLogDataValid_of_cachedCheck endpoint236PositiveFacts
    endpoint241PositiveFacts.valid leaf4421CoverageChecked

private noncomputable def leaf4421InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814701/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4421InputLogOnePlusV_eq :
    leaf4421InputLogOnePlusV = outerEnclosure 24
      (leaf4421Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4421RoundedFacts : LeafRoundedFacts 8
    leaf4421Certificate.logOnePlusV leaf4421InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4421InputLogOnePlusV_eq }

private noncomputable def leaf4421Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi278InputQChi innerPair507Input
    leaf4421InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4421LowerChecked :
    lowerCheck 24 leaf4421Box leaf4421Inputs = true := by
  rfl'

private theorem leaf4421CoversExact : CoversExact 8
    leaf4421Box leaf4421Certificate leaf4421InnerLog leaf4421Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi278RoundedFacts
    innerPair507RoundedFacts leaf4421RoundedFacts (by rfl)

private theorem leaf4421FlatSound : Sound leaf4421Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4421CertificateValid
    leaf4421InnerLogValid leaf4421CoversExact leaf4421LowerChecked

private noncomputable def leaf4422Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (1/4), chiHi := (65/256) }

private noncomputable def leaf4422Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871257/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715882496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (985600937/536870912) }, upper := { exponent := 0, mantissa := (3803/2048) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi277LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434376191/137431764992) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf4422InnerLog : WideLogData :=
  innerPair597Data

set_option maxRecDepth 1000000 in
private theorem leaf4422LocalValidity :
    LeafFacts leaf4422Box leaf4422Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4422Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715882496) }) = true
      norm_num [leaf4422Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4422CertificateValid :
    WideCertificateValid leaf4422Box leaf4422Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi277ValidityFacts
    leaf4422LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4422CoverageChecked :
    coverageCheck (innerAD leaf4422Box) leaf4422InnerLog = true := by
  rfl'

private theorem leaf4422InnerLogValid :
    leaf4422InnerLog.Valid 8 (innerAD leaf4422Box) :=
  wideLogDataValid_of_cachedCheck endpoint313PositiveFacts
    endpoint253PositiveFacts.valid leaf4422CoverageChecked

private noncomputable def leaf4422InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453675/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf4422InputLogOnePlusV_eq :
    leaf4422InputLogOnePlusV = outerEnclosure 24
      (leaf4422Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4422RoundedFacts : LeafRoundedFacts 8
    leaf4422Certificate.logOnePlusV leaf4422InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4422InputLogOnePlusV_eq }

private noncomputable def leaf4422Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi277InputQChi innerPair597Input
    leaf4422InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4422LowerChecked :
    lowerCheck 24 leaf4422Box leaf4422Inputs = true := by
  rfl'

private theorem leaf4422CoversExact : CoversExact 8
    leaf4422Box leaf4422Certificate leaf4422InnerLog leaf4422Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi277RoundedFacts
    innerPair597RoundedFacts leaf4422RoundedFacts (by rfl)

private theorem leaf4422FlatSound : Sound leaf4422Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4422CertificateValid
    leaf4422InnerLogValid leaf4422CoversExact leaf4422LowerChecked

private noncomputable def leaf4423Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (65/256), chiHi := (33/128) }

private noncomputable def leaf4423Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871259/536870912) }, vSqrt := { lower := (65529/65536), upper := (13743698739/13743165440) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (992612859/536870912) }, upper := { exponent := 0, mantissa := (1915/1024) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi278LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (27486864179/27486330880) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf4423InnerLog : WideLogData :=
  innerPair500Data

set_option maxRecDepth 1000000 in
private theorem leaf4423LocalValidity :
    LeafFacts leaf4423Box leaf4423Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4423Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (13743698739/13743165440) }) = true
      norm_num [leaf4423Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4423CertificateValid :
    WideCertificateValid leaf4423Box leaf4423Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi278ValidityFacts
    leaf4423LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4423CoverageChecked :
    coverageCheck (innerAD leaf4423Box) leaf4423InnerLog = true := by
  rfl'

private theorem leaf4423InnerLogValid :
    leaf4423InnerLog.Valid 8 (innerAD leaf4423Box) :=
  wideLogDataValid_of_cachedCheck endpoint223PositiveFacts
    endpoint243PositiveFacts.valid leaf4423CoverageChecked

private noncomputable def leaf4423InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814703/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4423InputLogOnePlusV_eq :
    leaf4423InputLogOnePlusV = outerEnclosure 24
      (leaf4423Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4423RoundedFacts : LeafRoundedFacts 8
    leaf4423Certificate.logOnePlusV leaf4423InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4423InputLogOnePlusV_eq }

private noncomputable def leaf4423Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi278InputQChi innerPair500Input
    leaf4423InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4423LowerChecked :
    lowerCheck 24 leaf4423Box leaf4423Inputs = true := by
  rfl'

private theorem leaf4423CoversExact : CoversExact 8
    leaf4423Box leaf4423Certificate leaf4423InnerLog leaf4423Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi278RoundedFacts
    innerPair500RoundedFacts leaf4423RoundedFacts (by rfl)

private theorem leaf4423FlatSound : Sound leaf4423Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4423CertificateValid
    leaf4423InnerLogValid leaf4423CoversExact leaf4423LowerChecked

private noncomputable def leaf4424Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (33/128), chiHi := (67/256) }

private noncomputable def leaf4424Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871259/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905268736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (995299671/536870912) }, upper := { exponent := 0, mantissa := (15361/8192) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi275LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811433301/45810537472) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf4424InnerLog : WideLogData :=
  innerPair509Data

set_option maxRecDepth 1000000 in
private theorem leaf4424LocalValidity :
    LeafFacts leaf4424Box leaf4424Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4424Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905268736) }) = true
      norm_num [leaf4424Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4424CertificateValid :
    WideCertificateValid leaf4424Box leaf4424Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi275ValidityFacts
    leaf4424LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4424CoverageChecked :
    coverageCheck (innerAD leaf4424Box) leaf4424InnerLog = true := by
  rfl'

private theorem leaf4424InnerLogValid :
    leaf4424InnerLog.Valid 8 (innerAD leaf4424Box) :=
  wideLogDataValid_of_cachedCheck endpoint237PositiveFacts
    endpoint242PositiveFacts.valid leaf4424CoverageChecked

private noncomputable def leaf4424InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629409/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4424InputLogOnePlusV_eq :
    leaf4424InputLogOnePlusV = outerEnclosure 24
      (leaf4424Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4424RoundedFacts : LeafRoundedFacts 8
    leaf4424Certificate.logOnePlusV leaf4424InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4424InputLogOnePlusV_eq }

private noncomputable def leaf4424Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi275InputQChi innerPair509Input
    leaf4424InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4424LowerChecked :
    lowerCheck 24 leaf4424Box leaf4424Inputs = true := by
  rfl'

private theorem leaf4424CoversExact : CoversExact 8
    leaf4424Box leaf4424Certificate leaf4424InnerLog leaf4424Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi275RoundedFacts
    innerPair509RoundedFacts leaf4424RoundedFacts (by rfl)

private theorem leaf4424FlatSound : Sound leaf4424Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4424CertificateValid
    leaf4424InnerLogValid leaf4424CoversExact leaf4424LowerChecked

private noncomputable def leaf4425Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (67/256), chiHi := (17/64) }

private noncomputable def leaf4425Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871261/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715751424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1002246061/536870912) }, upper := { exponent := 0, mantissa := (3867/2048) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi276LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434245119/137431502848) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf4425InnerLog : WideLogData :=
  innerPair482Data

set_option maxRecDepth 1000000 in
private theorem leaf4425LocalValidity :
    LeafFacts leaf4425Box leaf4425Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4425Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715751424) }) = true
      norm_num [leaf4425Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4425CertificateValid :
    WideCertificateValid leaf4425Box leaf4425Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi276ValidityFacts
    leaf4425LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4425CoverageChecked :
    coverageCheck (innerAD leaf4425Box) leaf4425InnerLog = true := by
  rfl'

private theorem leaf4425InnerLogValid :
    leaf4425InnerLog.Valid 8 (innerAD leaf4425Box) :=
  wideLogDataValid_of_cachedCheck endpoint211PositiveFacts
    endpoint69PositiveFacts.valid leaf4425CoverageChecked

private noncomputable def leaf4425InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453677/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf4425InputLogOnePlusV_eq :
    leaf4425InputLogOnePlusV = outerEnclosure 24
      (leaf4425Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4425RoundedFacts : LeafRoundedFacts 8
    leaf4425Certificate.logOnePlusV leaf4425InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4425InputLogOnePlusV_eq }

private noncomputable def leaf4425Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi276InputQChi innerPair482Input
    leaf4425InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4425LowerChecked :
    lowerCheck 24 leaf4425Box leaf4425Inputs = true := by
  rfl'

private theorem leaf4425CoversExact : CoversExact 8
    leaf4425Box leaf4425Certificate leaf4425InnerLog leaf4425Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi276RoundedFacts
    innerPair482RoundedFacts leaf4425RoundedFacts (by rfl)

private theorem leaf4425FlatSound : Sound leaf4425Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4425CertificateValid
    leaf4425InnerLogValid leaf4425CoversExact leaf4425LowerChecked

private noncomputable def leaf4426Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (33/128), chiHi := (67/256) }

private noncomputable def leaf4426Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871261/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715771904) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (999624781/536870912) }, upper := { exponent := 0, mantissa := (3857/2048) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi275LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434265599/137431543808) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf4426InnerLog : WideLogData :=
  innerPair485Data

set_option maxRecDepth 1000000 in
private theorem leaf4426LocalValidity :
    LeafFacts leaf4426Box leaf4426Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4426Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715771904) }) = true
      norm_num [leaf4426Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4426CertificateValid :
    WideCertificateValid leaf4426Box leaf4426Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi275ValidityFacts
    leaf4426LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4426CoverageChecked :
    coverageCheck (innerAD leaf4426Box) leaf4426InnerLog = true := by
  rfl'

private theorem leaf4426InnerLogValid :
    leaf4426InnerLog.Valid 8 (innerAD leaf4426Box) :=
  wideLogDataValid_of_cachedCheck endpoint211PositiveFacts
    endpoint245PositiveFacts.valid leaf4426CoverageChecked

private noncomputable def leaf4426InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629413/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4426InputLogOnePlusV_eq :
    leaf4426InputLogOnePlusV = outerEnclosure 24
      (leaf4426Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4426RoundedFacts : LeafRoundedFacts 8
    leaf4426Certificate.logOnePlusV leaf4426InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4426InputLogOnePlusV_eq }

private noncomputable def leaf4426Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi275InputQChi innerPair485Input
    leaf4426InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4426LowerChecked :
    lowerCheck 24 leaf4426Box leaf4426Inputs = true := by
  rfl'

private theorem leaf4426CoversExact : CoversExact 8
    leaf4426Box leaf4426Certificate leaf4426InnerLog leaf4426Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi275RoundedFacts
    innerPair485RoundedFacts leaf4426RoundedFacts (by rfl)

private theorem leaf4426FlatSound : Sound leaf4426Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4426CertificateValid
    leaf4426InnerLogValid leaf4426CoversExact leaf4426LowerChecked

private noncomputable def leaf4427Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (67/256), chiHi := (17/64) }

private noncomputable def leaf4427Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871263/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715716608) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1006636703/536870912) }, upper := { exponent := 0, mantissa := (971/512) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi276LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434210303/137431433216) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf4427InnerLog : WideLogData :=
  innerPair107Data

set_option maxRecDepth 1000000 in
private theorem leaf4427LocalValidity :
    LeafFacts leaf4427Box leaf4427Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4427Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715716608) }) = true
      norm_num [leaf4427Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4427CertificateValid :
    WideCertificateValid leaf4427Box leaf4427Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi276ValidityFacts
    leaf4427LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4427CoverageChecked :
    coverageCheck (innerAD leaf4427Box) leaf4427InnerLog = true := by
  rfl'

private theorem leaf4427InnerLogValid :
    leaf4427InnerLog.Valid 8 (innerAD leaf4427Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint257PositiveFacts.valid leaf4427CoverageChecked

private noncomputable def leaf4427InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907355/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4427InputLogOnePlusV_eq :
    leaf4427InputLogOnePlusV = outerEnclosure 24
      (leaf4427Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4427RoundedFacts : LeafRoundedFacts 8
    leaf4427Certificate.logOnePlusV leaf4427InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4427InputLogOnePlusV_eq }

private noncomputable def leaf4427Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi276InputQChi innerPair107Input
    leaf4427InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4427LowerChecked :
    lowerCheck 24 leaf4427Box leaf4427Inputs = true := by
  rfl'

private theorem leaf4427CoversExact : CoversExact 8
    leaf4427Box leaf4427Certificate leaf4427InnerLog leaf4427Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi276RoundedFacts
    innerPair107RoundedFacts leaf4427RoundedFacts (by rfl)

private theorem leaf4427FlatSound : Sound leaf4427Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4427CertificateValid
    leaf4427InnerLogValid leaf4427CoversExact leaf4427LowerChecked

private noncomputable def leaf4428Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (17/64), chiHi := (69/256) }

private noncomputable def leaf4428Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871259/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715767296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1000280103/536870912) }, upper := { exponent := 0, mantissa := (15437/8192) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi257LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434260991/137431534592) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf4428InnerLog : WideLogData :=
  innerPair482Data

set_option maxRecDepth 1000000 in
private theorem leaf4428LocalValidity :
    LeafFacts leaf4428Box leaf4428Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4428Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715767296) }) = true
      norm_num [leaf4428Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4428CertificateValid :
    WideCertificateValid leaf4428Box leaf4428Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi257ValidityFacts
    leaf4428LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4428CoverageChecked :
    coverageCheck (innerAD leaf4428Box) leaf4428InnerLog = true := by
  rfl'

private theorem leaf4428InnerLogValid :
    leaf4428InnerLog.Valid 8 (innerAD leaf4428Box) :=
  wideLogDataValid_of_cachedCheck endpoint211PositiveFacts
    endpoint69PositiveFacts.valid leaf4428CoverageChecked

private noncomputable def leaf4428InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814707/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4428InputLogOnePlusV_eq :
    leaf4428InputLogOnePlusV = outerEnclosure 24
      (leaf4428Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4428RoundedFacts : LeafRoundedFacts 8
    leaf4428Certificate.logOnePlusV leaf4428InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4428InputLogOnePlusV_eq }

private noncomputable def leaf4428Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi257InputQChi innerPair482Input
    leaf4428InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4428LowerChecked :
    lowerCheck 24 leaf4428Box leaf4428Inputs = true := by
  rfl'

private theorem leaf4428CoversExact : CoversExact 8
    leaf4428Box leaf4428Certificate leaf4428InnerLog leaf4428Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi257RoundedFacts
    innerPair482RoundedFacts leaf4428RoundedFacts (by rfl)

private theorem leaf4428FlatSound : Sound leaf4428Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4428CertificateValid
    leaf4428InnerLogValid leaf4428CoversExact leaf4428LowerChecked

private noncomputable def leaf4429Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (69/256), chiHi := (35/128) }

private noncomputable def leaf4429Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871261/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715713536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1007095429/536870912) }, upper := { exponent := 0, mantissa := (7771/4096) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi258LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434207231/137431427072) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf4429InnerLog : WideLogData :=
  innerPair103Data

set_option maxRecDepth 1000000 in
private theorem leaf4429LocalValidity :
    LeafFacts leaf4429Box leaf4429Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4429Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715713536) }) = true
      norm_num [leaf4429Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4429CertificateValid :
    WideCertificateValid leaf4429Box leaf4429Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi258ValidityFacts
    leaf4429LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4429CoverageChecked :
    coverageCheck (innerAD leaf4429Box) leaf4429InnerLog = true := by
  rfl'

private theorem leaf4429InnerLogValid :
    leaf4429InnerLog.Valid 8 (innerAD leaf4429Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint70PositiveFacts.valid leaf4429CoverageChecked

private noncomputable def leaf4429InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907355/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4429InputLogOnePlusV_eq :
    leaf4429InputLogOnePlusV = outerEnclosure 24
      (leaf4429Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4429RoundedFacts : LeafRoundedFacts 8
    leaf4429Certificate.logOnePlusV leaf4429InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4429InputLogOnePlusV_eq }

private noncomputable def leaf4429Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi258InputQChi innerPair103Input
    leaf4429InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4429LowerChecked :
    lowerCheck 24 leaf4429Box leaf4429Inputs = true := by
  rfl'

private theorem leaf4429CoversExact : CoversExact 8
    leaf4429Box leaf4429Certificate leaf4429InnerLog leaf4429Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi258RoundedFacts
    innerPair103RoundedFacts leaf4429RoundedFacts (by rfl)

private theorem leaf4429FlatSound : Sound leaf4429Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4429CertificateValid
    leaf4429InnerLogValid leaf4429CoversExact leaf4429LowerChecked

private noncomputable def leaf4430Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (17/64), chiHi := (69/256) }

private noncomputable def leaf4430Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871261/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715731968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1004736277/536870912) }, upper := { exponent := 0, mantissa := (7753/4096) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi257LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434225663/137431463936) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf4430InnerLog : WideLogData :=
  innerPair483Data

set_option maxRecDepth 1000000 in
private theorem leaf4430LocalValidity :
    LeafFacts leaf4430Box leaf4430Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4430Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715731968) }) = true
      norm_num [leaf4430Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4430CertificateValid :
    WideCertificateValid leaf4430Box leaf4430Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi257ValidityFacts
    leaf4430LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4430CoverageChecked :
    coverageCheck (innerAD leaf4430Box) leaf4430InnerLog = true := by
  rfl'

private theorem leaf4430InnerLogValid :
    leaf4430InnerLog.Valid 8 (innerAD leaf4430Box) :=
  wideLogDataValid_of_cachedCheck endpoint211PositiveFacts
    endpoint70PositiveFacts.valid leaf4430CoverageChecked

private noncomputable def leaf4430InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814709/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4430InputLogOnePlusV_eq :
    leaf4430InputLogOnePlusV = outerEnclosure 24
      (leaf4430Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4430RoundedFacts : LeafRoundedFacts 8
    leaf4430Certificate.logOnePlusV leaf4430InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4430InputLogOnePlusV_eq }

private noncomputable def leaf4430Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi257InputQChi innerPair483Input
    leaf4430InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4430LowerChecked :
    lowerCheck 24 leaf4430Box leaf4430Inputs = true := by
  rfl'

private theorem leaf4430CoversExact : CoversExact 8
    leaf4430Box leaf4430Certificate leaf4430InnerLog leaf4430Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi257RoundedFacts
    innerPair483RoundedFacts leaf4430RoundedFacts (by rfl)

private theorem leaf4430FlatSound : Sound leaf4430Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4430CertificateValid
    leaf4430InnerLogValid leaf4430CoversExact leaf4430LowerChecked

private noncomputable def leaf4431Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (69/256), chiHi := (35/128) }

private noncomputable def leaf4431Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871263/536870912) }, vSqrt := { lower := (65529/65536), upper := (4042264335/4042098688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1011617135/536870912) }, upper := { exponent := 0, mantissa := (3903/2048) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi258LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (8084363023/8084197376) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf4431InnerLog : WideLogData :=
  innerPair103Data

set_option maxRecDepth 1000000 in
private theorem leaf4431LocalValidity :
    LeafFacts leaf4431Box leaf4431Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4431Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4042264335/4042098688) }) = true
      norm_num [leaf4431Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4431CertificateValid :
    WideCertificateValid leaf4431Box leaf4431Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi258ValidityFacts
    leaf4431LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4431CoverageChecked :
    coverageCheck (innerAD leaf4431Box) leaf4431InnerLog = true := by
  rfl'

private theorem leaf4431InnerLogValid :
    leaf4431InnerLog.Valid 8 (innerAD leaf4431Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint70PositiveFacts.valid leaf4431CoverageChecked

private noncomputable def leaf4431InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629425/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4431InputLogOnePlusV_eq :
    leaf4431InputLogOnePlusV = outerEnclosure 24
      (leaf4431Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4431RoundedFacts : LeafRoundedFacts 8
    leaf4431Certificate.logOnePlusV leaf4431InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4431InputLogOnePlusV_eq }

private noncomputable def leaf4431Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi258InputQChi innerPair103Input
    leaf4431InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4431LowerChecked :
    lowerCheck 24 leaf4431Box leaf4431Inputs = true := by
  rfl'

private theorem leaf4431CoversExact : CoversExact 8
    leaf4431Box leaf4431Certificate leaf4431InnerLog leaf4431Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi258RoundedFacts
    innerPair103RoundedFacts leaf4431RoundedFacts (by rfl)

private theorem leaf4431FlatSound : Sound leaf4431Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4431CertificateValid
    leaf4431InnerLogValid leaf4431CoversExact leaf4431LowerChecked

private noncomputable def leaf4432Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (35/128), chiHi := (71/256) }

private noncomputable def leaf4432Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871263/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715659776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1013910755/536870912) }, upper := { exponent := 0, mantissa := (15647/8192) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi279LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434153471/137431319552) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf4432InnerLog : WideLogData :=
  innerPair106Data

set_option maxRecDepth 1000000 in
private theorem leaf4432LocalValidity :
    LeafFacts leaf4432Box leaf4432Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4432Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715659776) }) = true
      norm_num [leaf4432Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4432CertificateValid :
    WideCertificateValid leaf4432Box leaf4432Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi279ValidityFacts
    leaf4432LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4432CoverageChecked :
    coverageCheck (innerAD leaf4432Box) leaf4432InnerLog = true := by
  rfl'

private theorem leaf4432InnerLogValid :
    leaf4432InnerLog.Valid 8 (innerAD leaf4432Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint81PositiveFacts.valid leaf4432CoverageChecked

private noncomputable def leaf4432InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629427/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4432InputLogOnePlusV_eq :
    leaf4432InputLogOnePlusV = outerEnclosure 24
      (leaf4432Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4432RoundedFacts : LeafRoundedFacts 8
    leaf4432Certificate.logOnePlusV leaf4432InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4432InputLogOnePlusV_eq }

private noncomputable def leaf4432Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi279InputQChi innerPair106Input
    leaf4432InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4432LowerChecked :
    lowerCheck 24 leaf4432Box leaf4432Inputs = true := by
  rfl'

private theorem leaf4432CoversExact : CoversExact 8
    leaf4432Box leaf4432Certificate leaf4432InnerLog leaf4432Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi279RoundedFacts
    innerPair106RoundedFacts leaf4432RoundedFacts (by rfl)

private theorem leaf4432FlatSound : Sound leaf4432Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4432CertificateValid
    leaf4432InnerLogValid leaf4432CoversExact leaf4432LowerChecked

private noncomputable def leaf4433Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (71/256), chiHi := (9/32) }

private noncomputable def leaf4433Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871265/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715606016) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1020726081/536870912) }, upper := { exponent := 0, mantissa := (1969/1024) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi280LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434099711/137431212032) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf4433InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4433LocalValidity :
    LeafFacts leaf4433Box leaf4433Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4433Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715606016) }) = true
      norm_num [leaf4433Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4433CertificateValid :
    WideCertificateValid leaf4433Box leaf4433Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi280ValidityFacts
    leaf4433LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4433CoverageChecked :
    coverageCheck (innerAD leaf4433Box) leaf4433InnerLog = true := by
  rfl'

private theorem leaf4433InnerLogValid :
    leaf4433InnerLog.Valid 8 (innerAD leaf4433Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4433CoverageChecked

private noncomputable def leaf4433InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629433/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4433InputLogOnePlusV_eq :
    leaf4433InputLogOnePlusV = outerEnclosure 24
      (leaf4433Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4433RoundedFacts : LeafRoundedFacts 8
    leaf4433Certificate.logOnePlusV leaf4433InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4433InputLogOnePlusV_eq }

private noncomputable def leaf4433Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi280InputQChi innerPair100Input
    leaf4433InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4433LowerChecked :
    lowerCheck 24 leaf4433Box leaf4433Inputs = true := by
  rfl'

private theorem leaf4433CoversExact : CoversExact 8
    leaf4433Box leaf4433Certificate leaf4433InnerLog leaf4433Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi280RoundedFacts
    innerPair100RoundedFacts leaf4433RoundedFacts (by rfl)

private theorem leaf4433FlatSound : Sound leaf4433Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4433CertificateValid
    leaf4433InnerLogValid leaf4433CoversExact leaf4433LowerChecked

private noncomputable def leaf4434Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (35/128), chiHi := (71/256) }

private noncomputable def leaf4434Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871265/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905207808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1018497993/536870912) }, upper := { exponent := 0, mantissa := (7859/4096) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi279LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811372373/45810415616) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf4434InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4434LocalValidity :
    LeafFacts leaf4434Box leaf4434Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4434Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905207808) }) = true
      norm_num [leaf4434Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4434CertificateValid :
    WideCertificateValid leaf4434Box leaf4434Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi279ValidityFacts
    leaf4434LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4434CoverageChecked :
    coverageCheck (innerAD leaf4434Box) leaf4434InnerLog = true := by
  rfl'

private theorem leaf4434InnerLogValid :
    leaf4434InnerLog.Valid 8 (innerAD leaf4434Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4434CoverageChecked

private noncomputable def leaf4434InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629431/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4434InputLogOnePlusV_eq :
    leaf4434InputLogOnePlusV = outerEnclosure 24
      (leaf4434Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4434RoundedFacts : LeafRoundedFacts 8
    leaf4434Certificate.logOnePlusV leaf4434InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4434InputLogOnePlusV_eq }

private noncomputable def leaf4434Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi279InputQChi innerPair100Input
    leaf4434InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4434LowerChecked :
    lowerCheck 24 leaf4434Box leaf4434Inputs = true := by
  rfl'

private theorem leaf4434CoversExact : CoversExact 8
    leaf4434Box leaf4434Certificate leaf4434InnerLog leaf4434Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi279RoundedFacts
    innerPair100RoundedFacts leaf4434RoundedFacts (by rfl)

private theorem leaf4434FlatSound : Sound leaf4434Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4434CertificateValid
    leaf4434InnerLogValid leaf4434CoversExact leaf4434LowerChecked

private noncomputable def leaf4435Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (71/256), chiHi := (9/32) }

private noncomputable def leaf4435Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871267/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715569152) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1025378851/536870912) }, upper := { exponent := 0, mantissa := (989/512) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi280LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434062847/137431138304) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf4435InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4435LocalValidity :
    LeafFacts leaf4435Box leaf4435Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4435Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715569152) }) = true
      norm_num [leaf4435Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4435CertificateValid :
    WideCertificateValid leaf4435Box leaf4435Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi280ValidityFacts
    leaf4435LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4435CoverageChecked :
    coverageCheck (innerAD leaf4435Box) leaf4435InnerLog = true := by
  rfl'

private theorem leaf4435InnerLogValid :
    leaf4435InnerLog.Valid 8 (innerAD leaf4435Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4435CoverageChecked

private noncomputable def leaf4435InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814719/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4435InputLogOnePlusV_eq :
    leaf4435InputLogOnePlusV = outerEnclosure 24
      (leaf4435Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4435RoundedFacts : LeafRoundedFacts 8
    leaf4435Certificate.logOnePlusV leaf4435InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4435InputLogOnePlusV_eq }

private noncomputable def leaf4435Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi280InputQChi innerPair100Input
    leaf4435InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4435LowerChecked :
    lowerCheck 24 leaf4435Box leaf4435Inputs = true := by
  rfl'

private theorem leaf4435CoversExact : CoversExact 8
    leaf4435Box leaf4435Certificate leaf4435InnerLog leaf4435Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi280RoundedFacts
    innerPair100RoundedFacts leaf4435RoundedFacts (by rfl)

private theorem leaf4435FlatSound : Sound leaf4435Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4435CertificateValid
    leaf4435InnerLogValid leaf4435CoversExact leaf4435LowerChecked

private noncomputable def leaf4436Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (17/64), chiHi := (69/256) }

private noncomputable def leaf4436Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871263/536870912) }, vSqrt := { lower := (65529/65536), upper := (13743698739/13743139328) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1009192451/536870912) }, upper := { exponent := 0, mantissa := (15575/8192) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi257LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (27486838067/27486278656) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf4436InnerLog : WideLogData :=
  innerPair103Data

set_option maxRecDepth 1000000 in
private theorem leaf4436LocalValidity :
    LeafFacts leaf4436Box leaf4436Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4436Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (13743698739/13743139328) }) = true
      norm_num [leaf4436Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4436CertificateValid :
    WideCertificateValid leaf4436Box leaf4436Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi257ValidityFacts
    leaf4436LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4436CoverageChecked :
    coverageCheck (innerAD leaf4436Box) leaf4436InnerLog = true := by
  rfl'

private theorem leaf4436InnerLogValid :
    leaf4436InnerLog.Valid 8 (innerAD leaf4436Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint70PositiveFacts.valid leaf4436CoverageChecked

private noncomputable def leaf4436InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814711/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4436InputLogOnePlusV_eq :
    leaf4436InputLogOnePlusV = outerEnclosure 24
      (leaf4436Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4436RoundedFacts : LeafRoundedFacts 8
    leaf4436Certificate.logOnePlusV leaf4436InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4436InputLogOnePlusV_eq }

private noncomputable def leaf4436Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi257InputQChi innerPair103Input
    leaf4436InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4436LowerChecked :
    lowerCheck 24 leaf4436Box leaf4436Inputs = true := by
  rfl'

private theorem leaf4436CoversExact : CoversExact 8
    leaf4436Box leaf4436Certificate leaf4436InnerLog leaf4436Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi257RoundedFacts
    innerPair103RoundedFacts leaf4436RoundedFacts (by rfl)

private theorem leaf4436FlatSound : Sound leaf4436Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4436CertificateValid
    leaf4436InnerLogValid leaf4436CoversExact leaf4436LowerChecked

private noncomputable def leaf4437Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (69/256), chiHi := (35/128) }

private noncomputable def leaf4437Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871265/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905213952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1016138841/536870912) }, upper := { exponent := 0, mantissa := (7841/4096) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi258LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811378517/45810427904) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf4437InnerLog : WideLogData :=
  innerPair229Data

set_option maxRecDepth 1000000 in
private theorem leaf4437LocalValidity :
    LeafFacts leaf4437Box leaf4437Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4437Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905213952) }) = true
      norm_num [leaf4437Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4437CertificateValid :
    WideCertificateValid leaf4437Box leaf4437Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi258ValidityFacts
    leaf4437LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4437CoverageChecked :
    coverageCheck (innerAD leaf4437Box) leaf4437InnerLog = true := by
  rfl'

private theorem leaf4437InnerLogValid :
    leaf4437InnerLog.Valid 8 (innerAD leaf4437Box) :=
  wideLogDataValid_of_cachedCheck endpoint69PositiveFacts
    endpoint81PositiveFacts.valid leaf4437CoverageChecked

private noncomputable def leaf4437InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629429/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4437InputLogOnePlusV_eq :
    leaf4437InputLogOnePlusV = outerEnclosure 24
      (leaf4437Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4437RoundedFacts : LeafRoundedFacts 8
    leaf4437Certificate.logOnePlusV leaf4437InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4437InputLogOnePlusV_eq }

private noncomputable def leaf4437Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi258InputQChi innerPair229Input
    leaf4437InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4437LowerChecked :
    lowerCheck 24 leaf4437Box leaf4437Inputs = true := by
  rfl'

private theorem leaf4437CoversExact : CoversExact 8
    leaf4437Box leaf4437Certificate leaf4437InnerLog leaf4437Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi258RoundedFacts
    innerPair229RoundedFacts leaf4437RoundedFacts (by rfl)

private theorem leaf4437FlatSound : Sound leaf4437Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4437CertificateValid
    leaf4437InnerLogValid leaf4437CoversExact leaf4437LowerChecked

private noncomputable def leaf4438Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (17/64), chiHi := (69/256) }

private noncomputable def leaf4438Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871265/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715661312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1013648625/536870912) }, upper := { exponent := 0, mantissa := (3911/2048) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi257LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434155007/137431322624) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf4438InnerLog : WideLogData :=
  innerPair515Data

set_option maxRecDepth 1000000 in
private theorem leaf4438LocalValidity :
    LeafFacts leaf4438Box leaf4438Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4438Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715661312) }) = true
      norm_num [leaf4438Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4438CertificateValid :
    WideCertificateValid leaf4438Box leaf4438Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi257ValidityFacts
    leaf4438LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4438CoverageChecked :
    coverageCheck (innerAD leaf4438Box) leaf4438InnerLog = true := by
  rfl'

private theorem leaf4438InnerLogValid :
    leaf4438InnerLog.Valid 8 (innerAD leaf4438Box) :=
  wideLogDataValid_of_cachedCheck endpoint245PositiveFacts
    endpoint246PositiveFacts.valid leaf4438CoverageChecked

private noncomputable def leaf4438InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629427/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4438InputLogOnePlusV_eq :
    leaf4438InputLogOnePlusV = outerEnclosure 24
      (leaf4438Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4438RoundedFacts : LeafRoundedFacts 8
    leaf4438Certificate.logOnePlusV leaf4438InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4438InputLogOnePlusV_eq }

private noncomputable def leaf4438Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi257InputQChi innerPair515Input
    leaf4438InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4438LowerChecked :
    lowerCheck 24 leaf4438Box leaf4438Inputs = true := by
  rfl'

private theorem leaf4438CoversExact : CoversExact 8
    leaf4438Box leaf4438Certificate leaf4438InnerLog leaf4438Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi257RoundedFacts
    innerPair515RoundedFacts leaf4438RoundedFacts (by rfl)

private theorem leaf4438FlatSound : Sound leaf4438Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4438CertificateValid
    leaf4438InnerLogValid leaf4438CoversExact leaf4438LowerChecked

private noncomputable def leaf4439Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (69/256), chiHi := (35/128) }

private noncomputable def leaf4439Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871267/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715606016) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1020660547/536870912) }, upper := { exponent := 0, mantissa := (1969/1024) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi258LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434099711/137431212032) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf4439InnerLog : WideLogData :=
  innerPair523Data

set_option maxRecDepth 1000000 in
private theorem leaf4439LocalValidity :
    LeafFacts leaf4439Box leaf4439Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4439Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715606016) }) = true
      norm_num [leaf4439Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4439CertificateValid :
    WideCertificateValid leaf4439Box leaf4439Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi258ValidityFacts
    leaf4439LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4439CoverageChecked :
    coverageCheck (innerAD leaf4439Box) leaf4439InnerLog = true := by
  rfl'

private theorem leaf4439InnerLogValid :
    leaf4439InnerLog.Valid 8 (innerAD leaf4439Box) :=
  wideLogDataValid_of_cachedCheck endpoint257PositiveFacts
    endpoint248PositiveFacts.valid leaf4439CoverageChecked

private noncomputable def leaf4439InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629433/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4439InputLogOnePlusV_eq :
    leaf4439InputLogOnePlusV = outerEnclosure 24
      (leaf4439Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4439RoundedFacts : LeafRoundedFacts 8
    leaf4439Certificate.logOnePlusV leaf4439InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4439InputLogOnePlusV_eq }

private noncomputable def leaf4439Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi258InputQChi innerPair523Input
    leaf4439InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4439LowerChecked :
    lowerCheck 24 leaf4439Box leaf4439Inputs = true := by
  rfl'

private theorem leaf4439CoversExact : CoversExact 8
    leaf4439Box leaf4439Certificate leaf4439InnerLog leaf4439Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi258RoundedFacts
    innerPair523RoundedFacts leaf4439RoundedFacts (by rfl)

private theorem leaf4439FlatSound : Sound leaf4439Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4439CertificateValid
    leaf4439InnerLogValid leaf4439CoversExact leaf4439LowerChecked

private noncomputable def leaf4440Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (35/128), chiHi := (71/256) }

private noncomputable def leaf4440Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871267/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715587072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1023085231/536870912) }, upper := { exponent := 0, mantissa := (15789/8192) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi279LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434080767/137431174144) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf4440InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4440LocalValidity :
    LeafFacts leaf4440Box leaf4440Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4440Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715587072) }) = true
      norm_num [leaf4440Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4440CertificateValid :
    WideCertificateValid leaf4440Box leaf4440Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi279ValidityFacts
    leaf4440LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4440CoverageChecked :
    coverageCheck (innerAD leaf4440Box) leaf4440InnerLog = true := by
  rfl'

private theorem leaf4440InnerLogValid :
    leaf4440InnerLog.Valid 8 (innerAD leaf4440Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4440CoverageChecked

private noncomputable def leaf4440InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907359/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4440InputLogOnePlusV_eq :
    leaf4440InputLogOnePlusV = outerEnclosure 24
      (leaf4440Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4440RoundedFacts : LeafRoundedFacts 8
    leaf4440Certificate.logOnePlusV leaf4440InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4440InputLogOnePlusV_eq }

private noncomputable def leaf4440Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi279InputQChi innerPair100Input
    leaf4440InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4440LowerChecked :
    lowerCheck 24 leaf4440Box leaf4440Inputs = true := by
  rfl'

private theorem leaf4440CoversExact : CoversExact 8
    leaf4440Box leaf4440Certificate leaf4440InnerLog leaf4440Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi279RoundedFacts
    innerPair100RoundedFacts leaf4440RoundedFacts (by rfl)

private theorem leaf4440FlatSound : Sound leaf4440Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4440CertificateValid
    leaf4440InnerLogValid leaf4440CoversExact leaf4440LowerChecked

private noncomputable def leaf4441Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (71/256), chiHi := (9/32) }

private noncomputable def leaf4441Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871269/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715532288) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1030031621/536870912) }, upper := { exponent := 0, mantissa := (1987/1024) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi280LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434025983/137431064576) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf4441InnerLog : WideLogData :=
  innerPair233Data

set_option maxRecDepth 1000000 in
private theorem leaf4441LocalValidity :
    LeafFacts leaf4441Box leaf4441Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4441Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715532288) }) = true
      norm_num [leaf4441Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4441CertificateValid :
    WideCertificateValid leaf4441Box leaf4441Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi280ValidityFacts
    leaf4441LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4441CoverageChecked :
    coverageCheck (innerAD leaf4441Box) leaf4441InnerLog = true := by
  rfl'

private theorem leaf4441InnerLogValid :
    leaf4441InnerLog.Valid 8 (innerAD leaf4441Box) :=
  wideLogDataValid_of_cachedCheck endpoint70PositiveFacts
    endpoint71PositiveFacts.valid leaf4441CoverageChecked

private noncomputable def leaf4441InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814721/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4441InputLogOnePlusV_eq :
    leaf4441InputLogOnePlusV = outerEnclosure 24
      (leaf4441Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4441RoundedFacts : LeafRoundedFacts 8
    leaf4441Certificate.logOnePlusV leaf4441InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4441InputLogOnePlusV_eq }

private noncomputable def leaf4441Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi280InputQChi innerPair233Input
    leaf4441InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4441LowerChecked :
    lowerCheck 24 leaf4441Box leaf4441Inputs = true := by
  rfl'

private theorem leaf4441CoversExact : CoversExact 8
    leaf4441Box leaf4441Certificate leaf4441InnerLog leaf4441Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi280RoundedFacts
    innerPair233RoundedFacts leaf4441RoundedFacts (by rfl)

private theorem leaf4441FlatSound : Sound leaf4441Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4441CertificateValid
    leaf4441InnerLogValid leaf4441CoversExact leaf4441LowerChecked

private noncomputable def leaf4442Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (35/128), chiHi := (71/256) }

private noncomputable def leaf4442Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871269/536870912) }, vSqrt := { lower := (65529/65536), upper := (13743698739/13743110144) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1027672469/536870912) }, upper := { exponent := 0, mantissa := (3965/2048) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi279LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (27486808883/27486220288) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf4442InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4442LocalValidity :
    LeafFacts leaf4442Box leaf4442Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4442Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (13743698739/13743110144) }) = true
      norm_num [leaf4442Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4442CertificateValid :
    WideCertificateValid leaf4442Box leaf4442Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi279ValidityFacts
    leaf4442LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4442CoverageChecked :
    coverageCheck (innerAD leaf4442Box) leaf4442InnerLog = true := by
  rfl'

private theorem leaf4442InnerLogValid :
    leaf4442InnerLog.Valid 8 (innerAD leaf4442Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4442CoverageChecked

private noncomputable def leaf4442InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (90855/131072) }

set_option maxRecDepth 1000000 in
private theorem leaf4442InputLogOnePlusV_eq :
    leaf4442InputLogOnePlusV = outerEnclosure 24
      (leaf4442Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4442RoundedFacts : LeafRoundedFacts 8
    leaf4442Certificate.logOnePlusV leaf4442InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4442InputLogOnePlusV_eq }

private noncomputable def leaf4442Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi279InputQChi innerPair100Input
    leaf4442InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4442LowerChecked :
    lowerCheck 24 leaf4442Box leaf4442Inputs = true := by
  rfl'

private theorem leaf4442CoversExact : CoversExact 8
    leaf4442Box leaf4442Certificate leaf4442InnerLog leaf4442Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi279RoundedFacts
    innerPair100RoundedFacts leaf4442RoundedFacts (by rfl)

private theorem leaf4442FlatSound : Sound leaf4442Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4442CertificateValid
    leaf4442InnerLogValid leaf4442CoversExact leaf4442LowerChecked

private noncomputable def leaf4443Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (71/256), chiHi := (9/32) }

private noncomputable def leaf4443Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871271/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715495424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1034684391/536870912) }, upper := { exponent := 0, mantissa := (499/256) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi280LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137433989119/137430990848) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf4443InnerLog : WideLogData :=
  innerPair304Data

set_option maxRecDepth 1000000 in
private theorem leaf4443LocalValidity :
    LeafFacts leaf4443Box leaf4443Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4443Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715495424) }) = true
      norm_num [leaf4443Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4443CertificateValid :
    WideCertificateValid leaf4443Box leaf4443Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi280ValidityFacts
    leaf4443LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4443CoverageChecked :
    coverageCheck (innerAD leaf4443Box) leaf4443InnerLog = true := by
  rfl'

private theorem leaf4443InnerLogValid :
    leaf4443InnerLog.Valid 8 (innerAD leaf4443Box) :=
  wideLogDataValid_of_cachedCheck endpoint81PositiveFacts
    endpoint71PositiveFacts.valid leaf4443CoverageChecked

private noncomputable def leaf4443InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629447/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4443InputLogOnePlusV_eq :
    leaf4443InputLogOnePlusV = outerEnclosure 24
      (leaf4443Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4443RoundedFacts : LeafRoundedFacts 8
    leaf4443Certificate.logOnePlusV leaf4443InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4443InputLogOnePlusV_eq }

private noncomputable def leaf4443Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi280InputQChi innerPair304Input
    leaf4443InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4443LowerChecked :
    lowerCheck 24 leaf4443Box leaf4443Inputs = true := by
  rfl'

private theorem leaf4443CoversExact : CoversExact 8
    leaf4443Box leaf4443Certificate leaf4443InnerLog leaf4443Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi280RoundedFacts
    innerPair304RoundedFacts leaf4443RoundedFacts (by rfl)

private theorem leaf4443FlatSound : Sound leaf4443Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4443CertificateValid
    leaf4443InnerLogValid leaf4443CoversExact leaf4443LowerChecked

private noncomputable def component90Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (1/4), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component90Node0_sound : Sound component90Node0Box :=
  sound_of_literal_split component90Node0Box leaf4412Box leaf4413Box
    .chi (65/256) (by rfl) (by rfl)
    leaf4412FlatSound leaf4413FlatSound

private noncomputable def component90Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (1/4), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component90Node1_sound : Sound component90Node1Box :=
  sound_of_literal_split component90Node1Box leaf4414Box leaf4415Box
    .chi (65/256) (by rfl) (by rfl)
    leaf4414FlatSound leaf4415FlatSound

private noncomputable def component90Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (1/4), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component90Node2_sound : Sound component90Node2Box :=
  sound_of_literal_split component90Node2Box component90Node0Box component90Node1Box
    .k (105/32) (by rfl) (by rfl)
    component90Node0_sound component90Node1_sound

private noncomputable def component90Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (33/128), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component90Node3_sound : Sound component90Node3Box :=
  sound_of_literal_split component90Node3Box leaf4416Box leaf4417Box
    .chi (67/256) (by rfl) (by rfl)
    leaf4416FlatSound leaf4417FlatSound

private noncomputable def component90Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (33/128), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component90Node4_sound : Sound component90Node4Box :=
  sound_of_literal_split component90Node4Box leaf4418Box leaf4419Box
    .chi (67/256) (by rfl) (by rfl)
    leaf4418FlatSound leaf4419FlatSound

private noncomputable def component90Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (33/128), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component90Node5_sound : Sound component90Node5Box :=
  sound_of_literal_split component90Node5Box component90Node3Box component90Node4Box
    .k (105/32) (by rfl) (by rfl)
    component90Node3_sound component90Node4_sound

private noncomputable def component90Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component90Node6_sound : Sound component90Node6Box :=
  sound_of_literal_split component90Node6Box component90Node2Box component90Node5Box
    .chi (33/128) (by rfl) (by rfl)
    component90Node2_sound component90Node5_sound

private noncomputable def component90Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (1/4), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component90Node7_sound : Sound component90Node7Box :=
  sound_of_literal_split component90Node7Box leaf4420Box leaf4421Box
    .chi (65/256) (by rfl) (by rfl)
    leaf4420FlatSound leaf4421FlatSound

private noncomputable def component90Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (1/4), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component90Node8_sound : Sound component90Node8Box :=
  sound_of_literal_split component90Node8Box leaf4422Box leaf4423Box
    .chi (65/256) (by rfl) (by rfl)
    leaf4422FlatSound leaf4423FlatSound

private noncomputable def component90Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (1/4), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component90Node9_sound : Sound component90Node9Box :=
  sound_of_literal_split component90Node9Box component90Node7Box component90Node8Box
    .k (107/32) (by rfl) (by rfl)
    component90Node7_sound component90Node8_sound

private noncomputable def component90Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (33/128), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component90Node10_sound : Sound component90Node10Box :=
  sound_of_literal_split component90Node10Box leaf4424Box leaf4425Box
    .chi (67/256) (by rfl) (by rfl)
    leaf4424FlatSound leaf4425FlatSound

private noncomputable def component90Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (33/128), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component90Node11_sound : Sound component90Node11Box :=
  sound_of_literal_split component90Node11Box leaf4426Box leaf4427Box
    .chi (67/256) (by rfl) (by rfl)
    leaf4426FlatSound leaf4427FlatSound

private noncomputable def component90Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (33/128), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component90Node12_sound : Sound component90Node12Box :=
  sound_of_literal_split component90Node12Box component90Node10Box component90Node11Box
    .k (107/32) (by rfl) (by rfl)
    component90Node10_sound component90Node11_sound

private noncomputable def component90Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component90Node13_sound : Sound component90Node13Box :=
  sound_of_literal_split component90Node13Box component90Node9Box component90Node12Box
    .chi (33/128) (by rfl) (by rfl)
    component90Node9_sound component90Node12_sound

private noncomputable def component90Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component90Node14_sound : Sound component90Node14Box :=
  sound_of_literal_split component90Node14Box component90Node6Box component90Node13Box
    .k (53/16) (by rfl) (by rfl)
    component90Node6_sound component90Node13_sound

private noncomputable def component90Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (17/64), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component90Node15_sound : Sound component90Node15Box :=
  sound_of_literal_split component90Node15Box leaf4428Box leaf4429Box
    .chi (69/256) (by rfl) (by rfl)
    leaf4428FlatSound leaf4429FlatSound

private noncomputable def component90Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (17/64), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component90Node16_sound : Sound component90Node16Box :=
  sound_of_literal_split component90Node16Box leaf4430Box leaf4431Box
    .chi (69/256) (by rfl) (by rfl)
    leaf4430FlatSound leaf4431FlatSound

private noncomputable def component90Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (17/64), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component90Node17_sound : Sound component90Node17Box :=
  sound_of_literal_split component90Node17Box component90Node15Box component90Node16Box
    .k (105/32) (by rfl) (by rfl)
    component90Node15_sound component90Node16_sound

private noncomputable def component90Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (35/128), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component90Node18_sound : Sound component90Node18Box :=
  sound_of_literal_split component90Node18Box leaf4432Box leaf4433Box
    .chi (71/256) (by rfl) (by rfl)
    leaf4432FlatSound leaf4433FlatSound

private noncomputable def component90Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (35/128), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component90Node19_sound : Sound component90Node19Box :=
  sound_of_literal_split component90Node19Box leaf4434Box leaf4435Box
    .chi (71/256) (by rfl) (by rfl)
    leaf4434FlatSound leaf4435FlatSound

private noncomputable def component90Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (35/128), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component90Node20_sound : Sound component90Node20Box :=
  sound_of_literal_split component90Node20Box component90Node18Box component90Node19Box
    .k (105/32) (by rfl) (by rfl)
    component90Node18_sound component90Node19_sound

private noncomputable def component90Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component90Node21_sound : Sound component90Node21Box :=
  sound_of_literal_split component90Node21Box component90Node17Box component90Node20Box
    .chi (35/128) (by rfl) (by rfl)
    component90Node17_sound component90Node20_sound

private noncomputable def component90Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (17/64), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component90Node22_sound : Sound component90Node22Box :=
  sound_of_literal_split component90Node22Box leaf4436Box leaf4437Box
    .chi (69/256) (by rfl) (by rfl)
    leaf4436FlatSound leaf4437FlatSound

private noncomputable def component90Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (17/64), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component90Node23_sound : Sound component90Node23Box :=
  sound_of_literal_split component90Node23Box leaf4438Box leaf4439Box
    .chi (69/256) (by rfl) (by rfl)
    leaf4438FlatSound leaf4439FlatSound

private noncomputable def component90Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (17/64), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component90Node24_sound : Sound component90Node24Box :=
  sound_of_literal_split component90Node24Box component90Node22Box component90Node23Box
    .k (107/32) (by rfl) (by rfl)
    component90Node22_sound component90Node23_sound

private noncomputable def component90Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (35/128), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component90Node25_sound : Sound component90Node25Box :=
  sound_of_literal_split component90Node25Box leaf4440Box leaf4441Box
    .chi (71/256) (by rfl) (by rfl)
    leaf4440FlatSound leaf4441FlatSound

private noncomputable def component90Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (35/128), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component90Node26_sound : Sound component90Node26Box :=
  sound_of_literal_split component90Node26Box leaf4442Box leaf4443Box
    .chi (71/256) (by rfl) (by rfl)
    leaf4442FlatSound leaf4443FlatSound

private noncomputable def component90Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (35/128), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component90Node27_sound : Sound component90Node27Box :=
  sound_of_literal_split component90Node27Box component90Node25Box component90Node26Box
    .k (107/32) (by rfl) (by rfl)
    component90Node25_sound component90Node26_sound

private noncomputable def component90Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component90Node28_sound : Sound component90Node28Box :=
  sound_of_literal_split component90Node28Box component90Node24Box component90Node27Box
    .chi (35/128) (by rfl) (by rfl)
    component90Node24_sound component90Node27_sound

private noncomputable def component90Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component90Node29_sound : Sound component90Node29Box :=
  sound_of_literal_split component90Node29Box component90Node21Box component90Node28Box
    .k (53/16) (by rfl) (by rfl)
    component90Node21_sound component90Node28_sound

noncomputable def component90Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (1/4), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
theorem component90_sound : Sound component90Box :=
  sound_of_literal_split component90Box component90Node14Box component90Node29Box
    .chi (17/64) (by rfl) (by rfl)
    component90Node14_sound component90Node29_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
