import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch5
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

private noncomputable def leaf4562Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (5/16), chiHi := (41/128) }

private noncomputable def leaf4562Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435731/268435456) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715404288) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (520045295/268435456) }, upper := { exponent := 0, mantissa := (8073/4096) } }, logOuter := sk133LogOuterCertificate, logK := sk133LogKCertificate, logChi := chi249LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137433897983/137430808576) } }, logDArg := sk133LogDArgCertificate }

private noncomputable def leaf4562InnerLog : WideLogData :=
  innerPair308Data

set_option maxRecDepth 1000000 in
private theorem leaf4562LocalValidity :
    LeafFacts leaf4562Box leaf4562Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4562Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715404288) }) = true
      norm_num [leaf4562Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4562CertificateValid :
    WideCertificateValid leaf4562Box leaf4562Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk133ValidityFacts chi249ValidityFacts
    leaf4562LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4562CoverageChecked :
    coverageCheck (innerAD leaf4562Box) leaf4562InnerLog = true := by
  rfl'

private theorem leaf4562InnerLogValid :
    leaf4562InnerLog.Valid 8 (innerAD leaf4562Box) :=
  wideLogDataValid_of_cachedCheck endpoint81PositiveFacts
    endpoint267PositiveFacts.valid leaf4562CoverageChecked

private noncomputable def leaf4562InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814729/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4562InputLogOnePlusV_eq :
    leaf4562InputLogOnePlusV = outerEnclosure 24
      (leaf4562Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4562RoundedFacts : LeafRoundedFacts 8
    leaf4562Certificate.logOnePlusV leaf4562InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4562InputLogOnePlusV_eq }

private noncomputable def leaf4562Inputs : Inputs :=
  inputsOfCaches globalInput sk133RoundedInputs
    chi249InputQChi innerPair308Input
    leaf4562InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4562LowerChecked :
    lowerCheck 24 leaf4562Box leaf4562Inputs = true := by
  rfl'

private theorem leaf4562CoversExact : CoversExact 8
    leaf4562Box leaf4562Certificate leaf4562InnerLog leaf4562Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk133RoundedFacts chi249RoundedFacts
    innerPair308RoundedFacts leaf4562RoundedFacts (by rfl)

private theorem leaf4562FlatSound : Sound leaf4562Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4562CertificateValid
    leaf4562InnerLogValid leaf4562CoversExact leaf4562LowerChecked

private noncomputable def leaf4563Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (5/16), chiHi := (41/128) }

private noncomputable def leaf4563Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435733/268435456) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905120768) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (522666573/268435456) }, upper := { exponent := 0, mantissa := (4057/2048) } }, logOuter := sk134LogOuterCertificate, logK := sk134LogKCertificate, logChi := chi249LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811285333/45810241536) } }, logDArg := sk134LogDArgCertificate }

private noncomputable def leaf4563InnerLog : WideLogData :=
  innerPair114Data

set_option maxRecDepth 1000000 in
private theorem leaf4563LocalValidity :
    LeafFacts leaf4563Box leaf4563Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4563Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905120768) }) = true
      norm_num [leaf4563Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4563CertificateValid :
    WideCertificateValid leaf4563Box leaf4563Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk134ValidityFacts chi249ValidityFacts
    leaf4563LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4563CoverageChecked :
    coverageCheck (innerAD leaf4563Box) leaf4563InnerLog = true := by
  rfl'

private theorem leaf4563InnerLogValid :
    leaf4563InnerLog.Valid 8 (innerAD leaf4563Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint267PositiveFacts.valid leaf4563CoverageChecked

private noncomputable def leaf4563InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629463/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4563InputLogOnePlusV_eq :
    leaf4563InputLogOnePlusV = outerEnclosure 24
      (leaf4563Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4563RoundedFacts : LeafRoundedFacts 8
    leaf4563Certificate.logOnePlusV leaf4563InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4563InputLogOnePlusV_eq }

private noncomputable def leaf4563Inputs : Inputs :=
  inputsOfCaches globalInput sk134RoundedInputs
    chi249InputQChi innerPair114Input
    leaf4563InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4563LowerChecked :
    lowerCheck 24 leaf4563Box leaf4563Inputs = true := by
  rfl'

private theorem leaf4563CoversExact : CoversExact 8
    leaf4563Box leaf4563Certificate leaf4563InnerLog leaf4563Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk134RoundedFacts chi249RoundedFacts
    innerPair114RoundedFacts leaf4563RoundedFacts (by rfl)

private theorem leaf4563FlatSound : Sound leaf4563Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4563CertificateValid
    leaf4563InnerLogValid leaf4563CoversExact leaf4563LowerChecked

private noncomputable def leaf4564Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (41/128), chiHi := (21/64) }

private noncomputable def leaf4564Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435733/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357652480) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (526336365/268435456) }, upper := { exponent := 0, mantissa := (4085/2048) } }, logOuter := sk133LogOuterCertificate, logK := sk133LogKCertificate, logChi := chi250LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716375039/68715304960) } }, logDArg := sk133LogDArgCertificate }

private noncomputable def leaf4564InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4564LocalValidity :
    LeafFacts leaf4564Box leaf4564Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4564Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357652480) }) = true
      norm_num [leaf4564Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4564CertificateValid :
    WideCertificateValid leaf4564Box leaf4564Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk133ValidityFacts chi250ValidityFacts
    leaf4564LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4564CoverageChecked :
    coverageCheck (innerAD leaf4564Box) leaf4564InnerLog = true := by
  rfl'

private theorem leaf4564InnerLogValid :
    leaf4564InnerLog.Valid 8 (innerAD leaf4564Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4564CoverageChecked

private noncomputable def leaf4564InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814671/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4564InputLogOnePlusV_eq :
    leaf4564InputLogOnePlusV = outerEnclosure 24
      (leaf4564Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4564RoundedFacts : LeafRoundedFacts 8
    leaf4564Certificate.logOnePlusV leaf4564InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4564InputLogOnePlusV_eq }

private noncomputable def leaf4564Inputs : Inputs :=
  inputsOfCaches globalInput sk133RoundedInputs
    chi250InputQChi innerPair108Input
    leaf4564InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4564LowerChecked :
    lowerCheck 24 leaf4564Box leaf4564Inputs = true := by
  rfl'

private theorem leaf4564CoversExact : CoversExact 8
    leaf4564Box leaf4564Certificate leaf4564InnerLog leaf4564Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk133RoundedFacts chi250RoundedFacts
    innerPair108RoundedFacts leaf4564RoundedFacts (by rfl)

private theorem leaf4564FlatSound : Sound leaf4564Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4564CertificateValid
    leaf4564InnerLogValid leaf4564CoversExact leaf4564LowerChecked

private noncomputable def leaf4565Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (41/128), chiHi := (21/64) }

private noncomputable def leaf4565Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435735/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357630976) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (529023175/268435456) }, upper := { exponent := 1, mantissa := (2053/2048) } }, logOuter := sk134LogOuterCertificate, logK := sk134LogKCertificate, logChi := chi250LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716353535/68715261952) } }, logDArg := sk134LogDArgCertificate }

private noncomputable def leaf4565InnerLog : WideLogData :=
  innerPair321Data

set_option maxRecDepth 1000000 in
private theorem leaf4565LocalValidity :
    LeafFacts leaf4565Box leaf4565Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4565Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357630976) }) = true
      norm_num [leaf4565Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4565CertificateValid :
    WideCertificateValid leaf4565Box leaf4565Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk134ValidityFacts chi250ValidityFacts
    leaf4565LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4565CoverageChecked :
    coverageCheck (innerAD leaf4565Box) leaf4565InnerLog = true := by
  rfl'

private theorem leaf4565InnerLogValid :
    leaf4565InnerLog.Valid 8 (innerAD leaf4565Box) :=
  wideLogDataValid_of_cachedCheck endpoint85PositiveFacts
    endpoint283PositiveFacts.valid leaf4565CoverageChecked

private noncomputable def leaf4565InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629347/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4565InputLogOnePlusV_eq :
    leaf4565InputLogOnePlusV = outerEnclosure 24
      (leaf4565Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4565RoundedFacts : LeafRoundedFacts 8
    leaf4565Certificate.logOnePlusV leaf4565InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4565InputLogOnePlusV_eq }

private noncomputable def leaf4565Inputs : Inputs :=
  inputsOfCaches globalInput sk134RoundedInputs
    chi250InputQChi innerPair321Input
    leaf4565InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4565LowerChecked :
    lowerCheck 24 leaf4565Box leaf4565Inputs = true := by
  rfl'

private theorem leaf4565CoversExact : CoversExact 8
    leaf4565Box leaf4565Certificate leaf4565InnerLog leaf4565Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk134RoundedFacts chi250RoundedFacts
    innerPair321RoundedFacts leaf4565RoundedFacts (by rfl)

private theorem leaf4565FlatSound : Sound leaf4565Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4565CertificateValid
    leaf4565InnerLogValid leaf4565CoversExact leaf4565LowerChecked

private noncomputable def leaf4566Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (5/16), chiHi := (41/128) }

private noncomputable def leaf4566Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435735/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357660160) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (525287851/268435456) }, upper := { exponent := 0, mantissa := (8155/4096) } }, logOuter := sk135LogOuterCertificate, logK := sk135LogKCertificate, logChi := chi249LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716382719/68715320320) } }, logDArg := sk135LogDArgCertificate }

private noncomputable def leaf4566InnerLog : WideLogData :=
  innerPair240Data

set_option maxRecDepth 1000000 in
private theorem leaf4566LocalValidity :
    LeafFacts leaf4566Box leaf4566Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4566Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357660160) }) = true
      norm_num [leaf4566Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4566CertificateValid :
    WideCertificateValid leaf4566Box leaf4566Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk135ValidityFacts chi249ValidityFacts
    leaf4566LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4566CoverageChecked :
    coverageCheck (innerAD leaf4566Box) leaf4566InnerLog = true := by
  rfl'

private theorem leaf4566InnerLogValid :
    leaf4566InnerLog.Valid 8 (innerAD leaf4566Box) :=
  wideLogDataValid_of_cachedCheck endpoint71PositiveFacts
    endpoint278PositiveFacts.valid leaf4566CoverageChecked

private noncomputable def leaf4566InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907335/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4566InputLogOnePlusV_eq :
    leaf4566InputLogOnePlusV = outerEnclosure 24
      (leaf4566Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4566RoundedFacts : LeafRoundedFacts 8
    leaf4566Certificate.logOnePlusV leaf4566InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4566InputLogOnePlusV_eq }

private noncomputable def leaf4566Inputs : Inputs :=
  inputsOfCaches globalInput sk135RoundedInputs
    chi249InputQChi innerPair240Input
    leaf4566InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4566LowerChecked :
    lowerCheck 24 leaf4566Box leaf4566Inputs = true := by
  rfl'

private theorem leaf4566CoversExact : CoversExact 8
    leaf4566Box leaf4566Certificate leaf4566InnerLog leaf4566Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk135RoundedFacts chi249RoundedFacts
    innerPair240RoundedFacts leaf4566RoundedFacts (by rfl)

private theorem leaf4566FlatSound : Sound leaf4566Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4566CertificateValid
    leaf4566InnerLogValid leaf4566CoversExact leaf4566LowerChecked

private noncomputable def leaf4567Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (5/16), chiHi := (41/128) }

private noncomputable def leaf4567Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435737/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357639168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (527909129/268435456) }, upper := { exponent := 1, mantissa := (2049/2048) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi249LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716361727/68715278336) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf4567InnerLog : WideLogData :=
  innerPair540Data

set_option maxRecDepth 1000000 in
private theorem leaf4567LocalValidity :
    LeafFacts leaf4567Box leaf4567Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4567Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357639168) }) = true
      norm_num [leaf4567Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4567CertificateValid :
    WideCertificateValid leaf4567Box leaf4567Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi249ValidityFacts
    leaf4567LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4567CoverageChecked :
    coverageCheck (innerAD leaf4567Box) leaf4567InnerLog = true := by
  rfl'

private theorem leaf4567InnerLogValid :
    leaf4567InnerLog.Valid 8 (innerAD leaf4567Box) :=
  wideLogDataValid_of_cachedCheck endpoint274PositiveFacts
    endpoint328PositiveFacts.valid leaf4567CoverageChecked

private noncomputable def leaf4567InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629345/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4567InputLogOnePlusV_eq :
    leaf4567InputLogOnePlusV = outerEnclosure 24
      (leaf4567Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4567RoundedFacts : LeafRoundedFacts 8
    leaf4567Certificate.logOnePlusV leaf4567InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4567InputLogOnePlusV_eq }

private noncomputable def leaf4567Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi249InputQChi innerPair540Input
    leaf4567InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4567LowerChecked :
    lowerCheck 24 leaf4567Box leaf4567Inputs = true := by
  rfl'

private theorem leaf4567CoversExact : CoversExact 8
    leaf4567Box leaf4567Certificate leaf4567InnerLog leaf4567Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi249RoundedFacts
    innerPair540RoundedFacts leaf4567RoundedFacts (by rfl)

private theorem leaf4567FlatSound : Sound leaf4567Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4567CertificateValid
    leaf4567InnerLogValid leaf4567CoversExact leaf4567LowerChecked

private noncomputable def leaf4568Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (41/128), chiHi := (21/64) }

private noncomputable def leaf4568Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435737/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357609472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (531709985/268435456) }, upper := { exponent := 1, mantissa := (4127/4096) } }, logOuter := sk135LogOuterCertificate, logK := sk135LogKCertificate, logChi := chi250LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716332031/68715218944) } }, logDArg := sk135LogDArgCertificate }

private noncomputable def leaf4568InnerLog : WideLogData :=
  innerPair321Data

set_option maxRecDepth 1000000 in
private theorem leaf4568LocalValidity :
    LeafFacts leaf4568Box leaf4568Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4568Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357609472) }) = true
      norm_num [leaf4568Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4568CertificateValid :
    WideCertificateValid leaf4568Box leaf4568Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk135ValidityFacts chi250ValidityFacts
    leaf4568LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4568CoverageChecked :
    coverageCheck (innerAD leaf4568Box) leaf4568InnerLog = true := by
  rfl'

private theorem leaf4568InnerLogValid :
    leaf4568InnerLog.Valid 8 (innerAD leaf4568Box) :=
  wideLogDataValid_of_cachedCheck endpoint85PositiveFacts
    endpoint283PositiveFacts.valid leaf4568CoverageChecked

private noncomputable def leaf4568InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629353/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4568InputLogOnePlusV_eq :
    leaf4568InputLogOnePlusV = outerEnclosure 24
      (leaf4568Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4568RoundedFacts : LeafRoundedFacts 8
    leaf4568Certificate.logOnePlusV leaf4568InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4568InputLogOnePlusV_eq }

private noncomputable def leaf4568Inputs : Inputs :=
  inputsOfCaches globalInput sk135RoundedInputs
    chi250InputQChi innerPair321Input
    leaf4568InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4568LowerChecked :
    lowerCheck 24 leaf4568Box leaf4568Inputs = true := by
  rfl'

private theorem leaf4568CoversExact : CoversExact 8
    leaf4568Box leaf4568Certificate leaf4568InnerLog leaf4568Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk135RoundedFacts chi250RoundedFacts
    innerPair321RoundedFacts leaf4568RoundedFacts (by rfl)

private theorem leaf4568FlatSound : Sound leaf4568Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4568CertificateValid
    leaf4568InnerLogValid leaf4568CoversExact leaf4568LowerChecked

private noncomputable def leaf4569Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (41/128), chiHi := (21/64) }

private noncomputable def leaf4569Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435739/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357587968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (534396795/268435456) }, upper := { exponent := 1, mantissa := (1037/1024) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi250LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716310527/68715175936) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf4569InnerLog : WideLogData :=
  innerPair531Data

set_option maxRecDepth 1000000 in
private theorem leaf4569LocalValidity :
    LeafFacts leaf4569Box leaf4569Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4569Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357587968) }) = true
      norm_num [leaf4569Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4569CertificateValid :
    WideCertificateValid leaf4569Box leaf4569Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi250ValidityFacts
    leaf4569LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4569CoverageChecked :
    coverageCheck (innerAD leaf4569Box) leaf4569InnerLog = true := by
  rfl'

private theorem leaf4569InnerLogValid :
    leaf4569InnerLog.Valid 8 (innerAD leaf4569Box) :=
  wideLogDataValid_of_cachedCheck endpoint267PositiveFacts
    endpoint82PositiveFacts.valid leaf4569CoverageChecked

private noncomputable def leaf4569InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814679/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4569InputLogOnePlusV_eq :
    leaf4569InputLogOnePlusV = outerEnclosure 24
      (leaf4569Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4569RoundedFacts : LeafRoundedFacts 8
    leaf4569Certificate.logOnePlusV leaf4569InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4569InputLogOnePlusV_eq }

private noncomputable def leaf4569Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi250InputQChi innerPair531Input
    leaf4569InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4569LowerChecked :
    lowerCheck 24 leaf4569Box leaf4569Inputs = true := by
  rfl'

private theorem leaf4569CoversExact : CoversExact 8
    leaf4569Box leaf4569Certificate leaf4569InnerLog leaf4569Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi250RoundedFacts
    innerPair531RoundedFacts leaf4569RoundedFacts (by rfl)

private theorem leaf4569FlatSound : Sound leaf4569Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4569CertificateValid
    leaf4569InnerLogValid leaf4569CoversExact leaf4569LowerChecked

private noncomputable def leaf4570Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (21/64), chiHi := (43/128) }

private noncomputable def leaf4570Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435735/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357602816) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (532627435/268435456) }, upper := { exponent := 1, mantissa := (8267/8192) } }, logOuter := sk133LogOuterCertificate, logK := sk133LogKCertificate, logChi := chi251LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716325375/68715205632) } }, logDArg := sk133LogDArgCertificate }

private noncomputable def leaf4570InnerLog : WideLogData :=
  innerPair317Data

set_option maxRecDepth 1000000 in
private theorem leaf4570LocalValidity :
    LeafFacts leaf4570Box leaf4570Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4570Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357602816) }) = true
      norm_num [leaf4570Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4570CertificateValid :
    WideCertificateValid leaf4570Box leaf4570Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk133ValidityFacts chi251ValidityFacts
    leaf4570LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4570CoverageChecked :
    coverageCheck (innerAD leaf4570Box) leaf4570InnerLog = true := by
  rfl'

private theorem leaf4570InnerLogValid :
    leaf4570InnerLog.Valid 8 (innerAD leaf4570Box) :=
  wideLogDataValid_of_cachedCheck endpoint85PositiveFacts
    endpoint82PositiveFacts.valid leaf4570CoverageChecked

private noncomputable def leaf4570InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814677/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4570InputLogOnePlusV_eq :
    leaf4570InputLogOnePlusV = outerEnclosure 24
      (leaf4570Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4570RoundedFacts : LeafRoundedFacts 8
    leaf4570Certificate.logOnePlusV leaf4570InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4570InputLogOnePlusV_eq }

private noncomputable def leaf4570Inputs : Inputs :=
  inputsOfCaches globalInput sk133RoundedInputs
    chi251InputQChi innerPair317Input
    leaf4570InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4570LowerChecked :
    lowerCheck 24 leaf4570Box leaf4570Inputs = true := by
  rfl'

private theorem leaf4570CoversExact : CoversExact 8
    leaf4570Box leaf4570Certificate leaf4570InnerLog leaf4570Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk133RoundedFacts chi251RoundedFacts
    innerPair317RoundedFacts leaf4570RoundedFacts (by rfl)

private theorem leaf4570FlatSound : Sound leaf4570Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4570CertificateValid
    leaf4570InnerLogValid leaf4570CoversExact leaf4570LowerChecked

private noncomputable def leaf4571Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (21/64), chiHi := (43/128) }

private noncomputable def leaf4571Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435737/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357580800) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (535379777/268435456) }, upper := { exponent := 1, mantissa := (4155/4096) } }, logOuter := sk134LogOuterCertificate, logK := sk134LogKCertificate, logChi := chi251LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716303359/68715161600) } }, logDArg := sk134LogDArgCertificate }

private noncomputable def leaf4571InnerLog : WideLogData :=
  innerPair531Data

set_option maxRecDepth 1000000 in
private theorem leaf4571LocalValidity :
    LeafFacts leaf4571Box leaf4571Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4571Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357580800) }) = true
      norm_num [leaf4571Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4571CertificateValid :
    WideCertificateValid leaf4571Box leaf4571Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk134ValidityFacts chi251ValidityFacts
    leaf4571LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4571CoverageChecked :
    coverageCheck (innerAD leaf4571Box) leaf4571InnerLog = true := by
  rfl'

private theorem leaf4571InnerLogValid :
    leaf4571InnerLog.Valid 8 (innerAD leaf4571Box) :=
  wideLogDataValid_of_cachedCheck endpoint267PositiveFacts
    endpoint82PositiveFacts.valid leaf4571CoverageChecked

private noncomputable def leaf4571InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (726835/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf4571InputLogOnePlusV_eq :
    leaf4571InputLogOnePlusV = outerEnclosure 24
      (leaf4571Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4571RoundedFacts : LeafRoundedFacts 8
    leaf4571Certificate.logOnePlusV leaf4571InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4571InputLogOnePlusV_eq }

private noncomputable def leaf4571Inputs : Inputs :=
  inputsOfCaches globalInput sk134RoundedInputs
    chi251InputQChi innerPair531Input
    leaf4571InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4571LowerChecked :
    lowerCheck 24 leaf4571Box leaf4571Inputs = true := by
  rfl'

private theorem leaf4571CoversExact : CoversExact 8
    leaf4571Box leaf4571Certificate leaf4571InnerLog leaf4571Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk134RoundedFacts chi251RoundedFacts
    innerPair531RoundedFacts leaf4571RoundedFacts (by rfl)

private theorem leaf4571FlatSound : Sound leaf4571Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4571CertificateValid
    leaf4571InnerLogValid leaf4571CoversExact leaf4571LowerChecked

private noncomputable def leaf4572Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (43/128), chiHi := (11/32) }

private noncomputable def leaf4572Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435737/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357553152) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (538918505/536870912) }, upper := { exponent := 1, mantissa := (2091/2048) } }, logOuter := sk133LogOuterCertificate, logK := sk133LogKCertificate, logChi := chi252LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716275711/68715106304) } }, logDArg := sk133LogDArgCertificate }

private noncomputable def leaf4572InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4572LocalValidity :
    LeafFacts leaf4572Box leaf4572Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4572Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357553152) }) = true
      norm_num [leaf4572Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4572CertificateValid :
    WideCertificateValid leaf4572Box leaf4572Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk133ValidityFacts chi252ValidityFacts
    leaf4572LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4572CoverageChecked :
    coverageCheck (innerAD leaf4572Box) leaf4572InnerLog = true := by
  rfl'

private theorem leaf4572InnerLogValid :
    leaf4572InnerLog.Valid 8 (innerAD leaf4572Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4572CoverageChecked

private noncomputable def leaf4572InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814683/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4572InputLogOnePlusV_eq :
    leaf4572InputLogOnePlusV = outerEnclosure 24
      (leaf4572Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4572RoundedFacts : LeafRoundedFacts 8
    leaf4572Certificate.logOnePlusV leaf4572InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4572InputLogOnePlusV_eq }

private noncomputable def leaf4572Inputs : Inputs :=
  inputsOfCaches globalInput sk133RoundedInputs
    chi252InputQChi innerPair116Input
    leaf4572InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4572LowerChecked :
    lowerCheck 24 leaf4572Box leaf4572Inputs = true := by
  rfl'

private theorem leaf4572CoversExact : CoversExact 8
    leaf4572Box leaf4572Certificate leaf4572InnerLog leaf4572Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk133RoundedFacts chi252RoundedFacts
    innerPair116RoundedFacts leaf4572RoundedFacts (by rfl)

private theorem leaf4572FlatSound : Sound leaf4572Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4572CertificateValid
    leaf4572InnerLogValid leaf4572CoversExact leaf4572LowerChecked

private noncomputable def leaf4573Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (43/128), chiHi := (11/32) }

private noncomputable def leaf4573Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435739/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357530624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (541736379/536870912) }, upper := { exponent := 1, mantissa := (1051/1024) } }, logOuter := sk134LogOuterCertificate, logK := sk134LogKCertificate, logChi := chi252LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716253183/68715061248) } }, logDArg := sk134LogDArgCertificate }

private noncomputable def leaf4573InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4573LocalValidity :
    LeafFacts leaf4573Box leaf4573Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4573Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357530624) }) = true
      norm_num [leaf4573Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4573CertificateValid :
    WideCertificateValid leaf4573Box leaf4573Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk134ValidityFacts chi252ValidityFacts
    leaf4573LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4573CoverageChecked :
    coverageCheck (innerAD leaf4573Box) leaf4573InnerLog = true := by
  rfl'

private theorem leaf4573InnerLogValid :
    leaf4573InnerLog.Valid 8 (innerAD leaf4573Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4573CoverageChecked

private noncomputable def leaf4573InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907343/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4573InputLogOnePlusV_eq :
    leaf4573InputLogOnePlusV = outerEnclosure 24
      (leaf4573Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4573RoundedFacts : LeafRoundedFacts 8
    leaf4573Certificate.logOnePlusV leaf4573InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4573InputLogOnePlusV_eq }

private noncomputable def leaf4573Inputs : Inputs :=
  inputsOfCaches globalInput sk134RoundedInputs
    chi252InputQChi innerPair116Input
    leaf4573InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4573LowerChecked :
    lowerCheck 24 leaf4573Box leaf4573Inputs = true := by
  rfl'

private theorem leaf4573CoversExact : CoversExact 8
    leaf4573Box leaf4573Certificate leaf4573InnerLog leaf4573Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk134RoundedFacts chi252RoundedFacts
    innerPair116RoundedFacts leaf4573RoundedFacts (by rfl)

private theorem leaf4573FlatSound : Sound leaf4573Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4573CertificateValid
    leaf4573InnerLogValid leaf4573CoversExact leaf4573LowerChecked

private noncomputable def leaf4574Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (21/64), chiHi := (43/128) }

private noncomputable def leaf4574Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435739/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357558784) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (538132119/536870912) }, upper := { exponent := 1, mantissa := (8353/8192) } }, logOuter := sk135LogOuterCertificate, logK := sk135LogKCertificate, logChi := chi251LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716281343/68715117568) } }, logDArg := sk135LogDArgCertificate }

private noncomputable def leaf4574InnerLog : WideLogData :=
  innerPair121Data

set_option maxRecDepth 1000000 in
private theorem leaf4574LocalValidity :
    LeafFacts leaf4574Box leaf4574Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4574Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357558784) }) = true
      norm_num [leaf4574Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4574CertificateValid :
    WideCertificateValid leaf4574Box leaf4574Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk135ValidityFacts chi251ValidityFacts
    leaf4574LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4574CoverageChecked :
    coverageCheck (innerAD leaf4574Box) leaf4574InnerLog = true := by
  rfl'

private theorem leaf4574InnerLogValid :
    leaf4574InnerLog.Valid 8 (innerAD leaf4574Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint87PositiveFacts.valid leaf4574CoverageChecked

private noncomputable def leaf4574InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629365/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4574InputLogOnePlusV_eq :
    leaf4574InputLogOnePlusV = outerEnclosure 24
      (leaf4574Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4574RoundedFacts : LeafRoundedFacts 8
    leaf4574Certificate.logOnePlusV leaf4574InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4574InputLogOnePlusV_eq }

private noncomputable def leaf4574Inputs : Inputs :=
  inputsOfCaches globalInput sk135RoundedInputs
    chi251InputQChi innerPair121Input
    leaf4574InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4574LowerChecked :
    lowerCheck 24 leaf4574Box leaf4574Inputs = true := by
  rfl'

private theorem leaf4574CoversExact : CoversExact 8
    leaf4574Box leaf4574Certificate leaf4574InnerLog leaf4574Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk135RoundedFacts chi251RoundedFacts
    innerPair121RoundedFacts leaf4574RoundedFacts (by rfl)

private theorem leaf4574FlatSound : Sound leaf4574Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4574CertificateValid
    leaf4574InnerLogValid leaf4574CoversExact leaf4574LowerChecked

private noncomputable def leaf4575Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (21/64), chiHi := (43/128) }

private noncomputable def leaf4575Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435741/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357536768) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (540884461/536870912) }, upper := { exponent := 1, mantissa := (2099/2048) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi251LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716259327/68715073536) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf4575InnerLog : WideLogData :=
  innerPair602Data

set_option maxRecDepth 1000000 in
private theorem leaf4575LocalValidity :
    LeafFacts leaf4575Box leaf4575Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4575Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357536768) }) = true
      norm_num [leaf4575Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4575CertificateValid :
    WideCertificateValid leaf4575Box leaf4575Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi251ValidityFacts
    leaf4575LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4575CoverageChecked :
    coverageCheck (innerAD leaf4575Box) leaf4575InnerLog = true := by
  rfl'

private theorem leaf4575InnerLogValid :
    leaf4575InnerLog.Valid 8 (innerAD leaf4575Box) :=
  wideLogDataValid_of_cachedCheck endpoint321PositiveFacts
    endpoint288PositiveFacts.valid leaf4575CoverageChecked

private noncomputable def leaf4575InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814685/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4575InputLogOnePlusV_eq :
    leaf4575InputLogOnePlusV = outerEnclosure 24
      (leaf4575Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4575RoundedFacts : LeafRoundedFacts 8
    leaf4575Certificate.logOnePlusV leaf4575InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4575InputLogOnePlusV_eq }

private noncomputable def leaf4575Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi251InputQChi innerPair602Input
    leaf4575InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4575LowerChecked :
    lowerCheck 24 leaf4575Box leaf4575Inputs = true := by
  rfl'

private theorem leaf4575CoversExact : CoversExact 8
    leaf4575Box leaf4575Certificate leaf4575InnerLog leaf4575Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi251RoundedFacts
    innerPair602RoundedFacts leaf4575RoundedFacts (by rfl)

private theorem leaf4575FlatSound : Sound leaf4575Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4575CertificateValid
    leaf4575InnerLogValid leaf4575CoversExact leaf4575LowerChecked

private noncomputable def leaf4576Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (43/128), chiHi := (11/32) }

private noncomputable def leaf4576Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435741/268435456) }, vSqrt := { lower := (65529/65536), upper := (2021101327/2021029888) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (544554253/536870912) }, upper := { exponent := 1, mantissa := (2113/2048) } }, logOuter := sk135LogOuterCertificate, logK := sk135LogKCertificate, logChi := chi252LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (4042131215/4042059776) } }, logDArg := sk135LogDArgCertificate }

private noncomputable def leaf4576InnerLog : WideLogData :=
  innerPair547Data

set_option maxRecDepth 1000000 in
private theorem leaf4576LocalValidity :
    LeafFacts leaf4576Box leaf4576Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4576Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (2021101327/2021029888) }) = true
      norm_num [leaf4576Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4576CertificateValid :
    WideCertificateValid leaf4576Box leaf4576Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk135ValidityFacts chi252ValidityFacts
    leaf4576LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4576CoverageChecked :
    coverageCheck (innerAD leaf4576Box) leaf4576InnerLog = true := by
  rfl'

private theorem leaf4576InnerLogValid :
    leaf4576InnerLog.Valid 8 (innerAD leaf4576Box) :=
  wideLogDataValid_of_cachedCheck endpoint283PositiveFacts
    endpoint86PositiveFacts.valid leaf4576CoverageChecked

private noncomputable def leaf4576InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629377/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4576InputLogOnePlusV_eq :
    leaf4576InputLogOnePlusV = outerEnclosure 24
      (leaf4576Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4576RoundedFacts : LeafRoundedFacts 8
    leaf4576Certificate.logOnePlusV leaf4576InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4576InputLogOnePlusV_eq }

private noncomputable def leaf4576Inputs : Inputs :=
  inputsOfCaches globalInput sk135RoundedInputs
    chi252InputQChi innerPair547Input
    leaf4576InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4576LowerChecked :
    lowerCheck 24 leaf4576Box leaf4576Inputs = true := by
  rfl'

private theorem leaf4576CoversExact : CoversExact 8
    leaf4576Box leaf4576Certificate leaf4576InnerLog leaf4576Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk135RoundedFacts chi252RoundedFacts
    innerPair547RoundedFacts leaf4576RoundedFacts (by rfl)

private theorem leaf4576FlatSound : Sound leaf4576Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4576CertificateValid
    leaf4576InnerLogValid leaf4576CoversExact leaf4576LowerChecked

private noncomputable def leaf4577Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (43/128), chiHi := (11/32) }

private noncomputable def leaf4577Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435743/268435456) }, vSqrt := { lower := (65529/65536), upper := (4908388937/4908212224) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (547372127/536870912) }, upper := { exponent := 1, mantissa := (531/512) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi252LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9816601161/9816424448) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf4577InnerLog : WideLogData :=
  innerPair311Data

set_option maxRecDepth 1000000 in
private theorem leaf4577LocalValidity :
    LeafFacts leaf4577Box leaf4577Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4577Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4908388937/4908212224) }) = true
      norm_num [leaf4577Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4577CertificateValid :
    WideCertificateValid leaf4577Box leaf4577Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi252ValidityFacts
    leaf4577LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4577CoverageChecked :
    coverageCheck (innerAD leaf4577Box) leaf4577InnerLog = true := by
  rfl'

private theorem leaf4577InnerLogValid :
    leaf4577InnerLog.Valid 8 (innerAD leaf4577Box) :=
  wideLogDataValid_of_cachedCheck endpoint82PositiveFacts
    endpoint86PositiveFacts.valid leaf4577CoverageChecked

private noncomputable def leaf4577InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629383/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4577InputLogOnePlusV_eq :
    leaf4577InputLogOnePlusV = outerEnclosure 24
      (leaf4577Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4577RoundedFacts : LeafRoundedFacts 8
    leaf4577Certificate.logOnePlusV leaf4577InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4577InputLogOnePlusV_eq }

private noncomputable def leaf4577Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi252InputQChi innerPair311Input
    leaf4577InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4577LowerChecked :
    lowerCheck 24 leaf4577Box leaf4577Inputs = true := by
  rfl'

private theorem leaf4577CoversExact : CoversExact 8
    leaf4577Box leaf4577Certificate leaf4577InnerLog leaf4577Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi252RoundedFacts
    innerPair311RoundedFacts leaf4577RoundedFacts (by rfl)

private theorem leaf4577FlatSound : Sound leaf4577Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4577CertificateValid
    leaf4577InnerLogValid leaf4577CoversExact leaf4577LowerChecked

private noncomputable def leaf4578Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (5/16), chiHi := (81/256) }

private noncomputable def leaf4578Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871275/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357644032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1061093783/536870912) }, upper := { exponent := 0, mantissa := (16373/8192) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi289LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716366591/68715288064) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf4578InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4578LocalValidity :
    LeafFacts leaf4578Box leaf4578Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4578Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357644032) }) = true
      norm_num [leaf4578Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4578CertificateValid :
    WideCertificateValid leaf4578Box leaf4578Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi289ValidityFacts
    leaf4578LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4578CoverageChecked :
    coverageCheck (innerAD leaf4578Box) leaf4578InnerLog = true := by
  rfl'

private theorem leaf4578InnerLogValid :
    leaf4578InnerLog.Valid 8 (innerAD leaf4578Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4578CoverageChecked

private noncomputable def leaf4578InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (363417/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf4578InputLogOnePlusV_eq :
    leaf4578InputLogOnePlusV = outerEnclosure 24
      (leaf4578Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4578RoundedFacts : LeafRoundedFacts 8
    leaf4578Certificate.logOnePlusV leaf4578InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4578InputLogOnePlusV_eq }

private noncomputable def leaf4578Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi289InputQChi innerPair108Input
    leaf4578InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4578LowerChecked :
    lowerCheck 24 leaf4578Box leaf4578Inputs = true := by
  rfl'

private theorem leaf4578CoversExact : CoversExact 8
    leaf4578Box leaf4578Certificate leaf4578InnerLog leaf4578Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi289RoundedFacts
    innerPair108RoundedFacts leaf4578RoundedFacts (by rfl)

private theorem leaf4578FlatSound : Sound leaf4578Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4578CertificateValid
    leaf4578InnerLogValid leaf4578CoversExact leaf4578LowerChecked

private noncomputable def leaf4579Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (81/256), chiHi := (41/128) }

private noncomputable def leaf4579Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871277/536870912) }, vSqrt := { lower := (65529/65536), upper := (4908388937/4908231168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1067646981/536870912) }, upper := { exponent := 1, mantissa := (8237/8192) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi290LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9816620105/9816462336) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf4579InnerLog : WideLogData :=
  innerPair110Data

set_option maxRecDepth 1000000 in
private theorem leaf4579LocalValidity :
    LeafFacts leaf4579Box leaf4579Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4579Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4908388937/4908231168) }) = true
      norm_num [leaf4579Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4579CertificateValid :
    WideCertificateValid leaf4579Box leaf4579Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi290ValidityFacts
    leaf4579LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4579CoverageChecked :
    coverageCheck (innerAD leaf4579Box) leaf4579InnerLog = true := by
  rfl'

private theorem leaf4579InnerLogValid :
    leaf4579InnerLog.Valid 8 (innerAD leaf4579Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint72PositiveFacts.valid leaf4579CoverageChecked

private noncomputable def leaf4579InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814675/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4579InputLogOnePlusV_eq :
    leaf4579InputLogOnePlusV = outerEnclosure 24
      (leaf4579Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4579RoundedFacts : LeafRoundedFacts 8
    leaf4579Certificate.logOnePlusV leaf4579InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4579InputLogOnePlusV_eq }

private noncomputable def leaf4579Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi290InputQChi innerPair110Input
    leaf4579InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4579LowerChecked :
    lowerCheck 24 leaf4579Box leaf4579Inputs = true := by
  rfl'

private theorem leaf4579CoversExact : CoversExact 8
    leaf4579Box leaf4579Certificate leaf4579InnerLog leaf4579Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi290RoundedFacts
    innerPair110RoundedFacts leaf4579RoundedFacts (by rfl)

private theorem leaf4579FlatSound : Sound leaf4579Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4579CertificateValid
    leaf4579InnerLogValid leaf4579CoversExact leaf4579LowerChecked

private noncomputable def leaf4580Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (5/16), chiHi := (81/256) }

private noncomputable def leaf4580Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871277/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357623296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1066336341/536870912) }, upper := { exponent := 1, mantissa := (8227/8192) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi289LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716345855/68715246592) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf4580InnerLog : WideLogData :=
  innerPair110Data

set_option maxRecDepth 1000000 in
private theorem leaf4580LocalValidity :
    LeafFacts leaf4580Box leaf4580Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4580Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357623296) }) = true
      norm_num [leaf4580Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4580CertificateValid :
    WideCertificateValid leaf4580Box leaf4580Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi289ValidityFacts
    leaf4580LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4580CoverageChecked :
    coverageCheck (innerAD leaf4580Box) leaf4580InnerLog = true := by
  rfl'

private theorem leaf4580InnerLogValid :
    leaf4580InnerLog.Valid 8 (innerAD leaf4580Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint72PositiveFacts.valid leaf4580CoverageChecked

private noncomputable def leaf4580InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629349/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4580InputLogOnePlusV_eq :
    leaf4580InputLogOnePlusV = outerEnclosure 24
      (leaf4580Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4580RoundedFacts : LeafRoundedFacts 8
    leaf4580Certificate.logOnePlusV leaf4580InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4580InputLogOnePlusV_eq }

private noncomputable def leaf4580Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi289InputQChi innerPair110Input
    leaf4580InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4580LowerChecked :
    lowerCheck 24 leaf4580Box leaf4580Inputs = true := by
  rfl'

private theorem leaf4580CoversExact : CoversExact 8
    leaf4580Box leaf4580Certificate leaf4580InnerLog leaf4580Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi289RoundedFacts
    innerPair110RoundedFacts leaf4580RoundedFacts (by rfl)

private theorem leaf4580FlatSound : Sound leaf4580Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4580CertificateValid
    leaf4580InnerLogValid leaf4580CoversExact leaf4580LowerChecked

private noncomputable def leaf4581Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (81/256), chiHi := (41/128) }

private noncomputable def leaf4581Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871279/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357597184) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1072955071/536870912) }, upper := { exponent := 1, mantissa := (4139/4096) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi290LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716319743/68715194368) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf4581InnerLog : WideLogData :=
  innerPair110Data

set_option maxRecDepth 1000000 in
private theorem leaf4581LocalValidity :
    LeafFacts leaf4581Box leaf4581Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4581Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357597184) }) = true
      norm_num [leaf4581Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4581CertificateValid :
    WideCertificateValid leaf4581Box leaf4581Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi290ValidityFacts
    leaf4581LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4581CoverageChecked :
    coverageCheck (innerAD leaf4581Box) leaf4581InnerLog = true := by
  rfl'

private theorem leaf4581InnerLogValid :
    leaf4581InnerLog.Valid 8 (innerAD leaf4581Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint72PositiveFacts.valid leaf4581CoverageChecked

private noncomputable def leaf4581InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907339/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4581InputLogOnePlusV_eq :
    leaf4581InputLogOnePlusV = outerEnclosure 24
      (leaf4581Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4581RoundedFacts : LeafRoundedFacts 8
    leaf4581Certificate.logOnePlusV leaf4581InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4581InputLogOnePlusV_eq }

private noncomputable def leaf4581Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi290InputQChi innerPair110Input
    leaf4581InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4581LowerChecked :
    lowerCheck 24 leaf4581Box leaf4581Inputs = true := by
  rfl'

private theorem leaf4581CoversExact : CoversExact 8
    leaf4581Box leaf4581Certificate leaf4581InnerLog leaf4581Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi290RoundedFacts
    innerPair110RoundedFacts leaf4581RoundedFacts (by rfl)

private theorem leaf4581FlatSound : Sound leaf4581Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4581CertificateValid
    leaf4581InnerLogValid leaf4581CoversExact leaf4581LowerChecked

private noncomputable def leaf4582Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (41/128), chiHi := (21/64) }

private noncomputable def leaf4582Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435741/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357566464) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (537083605/536870912) }, upper := { exponent := 1, mantissa := (4169/4096) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi250LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716289023/68715132928) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf4582InnerLog : WideLogData :=
  innerPair123Data

set_option maxRecDepth 1000000 in
private theorem leaf4582LocalValidity :
    LeafFacts leaf4582Box leaf4582Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4582Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357566464) }) = true
      norm_num [leaf4582Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4582CertificateValid :
    WideCertificateValid leaf4582Box leaf4582Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi250ValidityFacts
    leaf4582LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4582CoverageChecked :
    coverageCheck (innerAD leaf4582Box) leaf4582InnerLog = true := by
  rfl'

private theorem leaf4582InnerLogValid :
    leaf4582InnerLog.Valid 8 (innerAD leaf4582Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint329PositiveFacts.valid leaf4582CoverageChecked

private noncomputable def leaf4582InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629363/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4582InputLogOnePlusV_eq :
    leaf4582InputLogOnePlusV = outerEnclosure 24
      (leaf4582Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4582RoundedFacts : LeafRoundedFacts 8
    leaf4582Certificate.logOnePlusV leaf4582InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4582InputLogOnePlusV_eq }

private noncomputable def leaf4582Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi250InputQChi innerPair123Input
    leaf4582InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4582LowerChecked :
    lowerCheck 24 leaf4582Box leaf4582Inputs = true := by
  rfl'

private theorem leaf4582CoversExact : CoversExact 8
    leaf4582Box leaf4582Certificate leaf4582InnerLog leaf4582Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi250RoundedFacts
    innerPair123RoundedFacts leaf4582RoundedFacts (by rfl)

private theorem leaf4582FlatSound : Sound leaf4582Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4582CertificateValid
    leaf4582InnerLogValid leaf4582CoversExact leaf4582LowerChecked

private noncomputable def leaf4583Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (41/128), chiHi := (83/256) }

private noncomputable def leaf4583Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871281/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357571072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1079573801/1073741824) }, upper := { exponent := 1, mantissa := (8329/8192) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi291LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716293631/68715142144) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf4583InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4583LocalValidity :
    LeafFacts leaf4583Box leaf4583Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4583Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357571072) }) = true
      norm_num [leaf4583Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4583CertificateValid :
    WideCertificateValid leaf4583Box leaf4583Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi291ValidityFacts
    leaf4583LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4583CoverageChecked :
    coverageCheck (innerAD leaf4583Box) leaf4583InnerLog = true := by
  rfl'

private theorem leaf4583InnerLogValid :
    leaf4583InnerLog.Valid 8 (innerAD leaf4583Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4583CoverageChecked

private noncomputable def leaf4583InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814681/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4583InputLogOnePlusV_eq :
    leaf4583InputLogOnePlusV = outerEnclosure 24
      (leaf4583Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4583RoundedFacts : LeafRoundedFacts 8
    leaf4583Certificate.logOnePlusV leaf4583InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4583InputLogOnePlusV_eq }

private noncomputable def leaf4583Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi291InputQChi innerPair116Input
    leaf4583InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4583LowerChecked :
    lowerCheck 24 leaf4583Box leaf4583Inputs = true := by
  rfl'

private theorem leaf4583CoversExact : CoversExact 8
    leaf4583Box leaf4583Certificate leaf4583InnerLog leaf4583Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi291RoundedFacts
    innerPair116RoundedFacts leaf4583RoundedFacts (by rfl)

private theorem leaf4583FlatSound : Sound leaf4583Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4583CertificateValid
    leaf4583InnerLogValid leaf4583CoversExact leaf4583LowerChecked

private noncomputable def leaf4584Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (83/256), chiHi := (21/64) }

private noncomputable def leaf4584Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871283/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357544960) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1086192531/1073741824) }, upper := { exponent := 1, mantissa := (2095/2048) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi292LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716267519/68715089920) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf4584InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4584LocalValidity :
    LeafFacts leaf4584Box leaf4584Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4584Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357544960) }) = true
      norm_num [leaf4584Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4584CertificateValid :
    WideCertificateValid leaf4584Box leaf4584Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi292ValidityFacts
    leaf4584LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4584CoverageChecked :
    coverageCheck (innerAD leaf4584Box) leaf4584InnerLog = true := by
  rfl'

private theorem leaf4584InnerLogValid :
    leaf4584InnerLog.Valid 8 (innerAD leaf4584Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4584CoverageChecked

private noncomputable def leaf4584InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453671/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf4584InputLogOnePlusV_eq :
    leaf4584InputLogOnePlusV = outerEnclosure 24
      (leaf4584Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4584RoundedFacts : LeafRoundedFacts 8
    leaf4584Certificate.logOnePlusV leaf4584InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4584InputLogOnePlusV_eq }

private noncomputable def leaf4584Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi292InputQChi innerPair116Input
    leaf4584InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4584LowerChecked :
    lowerCheck 24 leaf4584Box leaf4584Inputs = true := by
  rfl'

private theorem leaf4584CoversExact : CoversExact 8
    leaf4584Box leaf4584Certificate leaf4584InnerLog leaf4584Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi292RoundedFacts
    innerPair116RoundedFacts leaf4584RoundedFacts (by rfl)

private theorem leaf4584FlatSound : Sound leaf4584Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4584CertificateValid
    leaf4584InnerLogValid leaf4584CoversExact leaf4584LowerChecked

private noncomputable def leaf4585Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (5/16), chiHi := (81/256) }

private noncomputable def leaf4585Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871279/536870912) }, vSqrt := { lower := (65529/65536), upper := (1108345889/1108309760) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1071578899/536870912) }, upper := { exponent := 1, mantissa := (16535/16384) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi289LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (2216655649/2216619520) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf4585InnerLog : WideLogData :=
  innerPair110Data

set_option maxRecDepth 1000000 in
private theorem leaf4585LocalValidity :
    LeafFacts leaf4585Box leaf4585Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4585Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (1108345889/1108309760) }) = true
      norm_num [leaf4585Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4585CertificateValid :
    WideCertificateValid leaf4585Box leaf4585Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi289ValidityFacts
    leaf4585LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4585CoverageChecked :
    coverageCheck (innerAD leaf4585Box) leaf4585InnerLog = true := by
  rfl'

private theorem leaf4585InnerLogValid :
    leaf4585InnerLog.Valid 8 (innerAD leaf4585Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint72PositiveFacts.valid leaf4585CoverageChecked

private noncomputable def leaf4585InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814677/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4585InputLogOnePlusV_eq :
    leaf4585InputLogOnePlusV = outerEnclosure 24
      (leaf4585Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4585RoundedFacts : LeafRoundedFacts 8
    leaf4585Certificate.logOnePlusV leaf4585InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4585InputLogOnePlusV_eq }

private noncomputable def leaf4585Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi289InputQChi innerPair110Input
    leaf4585InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4585LowerChecked :
    lowerCheck 24 leaf4585Box leaf4585Inputs = true := by
  rfl'

private theorem leaf4585CoversExact : CoversExact 8
    leaf4585Box leaf4585Certificate leaf4585InnerLog leaf4585Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi289RoundedFacts
    innerPair110RoundedFacts leaf4585RoundedFacts (by rfl)

private theorem leaf4585FlatSound : Sound leaf4585Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4585CertificateValid
    leaf4585InnerLogValid leaf4585CoversExact leaf4585LowerChecked

private noncomputable def leaf4586Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (81/256), chiHi := (41/128) }

private noncomputable def leaf4586Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871281/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357576192) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1078263161/1073741824) }, upper := { exponent := 1, mantissa := (8319/8192) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi290LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716298751/68715152384) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf4586InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4586LocalValidity :
    LeafFacts leaf4586Box leaf4586Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4586Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357576192) }) = true
      norm_num [leaf4586Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4586CertificateValid :
    WideCertificateValid leaf4586Box leaf4586Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi290ValidityFacts
    leaf4586LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4586CoverageChecked :
    coverageCheck (innerAD leaf4586Box) leaf4586InnerLog = true := by
  rfl'

private theorem leaf4586InnerLogValid :
    leaf4586InnerLog.Valid 8 (innerAD leaf4586Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4586CoverageChecked

private noncomputable def leaf4586InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629361/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4586InputLogOnePlusV_eq :
    leaf4586InputLogOnePlusV = outerEnclosure 24
      (leaf4586Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4586RoundedFacts : LeafRoundedFacts 8
    leaf4586Certificate.logOnePlusV leaf4586InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4586InputLogOnePlusV_eq }

private noncomputable def leaf4586Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi290InputQChi innerPair116Input
    leaf4586InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4586LowerChecked :
    lowerCheck 24 leaf4586Box leaf4586Inputs = true := by
  rfl'

private theorem leaf4586CoversExact : CoversExact 8
    leaf4586Box leaf4586Certificate leaf4586InnerLog leaf4586Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi290RoundedFacts
    innerPair116RoundedFacts leaf4586RoundedFacts (by rfl)

private theorem leaf4586FlatSound : Sound leaf4586Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4586CertificateValid
    leaf4586InnerLogValid leaf4586CoversExact leaf4586LowerChecked

private noncomputable def leaf4587Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (5/16), chiHi := (81/256) }

private noncomputable def leaf4587Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871281/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357581824) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1076821457/1073741824) }, upper := { exponent := 1, mantissa := (2077/2048) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi289LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716304383/68715163648) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf4587InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4587LocalValidity :
    LeafFacts leaf4587Box leaf4587Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4587Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357581824) }) = true
      norm_num [leaf4587Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4587CertificateValid :
    WideCertificateValid leaf4587Box leaf4587Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi289ValidityFacts
    leaf4587LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4587CoverageChecked :
    coverageCheck (innerAD leaf4587Box) leaf4587InnerLog = true := by
  rfl'

private theorem leaf4587InnerLogValid :
    leaf4587InnerLog.Valid 8 (innerAD leaf4587Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4587CoverageChecked

private noncomputable def leaf4587InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629359/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4587InputLogOnePlusV_eq :
    leaf4587InputLogOnePlusV = outerEnclosure 24
      (leaf4587Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4587RoundedFacts : LeafRoundedFacts 8
    leaf4587Certificate.logOnePlusV leaf4587InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4587InputLogOnePlusV_eq }

private noncomputable def leaf4587Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi289InputQChi innerPair116Input
    leaf4587InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4587LowerChecked :
    lowerCheck 24 leaf4587Box leaf4587Inputs = true := by
  rfl'

private theorem leaf4587CoversExact : CoversExact 8
    leaf4587Box leaf4587Certificate leaf4587InnerLog leaf4587Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi289RoundedFacts
    innerPair116RoundedFacts leaf4587RoundedFacts (by rfl)

private theorem leaf4587FlatSound : Sound leaf4587Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4587CertificateValid
    leaf4587InnerLogValid leaf4587CoversExact leaf4587LowerChecked

private noncomputable def leaf4588Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (81/256), chiHi := (41/128) }

private noncomputable def leaf4588Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871283/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357555200) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1083571251/1073741824) }, upper := { exponent := 1, mantissa := (1045/1024) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi290LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716277759/68715110400) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf4588InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4588LocalValidity :
    LeafFacts leaf4588Box leaf4588Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4588Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357555200) }) = true
      norm_num [leaf4588Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4588CertificateValid :
    WideCertificateValid leaf4588Box leaf4588Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi290ValidityFacts
    leaf4588LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4588CoverageChecked :
    coverageCheck (innerAD leaf4588Box) leaf4588InnerLog = true := by
  rfl'

private theorem leaf4588InnerLogValid :
    leaf4588InnerLog.Valid 8 (innerAD leaf4588Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4588CoverageChecked

private noncomputable def leaf4588InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814683/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4588InputLogOnePlusV_eq :
    leaf4588InputLogOnePlusV = outerEnclosure 24
      (leaf4588Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4588RoundedFacts : LeafRoundedFacts 8
    leaf4588Certificate.logOnePlusV leaf4588InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4588InputLogOnePlusV_eq }

private noncomputable def leaf4588Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi290InputQChi innerPair116Input
    leaf4588InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4588LowerChecked :
    lowerCheck 24 leaf4588Box leaf4588Inputs = true := by
  rfl'

private theorem leaf4588CoversExact : CoversExact 8
    leaf4588Box leaf4588Certificate leaf4588InnerLog leaf4588Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi290RoundedFacts
    innerPair116RoundedFacts leaf4588RoundedFacts (by rfl)

private theorem leaf4588FlatSound : Sound leaf4588Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4588CertificateValid
    leaf4588InnerLogValid leaf4588CoversExact leaf4588LowerChecked

private noncomputable def leaf4589Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (41/128), chiHi := (83/256) }

private noncomputable def leaf4589Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871283/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357549824) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1084947423/1073741824) }, upper := { exponent := 1, mantissa := (16741/16384) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi291LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716272383/68715099648) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf4589InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4589LocalValidity :
    LeafFacts leaf4589Box leaf4589Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4589Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357549824) }) = true
      norm_num [leaf4589Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4589CertificateValid :
    WideCertificateValid leaf4589Box leaf4589Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi291ValidityFacts
    leaf4589LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4589CoverageChecked :
    coverageCheck (innerAD leaf4589Box) leaf4589InnerLog = true := by
  rfl'

private theorem leaf4589InnerLogValid :
    leaf4589InnerLog.Valid 8 (innerAD leaf4589Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4589CoverageChecked

private noncomputable def leaf4589InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629367/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4589InputLogOnePlusV_eq :
    leaf4589InputLogOnePlusV = outerEnclosure 24
      (leaf4589Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4589RoundedFacts : LeafRoundedFacts 8
    leaf4589Certificate.logOnePlusV leaf4589InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4589InputLogOnePlusV_eq }

private noncomputable def leaf4589Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi291InputQChi innerPair116Input
    leaf4589InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4589LowerChecked :
    lowerCheck 24 leaf4589Box leaf4589Inputs = true := by
  rfl'

private theorem leaf4589CoversExact : CoversExact 8
    leaf4589Box leaf4589Certificate leaf4589InnerLog leaf4589Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi291RoundedFacts
    innerPair116RoundedFacts leaf4589RoundedFacts (by rfl)

private theorem leaf4589FlatSound : Sound leaf4589Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4589CertificateValid
    leaf4589InnerLogValid leaf4589CoversExact leaf4589LowerChecked

private noncomputable def leaf4590Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (83/256), chiHi := (21/64) }

private noncomputable def leaf4590Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871285/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357523456) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1091631685/1073741824) }, upper := { exponent := 1, mantissa := (4211/4096) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi292LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716246015/68715046912) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf4590InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4590LocalValidity :
    LeafFacts leaf4590Box leaf4590Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4590Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357523456) }) = true
      norm_num [leaf4590Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4590CertificateValid :
    WideCertificateValid leaf4590Box leaf4590Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi292ValidityFacts
    leaf4590LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4590CoverageChecked :
    coverageCheck (innerAD leaf4590Box) leaf4590InnerLog = true := by
  rfl'

private theorem leaf4590InnerLogValid :
    leaf4590InnerLog.Valid 8 (innerAD leaf4590Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4590CoverageChecked

private noncomputable def leaf4590InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814687/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4590InputLogOnePlusV_eq :
    leaf4590InputLogOnePlusV = outerEnclosure 24
      (leaf4590Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4590RoundedFacts : LeafRoundedFacts 8
    leaf4590Certificate.logOnePlusV leaf4590InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4590InputLogOnePlusV_eq }

private noncomputable def leaf4590Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi292InputQChi innerPair116Input
    leaf4590InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4590LowerChecked :
    lowerCheck 24 leaf4590Box leaf4590Inputs = true := by
  rfl'

private theorem leaf4590CoversExact : CoversExact 8
    leaf4590Box leaf4590Certificate leaf4590InnerLog leaf4590Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi292RoundedFacts
    innerPair116RoundedFacts leaf4590RoundedFacts (by rfl)

private theorem leaf4590FlatSound : Sound leaf4590Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4590CertificateValid
    leaf4590InnerLogValid leaf4590CoversExact leaf4590LowerChecked

private noncomputable def leaf4591Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (41/128), chiHi := (83/256) }

private noncomputable def leaf4591Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871285/536870912) }, vSqrt := { lower := (65529/65536), upper := (4908388937/4908218368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1090321045/1073741824) }, upper := { exponent := 1, mantissa := (2103/2048) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi291LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9816607305/9816436736) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf4591InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4591LocalValidity :
    LeafFacts leaf4591Box leaf4591Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4591Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4908388937/4908218368) }) = true
      norm_num [leaf4591Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4591CertificateValid :
    WideCertificateValid leaf4591Box leaf4591Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi291ValidityFacts
    leaf4591LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4591CoverageChecked :
    coverageCheck (innerAD leaf4591Box) leaf4591InnerLog = true := by
  rfl'

private theorem leaf4591InnerLogValid :
    leaf4591InnerLog.Valid 8 (innerAD leaf4591Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4591CoverageChecked

private noncomputable def leaf4591InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907343/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4591InputLogOnePlusV_eq :
    leaf4591InputLogOnePlusV = outerEnclosure 24
      (leaf4591Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4591RoundedFacts : LeafRoundedFacts 8
    leaf4591Certificate.logOnePlusV leaf4591InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4591InputLogOnePlusV_eq }

private noncomputable def leaf4591Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi291InputQChi innerPair116Input
    leaf4591InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4591LowerChecked :
    lowerCheck 24 leaf4591Box leaf4591Inputs = true := by
  rfl'

private theorem leaf4591CoversExact : CoversExact 8
    leaf4591Box leaf4591Certificate leaf4591InnerLog leaf4591Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi291RoundedFacts
    innerPair116RoundedFacts leaf4591RoundedFacts (by rfl)

private theorem leaf4591FlatSound : Sound leaf4591Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4591CertificateValid
    leaf4591InnerLogValid leaf4591CoversExact leaf4591LowerChecked

private noncomputable def leaf4592Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (83/256), chiHi := (21/64) }

private noncomputable def leaf4592Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871287/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357501952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1097070839/1073741824) }, upper := { exponent := 1, mantissa := (529/512) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi292LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716224511/68715003904) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf4592InnerLog : WideLogData :=
  innerPair311Data

set_option maxRecDepth 1000000 in
private theorem leaf4592LocalValidity :
    LeafFacts leaf4592Box leaf4592Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4592Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357501952) }) = true
      norm_num [leaf4592Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4592CertificateValid :
    WideCertificateValid leaf4592Box leaf4592Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi292ValidityFacts
    leaf4592LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4592CoverageChecked :
    coverageCheck (innerAD leaf4592Box) leaf4592InnerLog = true := by
  rfl'

private theorem leaf4592InnerLogValid :
    leaf4592InnerLog.Valid 8 (innerAD leaf4592Box) :=
  wideLogDataValid_of_cachedCheck endpoint82PositiveFacts
    endpoint86PositiveFacts.valid leaf4592CoverageChecked

private noncomputable def leaf4592InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629379/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4592InputLogOnePlusV_eq :
    leaf4592InputLogOnePlusV = outerEnclosure 24
      (leaf4592Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4592RoundedFacts : LeafRoundedFacts 8
    leaf4592Certificate.logOnePlusV leaf4592InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4592InputLogOnePlusV_eq }

private noncomputable def leaf4592Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi292InputQChi innerPair311Input
    leaf4592InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4592LowerChecked :
    lowerCheck 24 leaf4592Box leaf4592Inputs = true := by
  rfl'

private theorem leaf4592CoversExact : CoversExact 8
    leaf4592Box leaf4592Certificate leaf4592InnerLog leaf4592Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi292RoundedFacts
    innerPair311RoundedFacts leaf4592RoundedFacts (by rfl)

private theorem leaf4592FlatSound : Sound leaf4592Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4592CertificateValid
    leaf4592InnerLogValid leaf4592CoversExact leaf4592LowerChecked

private noncomputable def leaf4593Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (21/64), chiHi := (43/128) }

private noncomputable def leaf4593Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435743/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357514752) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (543636803/536870912) }, upper := { exponent := 1, mantissa := (8439/8192) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi251LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716237311/68715029504) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf4593InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4593LocalValidity :
    LeafFacts leaf4593Box leaf4593Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4593Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357514752) }) = true
      norm_num [leaf4593Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4593CertificateValid :
    WideCertificateValid leaf4593Box leaf4593Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi251ValidityFacts
    leaf4593LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4593CoverageChecked :
    coverageCheck (innerAD leaf4593Box) leaf4593InnerLog = true := by
  rfl'

private theorem leaf4593InnerLogValid :
    leaf4593InnerLog.Valid 8 (innerAD leaf4593Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4593CoverageChecked

private noncomputable def leaf4593InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (181709/262144) }

set_option maxRecDepth 1000000 in
private theorem leaf4593InputLogOnePlusV_eq :
    leaf4593InputLogOnePlusV = outerEnclosure 24
      (leaf4593Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4593RoundedFacts : LeafRoundedFacts 8
    leaf4593Certificate.logOnePlusV leaf4593InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4593InputLogOnePlusV_eq }

private noncomputable def leaf4593Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi251InputQChi innerPair116Input
    leaf4593InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4593LowerChecked :
    lowerCheck 24 leaf4593Box leaf4593Inputs = true := by
  rfl'

private theorem leaf4593CoversExact : CoversExact 8
    leaf4593Box leaf4593Certificate leaf4593InnerLog leaf4593Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi251RoundedFacts
    innerPair116RoundedFacts leaf4593RoundedFacts (by rfl)

private theorem leaf4593FlatSound : Sound leaf4593Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4593CertificateValid
    leaf4593InnerLogValid leaf4593CoversExact leaf4593LowerChecked

private noncomputable def leaf4594Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (21/64), chiHi := (43/128) }

private noncomputable def leaf4594Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435745/268435456) }, vSqrt := { lower := (65529/65536), upper := (4908388937/4908213248) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (546389145/536870912) }, upper := { exponent := 1, mantissa := (4241/4096) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi251LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9816602185/9816426496) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf4594InnerLog : WideLogData :=
  innerPair605Data

set_option maxRecDepth 1000000 in
private theorem leaf4594LocalValidity :
    LeafFacts leaf4594Box leaf4594Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4594Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4908388937/4908213248) }) = true
      norm_num [leaf4594Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4594CertificateValid :
    WideCertificateValid leaf4594Box leaf4594Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi251ValidityFacts
    leaf4594LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4594CoverageChecked :
    coverageCheck (innerAD leaf4594Box) leaf4594InnerLog = true := by
  rfl'

private theorem leaf4594InnerLogValid :
    leaf4594InnerLog.Valid 8 (innerAD leaf4594Box) :=
  wideLogDataValid_of_cachedCheck endpoint330PositiveFacts
    endpoint331PositiveFacts.valid leaf4594CoverageChecked

private noncomputable def leaf4594InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629381/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4594InputLogOnePlusV_eq :
    leaf4594InputLogOnePlusV = outerEnclosure 24
      (leaf4594Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4594RoundedFacts : LeafRoundedFacts 8
    leaf4594Certificate.logOnePlusV leaf4594InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4594InputLogOnePlusV_eq }

private noncomputable def leaf4594Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi251InputQChi innerPair605Input
    leaf4594InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4594LowerChecked :
    lowerCheck 24 leaf4594Box leaf4594Inputs = true := by
  rfl'

private theorem leaf4594CoversExact : CoversExact 8
    leaf4594Box leaf4594Certificate leaf4594InnerLog leaf4594Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi251RoundedFacts
    innerPair605RoundedFacts leaf4594RoundedFacts (by rfl)

private theorem leaf4594FlatSound : Sound leaf4594Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4594CertificateValid
    leaf4594InnerLogValid leaf4594CoversExact leaf4594LowerChecked

private noncomputable def leaf4595Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (43/128), chiHi := (11/32) }

private noncomputable def leaf4595Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435745/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357463040) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (550190001/536870912) }, upper := { exponent := 1, mantissa := (2135/2048) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi252LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716185599/68714926080) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf4595InnerLog : WideLogData :=
  innerPair329Data

set_option maxRecDepth 1000000 in
private theorem leaf4595LocalValidity :
    LeafFacts leaf4595Box leaf4595Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4595Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357463040) }) = true
      norm_num [leaf4595Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4595CertificateValid :
    WideCertificateValid leaf4595Box leaf4595Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi252ValidityFacts
    leaf4595LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4595CoverageChecked :
    coverageCheck (innerAD leaf4595Box) leaf4595InnerLog = true := by
  rfl'

private theorem leaf4595InnerLogValid :
    leaf4595InnerLog.Valid 8 (innerAD leaf4595Box) :=
  wideLogDataValid_of_cachedCheck endpoint87PositiveFacts
    endpoint284PositiveFacts.valid leaf4595CoverageChecked

private noncomputable def leaf4595InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907347/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4595InputLogOnePlusV_eq :
    leaf4595InputLogOnePlusV = outerEnclosure 24
      (leaf4595Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4595RoundedFacts : LeafRoundedFacts 8
    leaf4595Certificate.logOnePlusV leaf4595InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4595InputLogOnePlusV_eq }

private noncomputable def leaf4595Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi252InputQChi innerPair329Input
    leaf4595InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4595LowerChecked :
    lowerCheck 24 leaf4595Box leaf4595Inputs = true := by
  rfl'

private theorem leaf4595CoversExact : CoversExact 8
    leaf4595Box leaf4595Certificate leaf4595InnerLog leaf4595Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi252RoundedFacts
    innerPair329RoundedFacts leaf4595RoundedFacts (by rfl)

private theorem leaf4595FlatSound : Sound leaf4595Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4595CertificateValid
    leaf4595InnerLogValid leaf4595CoversExact leaf4595LowerChecked

private noncomputable def leaf4596Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (43/128), chiHi := (11/32) }

private noncomputable def leaf4596Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435747/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357440512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (553007875/536870912) }, upper := { exponent := 1, mantissa := (1073/1024) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi252LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716163071/68714881024) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf4596InnerLog : WideLogData :=
  innerPair607Data

set_option maxRecDepth 1000000 in
private theorem leaf4596LocalValidity :
    LeafFacts leaf4596Box leaf4596Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4596Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357440512) }) = true
      norm_num [leaf4596Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4596CertificateValid :
    WideCertificateValid leaf4596Box leaf4596Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi252ValidityFacts
    leaf4596LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4596CoverageChecked :
    coverageCheck (innerAD leaf4596Box) leaf4596InnerLog = true := by
  rfl'

private theorem leaf4596InnerLogValid :
    leaf4596InnerLog.Valid 8 (innerAD leaf4596Box) :=
  wideLogDataValid_of_cachedCheck endpoint332PositiveFacts
    endpoint333PositiveFacts.valid leaf4596CoverageChecked

private noncomputable def leaf4596InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814697/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4596InputLogOnePlusV_eq :
    leaf4596InputLogOnePlusV = outerEnclosure 24
      (leaf4596Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4596RoundedFacts : LeafRoundedFacts 8
    leaf4596Certificate.logOnePlusV leaf4596InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4596InputLogOnePlusV_eq }

private noncomputable def leaf4596Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi252InputQChi innerPair607Input
    leaf4596InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4596LowerChecked :
    lowerCheck 24 leaf4596Box leaf4596Inputs = true := by
  rfl'

private theorem leaf4596CoversExact : CoversExact 8
    leaf4596Box leaf4596Certificate leaf4596InnerLog leaf4596Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi252RoundedFacts
    innerPair607RoundedFacts leaf4596RoundedFacts (by rfl)

private theorem leaf4596FlatSound : Sound leaf4596Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4596CertificateValid
    leaf4596InnerLogValid leaf4596CoversExact leaf4596LowerChecked

private noncomputable def leaf4597Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (21/64), chiHi := (85/256) }

private noncomputable def leaf4597Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871287/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357497088) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1098315947/1073741824) }, upper := { exponent := 1, mantissa := (16947/16384) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi293LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716219647/68714994176) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf4597InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf4597LocalValidity :
    LeafFacts leaf4597Box leaf4597Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4597Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357497088) }) = true
      norm_num [leaf4597Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4597CertificateValid :
    WideCertificateValid leaf4597Box leaf4597Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi293ValidityFacts
    leaf4597LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4597CoverageChecked :
    coverageCheck (innerAD leaf4597Box) leaf4597InnerLog = true := by
  rfl'

private theorem leaf4597InnerLogValid :
    leaf4597InnerLog.Valid 8 (innerAD leaf4597Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf4597CoverageChecked

private noncomputable def leaf4597InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907345/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4597InputLogOnePlusV_eq :
    leaf4597InputLogOnePlusV = outerEnclosure 24
      (leaf4597Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4597RoundedFacts : LeafRoundedFacts 8
    leaf4597Certificate.logOnePlusV leaf4597InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4597InputLogOnePlusV_eq }

private noncomputable def leaf4597Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi293InputQChi innerPair117Input
    leaf4597InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4597LowerChecked :
    lowerCheck 24 leaf4597Box leaf4597Inputs = true := by
  rfl'

private theorem leaf4597CoversExact : CoversExact 8
    leaf4597Box leaf4597Certificate leaf4597InnerLog leaf4597Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi293RoundedFacts
    innerPair117RoundedFacts leaf4597RoundedFacts (by rfl)

private theorem leaf4597FlatSound : Sound leaf4597Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4597CertificateValid
    leaf4597InnerLogValid leaf4597CoversExact leaf4597LowerChecked

private noncomputable def leaf4598Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (85/256), chiHi := (43/128) }

private noncomputable def leaf4598Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871289/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357470720) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1105000209/1073741824) }, upper := { exponent := 1, mantissa := (8525/8192) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi294LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716193279/68714941440) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf4598InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf4598LocalValidity :
    LeafFacts leaf4598Box leaf4598Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4598Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357470720) }) = true
      norm_num [leaf4598Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4598CertificateValid :
    WideCertificateValid leaf4598Box leaf4598Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi294ValidityFacts
    leaf4598LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4598CoverageChecked :
    coverageCheck (innerAD leaf4598Box) leaf4598InnerLog = true := by
  rfl'

private theorem leaf4598InnerLogValid :
    leaf4598InnerLog.Valid 8 (innerAD leaf4598Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf4598CoverageChecked

private noncomputable def leaf4598InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814693/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4598InputLogOnePlusV_eq :
    leaf4598InputLogOnePlusV = outerEnclosure 24
      (leaf4598Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4598RoundedFacts : LeafRoundedFacts 8
    leaf4598Certificate.logOnePlusV leaf4598InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4598InputLogOnePlusV_eq }

private noncomputable def leaf4598Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi294InputQChi innerPair117Input
    leaf4598InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4598LowerChecked :
    lowerCheck 24 leaf4598Box leaf4598Inputs = true := by
  rfl'

private theorem leaf4598CoversExact : CoversExact 8
    leaf4598Box leaf4598Certificate leaf4598InnerLog leaf4598Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi294RoundedFacts
    innerPair117RoundedFacts leaf4598RoundedFacts (by rfl)

private theorem leaf4598FlatSound : Sound leaf4598Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4598CertificateValid
    leaf4598InnerLogValid leaf4598CoversExact leaf4598LowerChecked

private noncomputable def leaf4599Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (21/64), chiHi := (85/256) }

private noncomputable def leaf4599Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871289/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357475328) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1103820633/1073741824) }, upper := { exponent := 1, mantissa := (2129/2048) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi293LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716197887/68714950656) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf4599InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf4599LocalValidity :
    LeafFacts leaf4599Box leaf4599Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4599Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357475328) }) = true
      norm_num [leaf4599Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4599CertificateValid :
    WideCertificateValid leaf4599Box leaf4599Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi293ValidityFacts
    leaf4599LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4599CoverageChecked :
    coverageCheck (innerAD leaf4599Box) leaf4599InnerLog = true := by
  rfl'

private theorem leaf4599InnerLogValid :
    leaf4599InnerLog.Valid 8 (innerAD leaf4599Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf4599CoverageChecked

private noncomputable def leaf4599InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629385/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4599InputLogOnePlusV_eq :
    leaf4599InputLogOnePlusV = outerEnclosure 24
      (leaf4599Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4599RoundedFacts : LeafRoundedFacts 8
    leaf4599Certificate.logOnePlusV leaf4599InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4599InputLogOnePlusV_eq }

private noncomputable def leaf4599Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi293InputQChi innerPair117Input
    leaf4599InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4599LowerChecked :
    lowerCheck 24 leaf4599Box leaf4599Inputs = true := by
  rfl'

private theorem leaf4599CoversExact : CoversExact 8
    leaf4599Box leaf4599Certificate leaf4599InnerLog leaf4599Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi293RoundedFacts
    innerPair117RoundedFacts leaf4599RoundedFacts (by rfl)

private theorem leaf4599FlatSound : Sound leaf4599Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4599CertificateValid
    leaf4599InnerLogValid leaf4599CoversExact leaf4599LowerChecked

private noncomputable def leaf4600Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (85/256), chiHi := (43/128) }

private noncomputable def leaf4600Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871291/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357448704) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1110570427/1073741824) }, upper := { exponent := 1, mantissa := (1071/1024) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi294LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716171263/68714897408) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf4600InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4600LocalValidity :
    LeafFacts leaf4600Box leaf4600Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4600Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357448704) }) = true
      norm_num [leaf4600Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4600CertificateValid :
    WideCertificateValid leaf4600Box leaf4600Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi294ValidityFacts
    leaf4600LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4600CoverageChecked :
    coverageCheck (innerAD leaf4600Box) leaf4600InnerLog = true := by
  rfl'

private theorem leaf4600InnerLogValid :
    leaf4600InnerLog.Valid 8 (innerAD leaf4600Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4600CoverageChecked

private noncomputable def leaf4600InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (726837/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf4600InputLogOnePlusV_eq :
    leaf4600InputLogOnePlusV = outerEnclosure 24
      (leaf4600Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4600RoundedFacts : LeafRoundedFacts 8
    leaf4600Certificate.logOnePlusV leaf4600InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4600InputLogOnePlusV_eq }

private noncomputable def leaf4600Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi294InputQChi innerPair242Input
    leaf4600InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4600LowerChecked :
    lowerCheck 24 leaf4600Box leaf4600Inputs = true := by
  rfl'

private theorem leaf4600CoversExact : CoversExact 8
    leaf4600Box leaf4600Certificate leaf4600InnerLog leaf4600Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi294RoundedFacts
    innerPair242RoundedFacts leaf4600RoundedFacts (by rfl)

private theorem leaf4600FlatSound : Sound leaf4600Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4600CertificateValid
    leaf4600InnerLogValid leaf4600CoversExact leaf4600LowerChecked

private noncomputable def leaf4601Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (43/128), chiHi := (11/32) }

private noncomputable def leaf4601Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435749/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357417984) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (555825749/536870912) }, upper := { exponent := 1, mantissa := (2157/2048) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi252LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716140543/68714835968) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf4601InnerLog : WideLogData :=
  innerPair247Data

set_option maxRecDepth 1000000 in
private theorem leaf4601LocalValidity :
    LeafFacts leaf4601Box leaf4601Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4601Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357417984) }) = true
      norm_num [leaf4601Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4601CertificateValid :
    WideCertificateValid leaf4601Box leaf4601Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi252ValidityFacts
    leaf4601LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4601CoverageChecked :
    coverageCheck (innerAD leaf4601Box) leaf4601InnerLog = true := by
  rfl'

private theorem leaf4601InnerLogValid :
    leaf4601InnerLog.Valid 8 (innerAD leaf4601Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint89PositiveFacts.valid leaf4601CoverageChecked

private noncomputable def leaf4601InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629399/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4601InputLogOnePlusV_eq :
    leaf4601InputLogOnePlusV = outerEnclosure 24
      (leaf4601Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4601RoundedFacts : LeafRoundedFacts 8
    leaf4601Certificate.logOnePlusV leaf4601InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4601InputLogOnePlusV_eq }

private noncomputable def leaf4601Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi252InputQChi innerPair247Input
    leaf4601InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4601LowerChecked :
    lowerCheck 24 leaf4601Box leaf4601Inputs = true := by
  rfl'

private theorem leaf4601CoversExact : CoversExact 8
    leaf4601Box leaf4601Certificate leaf4601InnerLog leaf4601Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi252RoundedFacts
    innerPair247RoundedFacts leaf4601RoundedFacts (by rfl)

private theorem leaf4601FlatSound : Sound leaf4601Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4601CertificateValid
    leaf4601InnerLogValid leaf4601CoversExact leaf4601LowerChecked

private noncomputable def leaf4602Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (43/128), chiHi := (11/32) }

private noncomputable def leaf4602Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435751/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357395456) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (558643623/536870912) }, upper := { exponent := 1, mantissa := (271/256) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi252LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716118015/68714790912) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf4602InnerLog : WideLogData :=
  innerPair325Data

set_option maxRecDepth 1000000 in
private theorem leaf4602LocalValidity :
    LeafFacts leaf4602Box leaf4602Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4602Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357395456) }) = true
      norm_num [leaf4602Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4602CertificateValid :
    WideCertificateValid leaf4602Box leaf4602Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi252ValidityFacts
    leaf4602LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4602CoverageChecked :
    coverageCheck (innerAD leaf4602Box) leaf4602InnerLog = true := by
  rfl'

private theorem leaf4602InnerLogValid :
    leaf4602InnerLog.Valid 8 (innerAD leaf4602Box) :=
  wideLogDataValid_of_cachedCheck endpoint86PositiveFacts
    endpoint334PositiveFacts.valid leaf4602CoverageChecked

private noncomputable def leaf4602InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629405/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4602InputLogOnePlusV_eq :
    leaf4602InputLogOnePlusV = outerEnclosure 24
      (leaf4602Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4602RoundedFacts : LeafRoundedFacts 8
    leaf4602Certificate.logOnePlusV leaf4602InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4602InputLogOnePlusV_eq }

private noncomputable def leaf4602Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi252InputQChi innerPair325Input
    leaf4602InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4602LowerChecked :
    lowerCheck 24 leaf4602Box leaf4602Inputs = true := by
  rfl'

private theorem leaf4602CoversExact : CoversExact 8
    leaf4602Box leaf4602Certificate leaf4602InnerLog leaf4602Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi252RoundedFacts
    innerPair325RoundedFacts leaf4602RoundedFacts (by rfl)

private theorem leaf4602FlatSound : Sound leaf4602Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4602CertificateValid
    leaf4602InnerLogValid leaf4602CoversExact leaf4602LowerChecked

private noncomputable def component94Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (5/16), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component94Node0_sound : Sound component94Node0Box :=
  sound_of_literal_split component94Node0Box leaf4562Box leaf4563Box
    .k (97/32) (by rfl) (by rfl)
    leaf4562FlatSound leaf4563FlatSound

private noncomputable def component94Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (41/128), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component94Node1_sound : Sound component94Node1Box :=
  sound_of_literal_split component94Node1Box leaf4564Box leaf4565Box
    .k (97/32) (by rfl) (by rfl)
    leaf4564FlatSound leaf4565FlatSound

private noncomputable def component94Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (5/16), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component94Node2_sound : Sound component94Node2Box :=
  sound_of_literal_split component94Node2Box component94Node0Box component94Node1Box
    .chi (41/128) (by rfl) (by rfl)
    component94Node0_sound component94Node1_sound

private noncomputable def component94Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (5/16), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component94Node3_sound : Sound component94Node3Box :=
  sound_of_literal_split component94Node3Box leaf4566Box leaf4567Box
    .k (99/32) (by rfl) (by rfl)
    leaf4566FlatSound leaf4567FlatSound

private noncomputable def component94Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (41/128), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component94Node4_sound : Sound component94Node4Box :=
  sound_of_literal_split component94Node4Box leaf4568Box leaf4569Box
    .k (99/32) (by rfl) (by rfl)
    leaf4568FlatSound leaf4569FlatSound

private noncomputable def component94Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (5/16), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component94Node5_sound : Sound component94Node5Box :=
  sound_of_literal_split component94Node5Box component94Node3Box component94Node4Box
    .chi (41/128) (by rfl) (by rfl)
    component94Node3_sound component94Node4_sound

private noncomputable def component94Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (5/16), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component94Node6_sound : Sound component94Node6Box :=
  sound_of_literal_split component94Node6Box component94Node2Box component94Node5Box
    .k (49/16) (by rfl) (by rfl)
    component94Node2_sound component94Node5_sound

private noncomputable def component94Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (21/64), chiHi := (43/128) }

set_option maxRecDepth 1000000 in
private theorem component94Node7_sound : Sound component94Node7Box :=
  sound_of_literal_split component94Node7Box leaf4570Box leaf4571Box
    .k (97/32) (by rfl) (by rfl)
    leaf4570FlatSound leaf4571FlatSound

private noncomputable def component94Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (43/128), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component94Node8_sound : Sound component94Node8Box :=
  sound_of_literal_split component94Node8Box leaf4572Box leaf4573Box
    .k (97/32) (by rfl) (by rfl)
    leaf4572FlatSound leaf4573FlatSound

private noncomputable def component94Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (21/64), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component94Node9_sound : Sound component94Node9Box :=
  sound_of_literal_split component94Node9Box component94Node7Box component94Node8Box
    .chi (43/128) (by rfl) (by rfl)
    component94Node7_sound component94Node8_sound

private noncomputable def component94Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (21/64), chiHi := (43/128) }

set_option maxRecDepth 1000000 in
private theorem component94Node10_sound : Sound component94Node10Box :=
  sound_of_literal_split component94Node10Box leaf4574Box leaf4575Box
    .k (99/32) (by rfl) (by rfl)
    leaf4574FlatSound leaf4575FlatSound

private noncomputable def component94Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (43/128), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component94Node11_sound : Sound component94Node11Box :=
  sound_of_literal_split component94Node11Box leaf4576Box leaf4577Box
    .k (99/32) (by rfl) (by rfl)
    leaf4576FlatSound leaf4577FlatSound

private noncomputable def component94Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (21/64), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component94Node12_sound : Sound component94Node12Box :=
  sound_of_literal_split component94Node12Box component94Node10Box component94Node11Box
    .chi (43/128) (by rfl) (by rfl)
    component94Node10_sound component94Node11_sound

private noncomputable def component94Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (21/64), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component94Node13_sound : Sound component94Node13Box :=
  sound_of_literal_split component94Node13Box component94Node9Box component94Node12Box
    .k (49/16) (by rfl) (by rfl)
    component94Node9_sound component94Node12_sound

private noncomputable def component94Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (5/16), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component94Node14_sound : Sound component94Node14Box :=
  sound_of_literal_split component94Node14Box component94Node6Box component94Node13Box
    .chi (21/64) (by rfl) (by rfl)
    component94Node6_sound component94Node13_sound

private noncomputable def component94Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (5/16), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component94Node15_sound : Sound component94Node15Box :=
  sound_of_literal_split component94Node15Box leaf4578Box leaf4579Box
    .chi (81/256) (by rfl) (by rfl)
    leaf4578FlatSound leaf4579FlatSound

private noncomputable def component94Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (5/16), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component94Node16_sound : Sound component94Node16Box :=
  sound_of_literal_split component94Node16Box leaf4580Box leaf4581Box
    .chi (81/256) (by rfl) (by rfl)
    leaf4580FlatSound leaf4581FlatSound

private noncomputable def component94Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (5/16), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component94Node17_sound : Sound component94Node17Box :=
  sound_of_literal_split component94Node17Box component94Node15Box component94Node16Box
    .k (101/32) (by rfl) (by rfl)
    component94Node15_sound component94Node16_sound

private noncomputable def component94Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (41/128), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component94Node18_sound : Sound component94Node18Box :=
  sound_of_literal_split component94Node18Box leaf4583Box leaf4584Box
    .chi (83/256) (by rfl) (by rfl)
    leaf4583FlatSound leaf4584FlatSound

private noncomputable def component94Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (41/128), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component94Node19_sound : Sound component94Node19Box :=
  sound_of_literal_split component94Node19Box leaf4582Box component94Node18Box
    .k (101/32) (by rfl) (by rfl)
    leaf4582FlatSound component94Node18_sound

private noncomputable def component94Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (5/16), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component94Node20_sound : Sound component94Node20Box :=
  sound_of_literal_split component94Node20Box component94Node17Box component94Node19Box
    .chi (41/128) (by rfl) (by rfl)
    component94Node17_sound component94Node19_sound

private noncomputable def component94Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (5/16), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component94Node21_sound : Sound component94Node21Box :=
  sound_of_literal_split component94Node21Box leaf4585Box leaf4586Box
    .chi (81/256) (by rfl) (by rfl)
    leaf4585FlatSound leaf4586FlatSound

private noncomputable def component94Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (5/16), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component94Node22_sound : Sound component94Node22Box :=
  sound_of_literal_split component94Node22Box leaf4587Box leaf4588Box
    .chi (81/256) (by rfl) (by rfl)
    leaf4587FlatSound leaf4588FlatSound

private noncomputable def component94Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (5/16), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component94Node23_sound : Sound component94Node23Box :=
  sound_of_literal_split component94Node23Box component94Node21Box component94Node22Box
    .k (103/32) (by rfl) (by rfl)
    component94Node21_sound component94Node22_sound

private noncomputable def component94Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (41/128), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component94Node24_sound : Sound component94Node24Box :=
  sound_of_literal_split component94Node24Box leaf4589Box leaf4590Box
    .chi (83/256) (by rfl) (by rfl)
    leaf4589FlatSound leaf4590FlatSound

private noncomputable def component94Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (41/128), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component94Node25_sound : Sound component94Node25Box :=
  sound_of_literal_split component94Node25Box leaf4591Box leaf4592Box
    .chi (83/256) (by rfl) (by rfl)
    leaf4591FlatSound leaf4592FlatSound

private noncomputable def component94Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (41/128), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component94Node26_sound : Sound component94Node26Box :=
  sound_of_literal_split component94Node26Box component94Node24Box component94Node25Box
    .k (103/32) (by rfl) (by rfl)
    component94Node24_sound component94Node25_sound

private noncomputable def component94Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (5/16), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component94Node27_sound : Sound component94Node27Box :=
  sound_of_literal_split component94Node27Box component94Node23Box component94Node26Box
    .chi (41/128) (by rfl) (by rfl)
    component94Node23_sound component94Node26_sound

private noncomputable def component94Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (5/16), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component94Node28_sound : Sound component94Node28Box :=
  sound_of_literal_split component94Node28Box component94Node20Box component94Node27Box
    .k (51/16) (by rfl) (by rfl)
    component94Node20_sound component94Node27_sound

private noncomputable def component94Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (21/64), chiHi := (43/128) }

set_option maxRecDepth 1000000 in
private theorem component94Node29_sound : Sound component94Node29Box :=
  sound_of_literal_split component94Node29Box leaf4593Box leaf4594Box
    .k (101/32) (by rfl) (by rfl)
    leaf4593FlatSound leaf4594FlatSound

private noncomputable def component94Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (43/128), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component94Node30_sound : Sound component94Node30Box :=
  sound_of_literal_split component94Node30Box leaf4595Box leaf4596Box
    .k (101/32) (by rfl) (by rfl)
    leaf4595FlatSound leaf4596FlatSound

private noncomputable def component94Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (21/64), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component94Node31_sound : Sound component94Node31Box :=
  sound_of_literal_split component94Node31Box component94Node29Box component94Node30Box
    .chi (43/128) (by rfl) (by rfl)
    component94Node29_sound component94Node30_sound

private noncomputable def component94Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (21/64), chiHi := (43/128) }

set_option maxRecDepth 1000000 in
private theorem component94Node32_sound : Sound component94Node32Box :=
  sound_of_literal_split component94Node32Box leaf4597Box leaf4598Box
    .chi (85/256) (by rfl) (by rfl)
    leaf4597FlatSound leaf4598FlatSound

private noncomputable def component94Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (21/64), chiHi := (43/128) }

set_option maxRecDepth 1000000 in
private theorem component94Node33_sound : Sound component94Node33Box :=
  sound_of_literal_split component94Node33Box leaf4599Box leaf4600Box
    .chi (85/256) (by rfl) (by rfl)
    leaf4599FlatSound leaf4600FlatSound

private noncomputable def component94Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (21/64), chiHi := (43/128) }

set_option maxRecDepth 1000000 in
private theorem component94Node34_sound : Sound component94Node34Box :=
  sound_of_literal_split component94Node34Box component94Node32Box component94Node33Box
    .k (103/32) (by rfl) (by rfl)
    component94Node32_sound component94Node33_sound

private noncomputable def component94Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (43/128), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component94Node35_sound : Sound component94Node35Box :=
  sound_of_literal_split component94Node35Box leaf4601Box leaf4602Box
    .k (103/32) (by rfl) (by rfl)
    leaf4601FlatSound leaf4602FlatSound

private noncomputable def component94Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (21/64), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component94Node36_sound : Sound component94Node36Box :=
  sound_of_literal_split component94Node36Box component94Node34Box component94Node35Box
    .chi (43/128) (by rfl) (by rfl)
    component94Node34_sound component94Node35_sound

private noncomputable def component94Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (21/64), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component94Node37_sound : Sound component94Node37Box :=
  sound_of_literal_split component94Node37Box component94Node31Box component94Node36Box
    .k (51/16) (by rfl) (by rfl)
    component94Node31_sound component94Node36_sound

private noncomputable def component94Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (5/16), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component94Node38_sound : Sound component94Node38Box :=
  sound_of_literal_split component94Node38Box component94Node28Box component94Node37Box
    .chi (21/64) (by rfl) (by rfl)
    component94Node28_sound component94Node37_sound

noncomputable def component94Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (13/4), chiLo := (5/16), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
theorem component94_sound : Sound component94Box :=
  sound_of_literal_split component94Box component94Node14Box component94Node38Box
    .k (25/8) (by rfl) (by rfl)
    component94Node14_sound component94Node38_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
