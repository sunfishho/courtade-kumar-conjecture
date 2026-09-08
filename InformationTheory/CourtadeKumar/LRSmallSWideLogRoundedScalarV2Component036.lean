import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch6
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

private noncomputable def leaf1565Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (0), chiHi := (1/128) }

private noncomputable def leaf1565Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108923/67108864) }, vSqrt := { lower := (8191/8192), upper := (16777280/16777187) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := -1, mantissa := (67076039/33554432) }, upper := { exponent := 0, mantissa := (1053/1024) } }, logOuter := sk149LogOuterCertificate, logK := sk149LogKCertificate, logChi := chi137LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (33554467/33554374) } }, logDArg := sk149LogDArgCertificate }

private noncomputable def leaf1565InnerLog : WideLogData :=
  innerPair1Data

set_option maxRecDepth 1000000 in
private theorem leaf1565LocalValidity :
    LeafFacts leaf1565Box leaf1565Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1565Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (16777280/16777187) }) = true
      norm_num [leaf1565Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1565CertificateValid :
    WideCertificateValid leaf1565Box leaf1565Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk149ValidityFacts chi137ValidityFacts
    leaf1565LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1565CoverageChecked :
    coverageCheck (innerAD leaf1565Box) leaf1565InnerLog = true := by
  rfl'

private theorem leaf1565InnerLogValid :
    leaf1565InnerLog.Valid 8 (innerAD leaf1565Box) :=
  wideLogDataValid_of_cachedCheck endpoint0PositiveFacts
    endpoint2PositiveFacts.valid leaf1565CoverageChecked

private noncomputable def leaf1565InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629127/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1565InputLogOnePlusV_eq :
    leaf1565InputLogOnePlusV = outerEnclosure 24
      (leaf1565Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1565RoundedFacts : LeafRoundedFacts 8
    leaf1565Certificate.logOnePlusV leaf1565InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1565InputLogOnePlusV_eq }

private noncomputable def leaf1565Inputs : Inputs :=
  inputsOfCaches globalInput sk149RoundedInputs
    chi137InputQChi innerPair1Input
    leaf1565InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1565LowerChecked :
    lowerCheck 24 leaf1565Box leaf1565Inputs = true := by
  rfl'

private theorem leaf1565CoversExact : CoversExact 8
    leaf1565Box leaf1565Certificate leaf1565InnerLog leaf1565Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk149RoundedFacts chi137RoundedFacts
    innerPair1RoundedFacts leaf1565RoundedFacts (by rfl)

private theorem leaf1565FlatSound : Sound leaf1565Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1565CertificateValid
    leaf1565InnerLogValid leaf1565CoversExact leaf1565LowerChecked

private noncomputable def leaf1566Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (0), chiHi := (1/128) }

private noncomputable def leaf1566Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108925/67108864) }, vSqrt := { lower := (8191/8192), upper := (8388640/8388593) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := -1, mantissa := (67076037/33554432) }, upper := { exponent := 0, mantissa := (527/512) } }, logOuter := sk150LogOuterCertificate, logK := sk150LogKCertificate, logChi := chi137LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16777233/16777186) } }, logDArg := sk150LogDArgCertificate }

private noncomputable def leaf1566InnerLog : WideLogData :=
  innerPair1Data

set_option maxRecDepth 1000000 in
private theorem leaf1566LocalValidity :
    LeafFacts leaf1566Box leaf1566Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1566Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8388640/8388593) }) = true
      norm_num [leaf1566Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1566CertificateValid :
    WideCertificateValid leaf1566Box leaf1566Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk150ValidityFacts chi137ValidityFacts
    leaf1566LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1566CoverageChecked :
    coverageCheck (innerAD leaf1566Box) leaf1566InnerLog = true := by
  rfl'

private theorem leaf1566InnerLogValid :
    leaf1566InnerLog.Valid 8 (innerAD leaf1566Box) :=
  wideLogDataValid_of_cachedCheck endpoint0PositiveFacts
    endpoint2PositiveFacts.valid leaf1566CoverageChecked

private noncomputable def leaf1566InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453641/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1566InputLogOnePlusV_eq :
    leaf1566InputLogOnePlusV = outerEnclosure 24
      (leaf1566Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1566RoundedFacts : LeafRoundedFacts 8
    leaf1566Certificate.logOnePlusV leaf1566InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1566InputLogOnePlusV_eq }

private noncomputable def leaf1566Inputs : Inputs :=
  inputsOfCaches globalInput sk150RoundedInputs
    chi137InputQChi innerPair1Input
    leaf1566InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1566LowerChecked :
    lowerCheck 24 leaf1566Box leaf1566Inputs = true := by
  rfl'

private theorem leaf1566CoversExact : CoversExact 8
    leaf1566Box leaf1566Certificate leaf1566InnerLog leaf1566Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk150RoundedFacts chi137RoundedFacts
    innerPair1RoundedFacts leaf1566RoundedFacts (by rfl)

private theorem leaf1566FlatSound : Sound leaf1566Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1566CertificateValid
    leaf1566InnerLogValid leaf1566CoversExact leaf1566LowerChecked

private noncomputable def leaf1567Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (1/128), chiHi := (1/64) }

private noncomputable def leaf1567Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108925/67108864) }, vSqrt := { lower := (8191/8192), upper := (8388640/8388579) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (68910933/67108864) }, upper := { exponent := 0, mantissa := (541/512) } }, logOuter := sk149LogOuterCertificate, logK := sk149LogKCertificate, logChi := chi138LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16777219/16777158) } }, logDArg := sk149LogDArgCertificate }

private noncomputable def leaf1567InnerLog : WideLogData :=
  innerPair10Data

set_option maxRecDepth 1000000 in
private theorem leaf1567LocalValidity :
    LeafFacts leaf1567Box leaf1567Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1567Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8388640/8388579) }) = true
      norm_num [leaf1567Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1567CertificateValid :
    WideCertificateValid leaf1567Box leaf1567Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk149ValidityFacts chi138ValidityFacts
    leaf1567LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1567CoverageChecked :
    coverageCheck (innerAD leaf1567Box) leaf1567InnerLog = true := by
  rfl'

private theorem leaf1567InnerLogValid :
    leaf1567InnerLog.Valid 8 (innerAD leaf1567Box) :=
  wideLogDataValid_of_cachedCheck endpoint3PositiveFacts
    endpoint2PositiveFacts.valid leaf1567CoverageChecked

private noncomputable def leaf1567InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814571/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1567InputLogOnePlusV_eq :
    leaf1567InputLogOnePlusV = outerEnclosure 24
      (leaf1567Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1567RoundedFacts : LeafRoundedFacts 8
    leaf1567Certificate.logOnePlusV leaf1567InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1567InputLogOnePlusV_eq }

private noncomputable def leaf1567Inputs : Inputs :=
  inputsOfCaches globalInput sk149RoundedInputs
    chi138InputQChi innerPair10Input
    leaf1567InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1567LowerChecked :
    lowerCheck 24 leaf1567Box leaf1567Inputs = true := by
  rfl'

private theorem leaf1567CoversExact : CoversExact 8
    leaf1567Box leaf1567Certificate leaf1567InnerLog leaf1567Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk149RoundedFacts chi138RoundedFacts
    innerPair10RoundedFacts leaf1567RoundedFacts (by rfl)

private theorem leaf1567FlatSound : Sound leaf1567Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1567CertificateValid
    leaf1567InnerLogValid leaf1567CoversExact leaf1567LowerChecked

private noncomputable def leaf1568Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (1/128), chiHi := (1/64) }

private noncomputable def leaf1568Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108927/67108864) }, vSqrt := { lower := (8191/8192), upper := (4194320/4194289) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (68976463/67108864) }, upper := { exponent := 0, mantissa := (271/256) } }, logOuter := sk150LogOuterCertificate, logK := sk150LogKCertificate, logChi := chi138LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (8388609/8388578) } }, logDArg := sk150LogDArgCertificate }

private noncomputable def leaf1568InnerLog : WideLogData :=
  innerPair10Data

set_option maxRecDepth 1000000 in
private theorem leaf1568LocalValidity :
    LeafFacts leaf1568Box leaf1568Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1568Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4194320/4194289) }) = true
      norm_num [leaf1568Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1568CertificateValid :
    WideCertificateValid leaf1568Box leaf1568Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk150ValidityFacts chi138ValidityFacts
    leaf1568LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1568CoverageChecked :
    coverageCheck (innerAD leaf1568Box) leaf1568InnerLog = true := by
  rfl'

private theorem leaf1568InnerLogValid :
    leaf1568InnerLog.Valid 8 (innerAD leaf1568Box) :=
  wideLogDataValid_of_cachedCheck endpoint3PositiveFacts
    endpoint2PositiveFacts.valid leaf1568CoverageChecked

private noncomputable def leaf1568InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629143/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1568InputLogOnePlusV_eq :
    leaf1568InputLogOnePlusV = outerEnclosure 24
      (leaf1568Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1568RoundedFacts : LeafRoundedFacts 8
    leaf1568Certificate.logOnePlusV leaf1568InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1568InputLogOnePlusV_eq }

private noncomputable def leaf1568Inputs : Inputs :=
  inputsOfCaches globalInput sk150RoundedInputs
    chi138InputQChi innerPair10Input
    leaf1568InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1568LowerChecked :
    lowerCheck 24 leaf1568Box leaf1568Inputs = true := by
  rfl'

private theorem leaf1568CoversExact : CoversExact 8
    leaf1568Box leaf1568Certificate leaf1568InnerLog leaf1568Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk150RoundedFacts chi138RoundedFacts
    innerPair10RoundedFacts leaf1568RoundedFacts (by rfl)

private theorem leaf1568FlatSound : Sound leaf1568Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1568CertificateValid
    leaf1568InnerLogValid leaf1568CoversExact leaf1568LowerChecked

private noncomputable def leaf1569Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (1/64), chiHi := (5/256) }

private noncomputable def leaf1569Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217795/134217728) }, vSqrt := { lower := (8191/8192), upper := (2581120/2581099) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (141524479/134217728) }, upper := { exponent := 0, mantissa := (2193/2048) } }, logOuter := sk149LogOuterCertificate, logK := sk149LogKCertificate, logChi := chi141LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (5162219/5162198) } }, logDArg := sk149LogDArgCertificate }

private noncomputable def leaf1569InnerLog : WideLogData :=
  innerPair9Data

set_option maxRecDepth 1000000 in
private theorem leaf1569LocalValidity :
    LeafFacts leaf1569Box leaf1569Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1569Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (2581120/2581099) }) = true
      norm_num [leaf1569Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1569CertificateValid :
    WideCertificateValid leaf1569Box leaf1569Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk149ValidityFacts chi141ValidityFacts
    leaf1569LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1569CoverageChecked :
    coverageCheck (innerAD leaf1569Box) leaf1569InnerLog = true := by
  rfl'

private theorem leaf1569InnerLogValid :
    leaf1569InnerLog.Valid 8 (innerAD leaf1569Box) :=
  wideLogDataValid_of_cachedCheck endpoint3PositiveFacts
    endpoint1PositiveFacts.valid leaf1569CoverageChecked

private noncomputable def leaf1569InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629149/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1569InputLogOnePlusV_eq :
    leaf1569InputLogOnePlusV = outerEnclosure 24
      (leaf1569Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1569RoundedFacts : LeafRoundedFacts 8
    leaf1569Certificate.logOnePlusV leaf1569InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1569InputLogOnePlusV_eq }

private noncomputable def leaf1569Inputs : Inputs :=
  inputsOfCaches globalInput sk149RoundedInputs
    chi141InputQChi innerPair9Input
    leaf1569InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1569LowerChecked :
    lowerCheck 24 leaf1569Box leaf1569Inputs = true := by
  rfl'

private theorem leaf1569CoversExact : CoversExact 8
    leaf1569Box leaf1569Certificate leaf1569InnerLog leaf1569Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk149RoundedFacts chi141RoundedFacts
    innerPair9RoundedFacts leaf1569RoundedFacts (by rfl)

private theorem leaf1569FlatSound : Sound leaf1569Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1569CertificateValid
    leaf1569InnerLogValid leaf1569CoversExact leaf1569LowerChecked

private noncomputable def leaf1570Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (5/256), chiHi := (3/128) }

private noncomputable def leaf1570Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217797/134217728) }, vSqrt := { lower := (8191/8192), upper := (16777280/16777129) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (143359373/134217728) }, upper := { exponent := 0, mantissa := (1111/1024) } }, logOuter := sk149LogOuterCertificate, logK := sk149LogKCertificate, logChi := chi142LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (33554409/33554258) } }, logDArg := sk149LogDArgCertificate }

private noncomputable def leaf1570InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf1570LocalValidity :
    LeafFacts leaf1570Box leaf1570Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1570Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (16777280/16777129) }) = true
      norm_num [leaf1570Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1570CertificateValid :
    WideCertificateValid leaf1570Box leaf1570Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk149ValidityFacts chi142ValidityFacts
    leaf1570LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1570CoverageChecked :
    coverageCheck (innerAD leaf1570Box) leaf1570InnerLog = true := by
  rfl'

private theorem leaf1570InnerLogValid :
    leaf1570InnerLog.Valid 8 (innerAD leaf1570Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf1570CoverageChecked

private noncomputable def leaf1570InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907289/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1570InputLogOnePlusV_eq :
    leaf1570InputLogOnePlusV = outerEnclosure 24
      (leaf1570Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1570RoundedFacts : LeafRoundedFacts 8
    leaf1570Certificate.logOnePlusV leaf1570InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1570InputLogOnePlusV_eq }

private noncomputable def leaf1570Inputs : Inputs :=
  inputsOfCaches globalInput sk149RoundedInputs
    chi142InputQChi innerPair5Input
    leaf1570InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1570LowerChecked :
    lowerCheck 24 leaf1570Box leaf1570Inputs = true := by
  rfl'

private theorem leaf1570CoversExact : CoversExact 8
    leaf1570Box leaf1570Certificate leaf1570InnerLog leaf1570Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk149RoundedFacts chi142RoundedFacts
    innerPair5RoundedFacts leaf1570RoundedFacts (by rfl)

private theorem leaf1570FlatSound : Sound leaf1570Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1570CertificateValid
    leaf1570InnerLogValid leaf1570CoversExact leaf1570LowerChecked

private noncomputable def leaf1571Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (1/64), chiHi := (5/256) }

private noncomputable def leaf1571Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217797/134217728) }, vSqrt := { lower := (8191/8192), upper := (16777280/16777141) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (141786605/134217728) }, upper := { exponent := 0, mantissa := (1099/1024) } }, logOuter := sk150LogOuterCertificate, logK := sk150LogKCertificate, logChi := chi141LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (33554421/33554282) } }, logDArg := sk150LogDArgCertificate }

private noncomputable def leaf1571InnerLog : WideLogData :=
  innerPair9Data

set_option maxRecDepth 1000000 in
private theorem leaf1571LocalValidity :
    LeafFacts leaf1571Box leaf1571Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1571Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (16777280/16777141) }) = true
      norm_num [leaf1571Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1571CertificateValid :
    WideCertificateValid leaf1571Box leaf1571Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk150ValidityFacts chi141ValidityFacts
    leaf1571LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1571CoverageChecked :
    coverageCheck (innerAD leaf1571Box) leaf1571InnerLog = true := by
  rfl'

private theorem leaf1571InnerLogValid :
    leaf1571InnerLog.Valid 8 (innerAD leaf1571Box) :=
  wideLogDataValid_of_cachedCheck endpoint3PositiveFacts
    endpoint1PositiveFacts.valid leaf1571CoverageChecked

private noncomputable def leaf1571InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814575/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1571InputLogOnePlusV_eq :
    leaf1571InputLogOnePlusV = outerEnclosure 24
      (leaf1571Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1571RoundedFacts : LeafRoundedFacts 8
    leaf1571Certificate.logOnePlusV leaf1571InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1571InputLogOnePlusV_eq }

private noncomputable def leaf1571Inputs : Inputs :=
  inputsOfCaches globalInput sk150RoundedInputs
    chi141InputQChi innerPair9Input
    leaf1571InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1571LowerChecked :
    lowerCheck 24 leaf1571Box leaf1571Inputs = true := by
  rfl'

private theorem leaf1571CoversExact : CoversExact 8
    leaf1571Box leaf1571Certificate leaf1571InnerLog leaf1571Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk150RoundedFacts chi141RoundedFacts
    innerPair9RoundedFacts leaf1571RoundedFacts (by rfl)

private theorem leaf1571FlatSound : Sound leaf1571Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1571CertificateValid
    leaf1571InnerLogValid leaf1571CoversExact leaf1571LowerChecked

private noncomputable def leaf1572Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (5/256), chiHi := (3/128) }

private noncomputable def leaf1572Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217799/134217728) }, vSqrt := { lower := (8191/8192), upper := (8388640/8388563) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (143687031/134217728) }, upper := { exponent := 0, mantissa := (557/512) } }, logOuter := sk150LogOuterCertificate, logK := sk150LogKCertificate, logChi := chi142LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16777203/16777126) } }, logDArg := sk150LogDArgCertificate }

private noncomputable def leaf1572InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf1572LocalValidity :
    LeafFacts leaf1572Box leaf1572Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1572Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8388640/8388563) }) = true
      norm_num [leaf1572Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1572CertificateValid :
    WideCertificateValid leaf1572Box leaf1572Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk150ValidityFacts chi142ValidityFacts
    leaf1572LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1572CoverageChecked :
    coverageCheck (innerAD leaf1572Box) leaf1572InnerLog = true := by
  rfl'

private theorem leaf1572InnerLogValid :
    leaf1572InnerLog.Valid 8 (innerAD leaf1572Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf1572CoverageChecked

private noncomputable def leaf1572InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814579/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1572InputLogOnePlusV_eq :
    leaf1572InputLogOnePlusV = outerEnclosure 24
      (leaf1572Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1572RoundedFacts : LeafRoundedFacts 8
    leaf1572Certificate.logOnePlusV leaf1572InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1572InputLogOnePlusV_eq }

private noncomputable def leaf1572Inputs : Inputs :=
  inputsOfCaches globalInput sk150RoundedInputs
    chi142InputQChi innerPair5Input
    leaf1572InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1572LowerChecked :
    lowerCheck 24 leaf1572Box leaf1572Inputs = true := by
  rfl'

private theorem leaf1572CoversExact : CoversExact 8
    leaf1572Box leaf1572Certificate leaf1572InnerLog leaf1572Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk150RoundedFacts chi142RoundedFacts
    innerPair5RoundedFacts leaf1572RoundedFacts (by rfl)

private theorem leaf1572FlatSound : Sound leaf1572Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1572CertificateValid
    leaf1572InnerLogValid leaf1572CoversExact leaf1572LowerChecked

private noncomputable def leaf1573Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (3/128), chiHi := (7/256) }

private noncomputable def leaf1573Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217799/134217728) }, vSqrt := { lower := (8191/8192), upper := (33554560/33554229) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (145194267/134217728) }, upper := { exponent := 0, mantissa := (2251/2048) } }, logOuter := sk149LogOuterCertificate, logK := sk149LogKCertificate, logChi := chi123LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67108789/67108458) } }, logDArg := sk149LogDArgCertificate }

private noncomputable def leaf1573InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf1573LocalValidity :
    LeafFacts leaf1573Box leaf1573Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1573Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554560/33554229) }) = true
      norm_num [leaf1573Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1573CertificateValid :
    WideCertificateValid leaf1573Box leaf1573Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk149ValidityFacts chi123ValidityFacts
    leaf1573LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1573CoverageChecked :
    coverageCheck (innerAD leaf1573Box) leaf1573InnerLog = true := by
  rfl'

private theorem leaf1573InnerLogValid :
    leaf1573InnerLog.Valid 8 (innerAD leaf1573Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf1573CoverageChecked

private noncomputable def leaf1573InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629163/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1573InputLogOnePlusV_eq :
    leaf1573InputLogOnePlusV = outerEnclosure 24
      (leaf1573Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1573RoundedFacts : LeafRoundedFacts 8
    leaf1573Certificate.logOnePlusV leaf1573InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1573InputLogOnePlusV_eq }

private noncomputable def leaf1573Inputs : Inputs :=
  inputsOfCaches globalInput sk149RoundedInputs
    chi123InputQChi innerPair5Input
    leaf1573InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1573LowerChecked :
    lowerCheck 24 leaf1573Box leaf1573Inputs = true := by
  rfl'

private theorem leaf1573CoversExact : CoversExact 8
    leaf1573Box leaf1573Certificate leaf1573InnerLog leaf1573Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk149RoundedFacts chi123RoundedFacts
    innerPair5RoundedFacts leaf1573RoundedFacts (by rfl)

private theorem leaf1573FlatSound : Sound leaf1573Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1573CertificateValid
    leaf1573InnerLogValid leaf1573CoversExact leaf1573LowerChecked

private noncomputable def leaf1574Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (7/256), chiHi := (1/32) }

private noncomputable def leaf1574Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435585/268435456) }, vSqrt := { lower := (8191/8192), upper := (8388624/8388551) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (294091105/268435456) }, upper := { exponent := 0, mantissa := (569/512) } }, logOuter := sk151LogOuterCertificate, logK := sk151LogKCertificate, logChi := chi124LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16777175/16777102) } }, logDArg := sk151LogDArgCertificate }

private noncomputable def leaf1574InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf1574LocalValidity :
    LeafFacts leaf1574Box leaf1574Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1574Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8388624/8388551) }) = true
      norm_num [leaf1574Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1574CertificateValid :
    WideCertificateValid leaf1574Box leaf1574Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk151ValidityFacts chi124ValidityFacts
    leaf1574LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1574CoverageChecked :
    coverageCheck (innerAD leaf1574Box) leaf1574InnerLog = true := by
  rfl'

private theorem leaf1574InnerLogValid :
    leaf1574InnerLog.Valid 8 (innerAD leaf1574Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf1574CoverageChecked

private noncomputable def leaf1574InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814577/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1574InputLogOnePlusV_eq :
    leaf1574InputLogOnePlusV = outerEnclosure 24
      (leaf1574Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1574RoundedFacts : LeafRoundedFacts 8
    leaf1574Certificate.logOnePlusV leaf1574InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1574InputLogOnePlusV_eq }

private noncomputable def leaf1574Inputs : Inputs :=
  inputsOfCaches globalInput sk151RoundedInputs
    chi124InputQChi innerPair5Input
    leaf1574InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1574LowerChecked :
    lowerCheck 24 leaf1574Box leaf1574Inputs = true := by
  rfl'

private theorem leaf1574CoversExact : CoversExact 8
    leaf1574Box leaf1574Certificate leaf1574InnerLog leaf1574Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk151RoundedFacts chi124RoundedFacts
    innerPair5RoundedFacts leaf1574RoundedFacts (by rfl)

private theorem leaf1574FlatSound : Sound leaf1574Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1574CertificateValid
    leaf1574InnerLogValid leaf1574CoversExact leaf1574LowerChecked

private noncomputable def leaf1575Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (7/256), chiHi := (1/32) }

private noncomputable def leaf1575Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435587/268435456) }, vSqrt := { lower := (8191/8192), upper := (4194312/4194275) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (294549827/268435456) }, upper := { exponent := 0, mantissa := (285/256) } }, logOuter := sk152LogOuterCertificate, logK := sk152LogKCertificate, logChi := chi124LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (8388587/8388550) } }, logDArg := sk152LogDArgCertificate }

private noncomputable def leaf1575InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf1575LocalValidity :
    LeafFacts leaf1575Box leaf1575Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1575Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4194312/4194275) }) = true
      norm_num [leaf1575Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1575CertificateValid :
    WideCertificateValid leaf1575Box leaf1575Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk152ValidityFacts chi124ValidityFacts
    leaf1575LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1575CoverageChecked :
    coverageCheck (innerAD leaf1575Box) leaf1575InnerLog = true := by
  rfl'

private theorem leaf1575InnerLogValid :
    leaf1575InnerLog.Valid 8 (innerAD leaf1575Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf1575CoverageChecked

private noncomputable def leaf1575InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629155/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1575InputLogOnePlusV_eq :
    leaf1575InputLogOnePlusV = outerEnclosure 24
      (leaf1575Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1575RoundedFacts : LeafRoundedFacts 8
    leaf1575Certificate.logOnePlusV leaf1575InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1575InputLogOnePlusV_eq }

private noncomputable def leaf1575Inputs : Inputs :=
  inputsOfCaches globalInput sk152RoundedInputs
    chi124InputQChi innerPair5Input
    leaf1575InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1575LowerChecked :
    lowerCheck 24 leaf1575Box leaf1575Inputs = true := by
  rfl'

private theorem leaf1575CoversExact : CoversExact 8
    leaf1575Box leaf1575Certificate leaf1575InnerLog leaf1575Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk152RoundedFacts chi124RoundedFacts
    innerPair5RoundedFacts leaf1575RoundedFacts (by rfl)

private theorem leaf1575FlatSound : Sound leaf1575Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1575CertificateValid
    leaf1575InnerLogValid leaf1575CoversExact leaf1575LowerChecked

private noncomputable def leaf1576Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (3/128), chiHi := (7/256) }

private noncomputable def leaf1576Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217801/134217728) }, vSqrt := { lower := (8191/8192), upper := (1290560/1290547) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (145587457/134217728) }, upper := { exponent := 0, mantissa := (1129/1024) } }, logOuter := sk150LogOuterCertificate, logK := sk150LogKCertificate, logChi := chi123LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (2581107/2581094) } }, logDArg := sk150LogDArgCertificate }

private noncomputable def leaf1576InnerLog : WideLogData :=
  innerPair440Data

set_option maxRecDepth 1000000 in
private theorem leaf1576LocalValidity :
    LeafFacts leaf1576Box leaf1576Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1576Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (1290560/1290547) }) = true
      norm_num [leaf1576Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1576CertificateValid :
    WideCertificateValid leaf1576Box leaf1576Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk150ValidityFacts chi123ValidityFacts
    leaf1576LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1576CoverageChecked :
    coverageCheck (innerAD leaf1576Box) leaf1576InnerLog = true := by
  rfl'

private theorem leaf1576InnerLogValid :
    leaf1576InnerLog.Valid 8 (innerAD leaf1576Box) :=
  wideLogDataValid_of_cachedCheck endpoint151PositiveFacts
    endpoint25PositiveFacts.valid leaf1576CoverageChecked

private noncomputable def leaf1576InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629165/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1576InputLogOnePlusV_eq :
    leaf1576InputLogOnePlusV = outerEnclosure 24
      (leaf1576Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1576RoundedFacts : LeafRoundedFacts 8
    leaf1576Certificate.logOnePlusV leaf1576InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1576InputLogOnePlusV_eq }

private noncomputable def leaf1576Inputs : Inputs :=
  inputsOfCaches globalInput sk150RoundedInputs
    chi123InputQChi innerPair440Input
    leaf1576InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1576LowerChecked :
    lowerCheck 24 leaf1576Box leaf1576Inputs = true := by
  rfl'

private theorem leaf1576CoversExact : CoversExact 8
    leaf1576Box leaf1576Certificate leaf1576InnerLog leaf1576Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk150RoundedFacts chi123RoundedFacts
    innerPair440RoundedFacts leaf1576RoundedFacts (by rfl)

private theorem leaf1576FlatSound : Sound leaf1576Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1576CertificateValid
    leaf1576InnerLogValid leaf1576CoversExact leaf1576LowerChecked

private noncomputable def leaf1577Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (7/256), chiHi := (1/32) }

private noncomputable def leaf1577Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435589/268435456) }, vSqrt := { lower := (8191/8192), upper := (2796208/2796183) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (295008549/268435456) }, upper := { exponent := 0, mantissa := (571/512) } }, logOuter := sk153LogOuterCertificate, logK := sk153LogKCertificate, logChi := chi124LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (5592391/5592366) } }, logDArg := sk153LogDArgCertificate }

private noncomputable def leaf1577InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf1577LocalValidity :
    LeafFacts leaf1577Box leaf1577Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1577Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (2796208/2796183) }) = true
      norm_num [leaf1577Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1577CertificateValid :
    WideCertificateValid leaf1577Box leaf1577Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk153ValidityFacts chi124ValidityFacts
    leaf1577LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1577CoverageChecked :
    coverageCheck (innerAD leaf1577Box) leaf1577InnerLog = true := by
  rfl'

private theorem leaf1577InnerLogValid :
    leaf1577InnerLog.Valid 8 (innerAD leaf1577Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf1577CoverageChecked

private noncomputable def leaf1577InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907289/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1577InputLogOnePlusV_eq :
    leaf1577InputLogOnePlusV = outerEnclosure 24
      (leaf1577Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1577RoundedFacts : LeafRoundedFacts 8
    leaf1577Certificate.logOnePlusV leaf1577InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1577InputLogOnePlusV_eq }

private noncomputable def leaf1577Inputs : Inputs :=
  inputsOfCaches globalInput sk153RoundedInputs
    chi124InputQChi innerPair5Input
    leaf1577InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1577LowerChecked :
    lowerCheck 24 leaf1577Box leaf1577Inputs = true := by
  rfl'

private theorem leaf1577CoversExact : CoversExact 8
    leaf1577Box leaf1577Certificate leaf1577InnerLog leaf1577Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk153RoundedFacts chi124RoundedFacts
    innerPair5RoundedFacts leaf1577RoundedFacts (by rfl)

private theorem leaf1577FlatSound : Sound leaf1577Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1577CertificateValid
    leaf1577InnerLogValid leaf1577CoversExact leaf1577LowerChecked

private noncomputable def leaf1578Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (7/256), chiHi := (1/32) }

private noncomputable def leaf1578Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435591/268435456) }, vSqrt := { lower := (8191/8192), upper := (2097156/2097137) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (295467271/268435456) }, upper := { exponent := 0, mantissa := (143/128) } }, logOuter := sk154LogOuterCertificate, logK := sk154LogKCertificate, logChi := chi124LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (4194293/4194274) } }, logDArg := sk154LogDArgCertificate }

private noncomputable def leaf1578InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf1578LocalValidity :
    LeafFacts leaf1578Box leaf1578Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1578Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (2097156/2097137) }) = true
      norm_num [leaf1578Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1578CertificateValid :
    WideCertificateValid leaf1578Box leaf1578Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk154ValidityFacts chi124ValidityFacts
    leaf1578LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1578CoverageChecked :
    coverageCheck (innerAD leaf1578Box) leaf1578InnerLog = true := by
  rfl'

private theorem leaf1578InnerLogValid :
    leaf1578InnerLog.Valid 8 (innerAD leaf1578Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf1578CoverageChecked

private noncomputable def leaf1578InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629157/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1578InputLogOnePlusV_eq :
    leaf1578InputLogOnePlusV = outerEnclosure 24
      (leaf1578Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1578RoundedFacts : LeafRoundedFacts 8
    leaf1578Certificate.logOnePlusV leaf1578InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1578InputLogOnePlusV_eq }

private noncomputable def leaf1578Inputs : Inputs :=
  inputsOfCaches globalInput sk154RoundedInputs
    chi124InputQChi innerPair5Input
    leaf1578InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1578LowerChecked :
    lowerCheck 24 leaf1578Box leaf1578Inputs = true := by
  rfl'

private theorem leaf1578CoversExact : CoversExact 8
    leaf1578Box leaf1578Certificate leaf1578InnerLog leaf1578Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk154RoundedFacts chi124RoundedFacts
    innerPair5RoundedFacts leaf1578RoundedFacts (by rfl)

private theorem leaf1578FlatSound : Sound leaf1578Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1578CertificateValid
    leaf1578InnerLogValid leaf1578CoversExact leaf1578LowerChecked

private noncomputable def leaf1579Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (0), chiHi := (1/128) }

private noncomputable def leaf1579Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108927/67108864) }, vSqrt := { lower := (8191/8192), upper := (3355456/3355437) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := -1, mantissa := (67076035/33554432) }, upper := { exponent := 0, mantissa := (1055/1024) } }, logOuter := sk155LogOuterCertificate, logK := sk155LogKCertificate, logChi := chi137LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (6710893/6710874) } }, logDArg := sk155LogDArgCertificate }

private noncomputable def leaf1579InnerLog : WideLogData :=
  innerPair1Data

set_option maxRecDepth 1000000 in
private theorem leaf1579LocalValidity :
    LeafFacts leaf1579Box leaf1579Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1579Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (3355456/3355437) }) = true
      norm_num [leaf1579Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1579CertificateValid :
    WideCertificateValid leaf1579Box leaf1579Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk155ValidityFacts chi137ValidityFacts
    leaf1579LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1579CoverageChecked :
    coverageCheck (innerAD leaf1579Box) leaf1579InnerLog = true := by
  rfl'

private theorem leaf1579InnerLogValid :
    leaf1579InnerLog.Valid 8 (innerAD leaf1579Box) :=
  wideLogDataValid_of_cachedCheck endpoint0PositiveFacts
    endpoint2PositiveFacts.valid leaf1579CoverageChecked

private noncomputable def leaf1579InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453641/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1579InputLogOnePlusV_eq :
    leaf1579InputLogOnePlusV = outerEnclosure 24
      (leaf1579Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1579RoundedFacts : LeafRoundedFacts 8
    leaf1579Certificate.logOnePlusV leaf1579InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1579InputLogOnePlusV_eq }

private noncomputable def leaf1579Inputs : Inputs :=
  inputsOfCaches globalInput sk155RoundedInputs
    chi137InputQChi innerPair1Input
    leaf1579InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1579LowerChecked :
    lowerCheck 24 leaf1579Box leaf1579Inputs = true := by
  rfl'

private theorem leaf1579CoversExact : CoversExact 8
    leaf1579Box leaf1579Certificate leaf1579InnerLog leaf1579Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk155RoundedFacts chi137RoundedFacts
    innerPair1RoundedFacts leaf1579RoundedFacts (by rfl)

private theorem leaf1579FlatSound : Sound leaf1579Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1579CertificateValid
    leaf1579InnerLogValid leaf1579CoversExact leaf1579LowerChecked

private noncomputable def leaf1580Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (0), chiHi := (1/128) }

private noncomputable def leaf1580Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108929/67108864) }, vSqrt := { lower := (65527/65536), upper := (524290/524287) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := -1, mantissa := (67076033/33554432) }, upper := { exponent := 0, mantissa := (33/32) } }, logOuter := sk156LogOuterCertificate, logK := sk156LogKCertificate, logChi := chi137LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (1048577/1048574) } }, logDArg := sk156LogDArgCertificate }

private noncomputable def leaf1580InnerLog : WideLogData :=
  innerPair1Data

set_option maxRecDepth 1000000 in
private theorem leaf1580LocalValidity :
    LeafFacts leaf1580Box leaf1580Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1580Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (524290/524287) }) = true
      norm_num [leaf1580Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1580CertificateValid :
    WideCertificateValid leaf1580Box leaf1580Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk156ValidityFacts chi137ValidityFacts
    leaf1580LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1580CoverageChecked :
    coverageCheck (innerAD leaf1580Box) leaf1580InnerLog = true := by
  rfl'

private theorem leaf1580InnerLogValid :
    leaf1580InnerLog.Valid 8 (innerAD leaf1580Box) :=
  wideLogDataValid_of_cachedCheck endpoint0PositiveFacts
    endpoint2PositiveFacts.valid leaf1580CoverageChecked

private noncomputable def leaf1580InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629129/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1580InputLogOnePlusV_eq :
    leaf1580InputLogOnePlusV = outerEnclosure 24
      (leaf1580Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1580RoundedFacts : LeafRoundedFacts 8
    leaf1580Certificate.logOnePlusV leaf1580InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1580InputLogOnePlusV_eq }

private noncomputable def leaf1580Inputs : Inputs :=
  inputsOfCaches globalInput sk156RoundedInputs
    chi137InputQChi innerPair1Input
    leaf1580InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1580LowerChecked :
    lowerCheck 24 leaf1580Box leaf1580Inputs = true := by
  rfl'

private theorem leaf1580CoversExact : CoversExact 8
    leaf1580Box leaf1580Certificate leaf1580InnerLog leaf1580Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk156RoundedFacts chi137RoundedFacts
    innerPair1RoundedFacts leaf1580RoundedFacts (by rfl)

private theorem leaf1580FlatSound : Sound leaf1580Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1580CertificateValid
    leaf1580InnerLogValid leaf1580CoversExact leaf1580LowerChecked

private noncomputable def leaf1581Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (1/128), chiHi := (1/64) }

private noncomputable def leaf1581Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108929/67108864) }, vSqrt := { lower := (8191/8192), upper := (8388640/8388577) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (69041993/67108864) }, upper := { exponent := 0, mantissa := (543/512) } }, logOuter := sk155LogOuterCertificate, logK := sk155LogKCertificate, logChi := chi138LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16777217/16777154) } }, logDArg := sk155LogDArgCertificate }

private noncomputable def leaf1581InnerLog : WideLogData :=
  innerPair10Data

set_option maxRecDepth 1000000 in
private theorem leaf1581LocalValidity :
    LeafFacts leaf1581Box leaf1581Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1581Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8388640/8388577) }) = true
      norm_num [leaf1581Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1581CertificateValid :
    WideCertificateValid leaf1581Box leaf1581Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk155ValidityFacts chi138ValidityFacts
    leaf1581LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1581CoverageChecked :
    coverageCheck (innerAD leaf1581Box) leaf1581InnerLog = true := by
  rfl'

private theorem leaf1581InnerLogValid :
    leaf1581InnerLog.Valid 8 (innerAD leaf1581Box) :=
  wideLogDataValid_of_cachedCheck endpoint3PositiveFacts
    endpoint2PositiveFacts.valid leaf1581CoverageChecked

private noncomputable def leaf1581InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453643/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1581InputLogOnePlusV_eq :
    leaf1581InputLogOnePlusV = outerEnclosure 24
      (leaf1581Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1581RoundedFacts : LeafRoundedFacts 8
    leaf1581Certificate.logOnePlusV leaf1581InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1581InputLogOnePlusV_eq }

private noncomputable def leaf1581Inputs : Inputs :=
  inputsOfCaches globalInput sk155RoundedInputs
    chi138InputQChi innerPair10Input
    leaf1581InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1581LowerChecked :
    lowerCheck 24 leaf1581Box leaf1581Inputs = true := by
  rfl'

private theorem leaf1581CoversExact : CoversExact 8
    leaf1581Box leaf1581Certificate leaf1581InnerLog leaf1581Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk155RoundedFacts chi138RoundedFacts
    innerPair10RoundedFacts leaf1581RoundedFacts (by rfl)

private theorem leaf1581FlatSound : Sound leaf1581Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1581CertificateValid
    leaf1581InnerLogValid leaf1581CoversExact leaf1581LowerChecked

private noncomputable def leaf1582Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (1/128), chiHi := (3/256) }

private noncomputable def leaf1582Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217797/134217728) }, vSqrt := { lower := (65527/65536), upper := (1048580/1048573) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (138247877/134217728) }, upper := { exponent := 0, mantissa := (67/64) } }, logOuter := sk156LogOuterCertificate, logK := sk156LogKCertificate, logChi := chi157LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (2097153/2097146) } }, logDArg := sk156LogDArgCertificate }

private noncomputable def leaf1582InnerLog : WideLogData :=
  innerPair10Data

set_option maxRecDepth 1000000 in
private theorem leaf1582LocalValidity :
    LeafFacts leaf1582Box leaf1582Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1582Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (1048580/1048573) }) = true
      norm_num [leaf1582Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1582CertificateValid :
    WideCertificateValid leaf1582Box leaf1582Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk156ValidityFacts chi157ValidityFacts
    leaf1582LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1582CoverageChecked :
    coverageCheck (innerAD leaf1582Box) leaf1582InnerLog = true := by
  rfl'

private theorem leaf1582InnerLogValid :
    leaf1582InnerLog.Valid 8 (innerAD leaf1582Box) :=
  wideLogDataValid_of_cachedCheck endpoint3PositiveFacts
    endpoint2PositiveFacts.valid leaf1582CoverageChecked

private noncomputable def leaf1582InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629137/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1582InputLogOnePlusV_eq :
    leaf1582InputLogOnePlusV = outerEnclosure 24
      (leaf1582Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1582RoundedFacts : LeafRoundedFacts 8
    leaf1582Certificate.logOnePlusV leaf1582InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1582InputLogOnePlusV_eq }

private noncomputable def leaf1582Inputs : Inputs :=
  inputsOfCaches globalInput sk156RoundedInputs
    chi157InputQChi innerPair10Input
    leaf1582InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1582LowerChecked :
    lowerCheck 24 leaf1582Box leaf1582Inputs = true := by
  rfl'

private theorem leaf1582CoversExact : CoversExact 8
    leaf1582Box leaf1582Certificate leaf1582InnerLog leaf1582Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk156RoundedFacts chi157RoundedFacts
    innerPair10RoundedFacts leaf1582RoundedFacts (by rfl)

private theorem leaf1582FlatSound : Sound leaf1582Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1582CertificateValid
    leaf1582InnerLogValid leaf1582CoversExact leaf1582LowerChecked

private noncomputable def leaf1583Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (3/256), chiHi := (1/64) }

private noncomputable def leaf1583Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217799/134217728) }, vSqrt := { lower := (65527/65536), upper := (262145/262143) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (140279367/134217728) }, upper := { exponent := 0, mantissa := (17/16) } }, logOuter := sk156LogOuterCertificate, logK := sk156LogKCertificate, logChi := chi158LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (262144/262143) } }, logDArg := sk156LogDArgCertificate }

private noncomputable def leaf1583InnerLog : WideLogData :=
  innerPair10Data

set_option maxRecDepth 1000000 in
private theorem leaf1583LocalValidity :
    LeafFacts leaf1583Box leaf1583Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1583Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (262145/262143) }) = true
      norm_num [leaf1583Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1583CertificateValid :
    WideCertificateValid leaf1583Box leaf1583Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk156ValidityFacts chi158ValidityFacts
    leaf1583LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1583CoverageChecked :
    coverageCheck (innerAD leaf1583Box) leaf1583InnerLog = true := by
  rfl'

private theorem leaf1583InnerLogValid :
    leaf1583InnerLog.Valid 8 (innerAD leaf1583Box) :=
  wideLogDataValid_of_cachedCheck endpoint3PositiveFacts
    endpoint2PositiveFacts.valid leaf1583CoverageChecked

private noncomputable def leaf1583InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629145/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1583InputLogOnePlusV_eq :
    leaf1583InputLogOnePlusV = outerEnclosure 24
      (leaf1583Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1583RoundedFacts : LeafRoundedFacts 8
    leaf1583Certificate.logOnePlusV leaf1583InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1583InputLogOnePlusV_eq }

private noncomputable def leaf1583Inputs : Inputs :=
  inputsOfCaches globalInput sk156RoundedInputs
    chi158InputQChi innerPair10Input
    leaf1583InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1583LowerChecked :
    lowerCheck 24 leaf1583Box leaf1583Inputs = true := by
  rfl'

private theorem leaf1583CoversExact : CoversExact 8
    leaf1583Box leaf1583Certificate leaf1583InnerLog leaf1583Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk156RoundedFacts chi158RoundedFacts
    innerPair10RoundedFacts leaf1583RoundedFacts (by rfl)

private theorem leaf1583FlatSound : Sound leaf1583Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1583CertificateValid
    leaf1583InnerLogValid leaf1583CoversExact leaf1583LowerChecked

private noncomputable def leaf1584Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (1/64), chiHi := (5/256) }

private noncomputable def leaf1584Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217799/134217728) }, vSqrt := { lower := (8191/8192), upper := (33554560/33554277) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (142048731/134217728) }, upper := { exponent := 0, mantissa := (2203/2048) } }, logOuter := sk155LogOuterCertificate, logK := sk155LogKCertificate, logChi := chi141LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67108837/67108554) } }, logDArg := sk155LogDArgCertificate }

private noncomputable def leaf1584InnerLog : WideLogData :=
  innerPair9Data

set_option maxRecDepth 1000000 in
private theorem leaf1584LocalValidity :
    LeafFacts leaf1584Box leaf1584Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1584Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554560/33554277) }) = true
      norm_num [leaf1584Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1584CertificateValid :
    WideCertificateValid leaf1584Box leaf1584Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk155ValidityFacts chi141ValidityFacts
    leaf1584LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1584CoverageChecked :
    coverageCheck (innerAD leaf1584Box) leaf1584InnerLog = true := by
  rfl'

private theorem leaf1584InnerLogValid :
    leaf1584InnerLog.Valid 8 (innerAD leaf1584Box) :=
  wideLogDataValid_of_cachedCheck endpoint3PositiveFacts
    endpoint1PositiveFacts.valid leaf1584CoverageChecked

private noncomputable def leaf1584InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629151/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1584InputLogOnePlusV_eq :
    leaf1584InputLogOnePlusV = outerEnclosure 24
      (leaf1584Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1584RoundedFacts : LeafRoundedFacts 8
    leaf1584Certificate.logOnePlusV leaf1584InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1584InputLogOnePlusV_eq }

private noncomputable def leaf1584Inputs : Inputs :=
  inputsOfCaches globalInput sk155RoundedInputs
    chi141InputQChi innerPair9Input
    leaf1584InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1584LowerChecked :
    lowerCheck 24 leaf1584Box leaf1584Inputs = true := by
  rfl'

private theorem leaf1584CoversExact : CoversExact 8
    leaf1584Box leaf1584Certificate leaf1584InnerLog leaf1584Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk155RoundedFacts chi141RoundedFacts
    innerPair9RoundedFacts leaf1584RoundedFacts (by rfl)

private theorem leaf1584FlatSound : Sound leaf1584Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1584CertificateValid
    leaf1584InnerLogValid leaf1584CoversExact leaf1584LowerChecked

private noncomputable def leaf1585Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (5/256), chiHi := (3/128) }

private noncomputable def leaf1585Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217801/134217728) }, vSqrt := { lower := (8191/8192), upper := (16777280/16777123) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (144014689/134217728) }, upper := { exponent := 0, mantissa := (1117/1024) } }, logOuter := sk155LogOuterCertificate, logK := sk155LogKCertificate, logChi := chi142LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (33554403/33554246) } }, logDArg := sk155LogDArgCertificate }

private noncomputable def leaf1585InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf1585LocalValidity :
    LeafFacts leaf1585Box leaf1585Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1585Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (16777280/16777123) }) = true
      norm_num [leaf1585Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1585CertificateValid :
    WideCertificateValid leaf1585Box leaf1585Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk155ValidityFacts chi142ValidityFacts
    leaf1585LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1585CoverageChecked :
    coverageCheck (innerAD leaf1585Box) leaf1585InnerLog = true := by
  rfl'

private theorem leaf1585InnerLogValid :
    leaf1585InnerLog.Valid 8 (innerAD leaf1585Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf1585CoverageChecked

private noncomputable def leaf1585InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629159/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1585InputLogOnePlusV_eq :
    leaf1585InputLogOnePlusV = outerEnclosure 24
      (leaf1585Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1585RoundedFacts : LeafRoundedFacts 8
    leaf1585Certificate.logOnePlusV leaf1585InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1585InputLogOnePlusV_eq }

private noncomputable def leaf1585Inputs : Inputs :=
  inputsOfCaches globalInput sk155RoundedInputs
    chi142InputQChi innerPair5Input
    leaf1585InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1585LowerChecked :
    lowerCheck 24 leaf1585Box leaf1585Inputs = true := by
  rfl'

private theorem leaf1585CoversExact : CoversExact 8
    leaf1585Box leaf1585Certificate leaf1585InnerLog leaf1585Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk155RoundedFacts chi142RoundedFacts
    innerPair5RoundedFacts leaf1585RoundedFacts (by rfl)

private theorem leaf1585FlatSound : Sound leaf1585Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1585CertificateValid
    leaf1585InnerLogValid leaf1585CoversExact leaf1585LowerChecked

private noncomputable def leaf1586Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (1/64), chiHi := (5/256) }

private noncomputable def leaf1586Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217801/134217728) }, vSqrt := { lower := (65527/65536), upper := (1048580/1048571) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (142310857/134217728) }, upper := { exponent := 0, mantissa := (69/64) } }, logOuter := sk156LogOuterCertificate, logK := sk156LogKCertificate, logChi := chi141LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (2097151/2097142) } }, logDArg := sk156LogDArgCertificate }

private noncomputable def leaf1586InnerLog : WideLogData :=
  innerPair9Data

set_option maxRecDepth 1000000 in
private theorem leaf1586LocalValidity :
    LeafFacts leaf1586Box leaf1586Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1586Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (1048580/1048571) }) = true
      norm_num [leaf1586Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1586CertificateValid :
    WideCertificateValid leaf1586Box leaf1586Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk156ValidityFacts chi141ValidityFacts
    leaf1586LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1586CoverageChecked :
    coverageCheck (innerAD leaf1586Box) leaf1586InnerLog = true := by
  rfl'

private theorem leaf1586InnerLogValid :
    leaf1586InnerLog.Valid 8 (innerAD leaf1586Box) :=
  wideLogDataValid_of_cachedCheck endpoint3PositiveFacts
    endpoint1PositiveFacts.valid leaf1586CoverageChecked

private noncomputable def leaf1586InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629153/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1586InputLogOnePlusV_eq :
    leaf1586InputLogOnePlusV = outerEnclosure 24
      (leaf1586Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1586RoundedFacts : LeafRoundedFacts 8
    leaf1586Certificate.logOnePlusV leaf1586InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1586InputLogOnePlusV_eq }

private noncomputable def leaf1586Inputs : Inputs :=
  inputsOfCaches globalInput sk156RoundedInputs
    chi141InputQChi innerPair9Input
    leaf1586InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1586LowerChecked :
    lowerCheck 24 leaf1586Box leaf1586Inputs = true := by
  rfl'

private theorem leaf1586CoversExact : CoversExact 8
    leaf1586Box leaf1586Certificate leaf1586InnerLog leaf1586Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk156RoundedFacts chi141RoundedFacts
    innerPair9RoundedFacts leaf1586RoundedFacts (by rfl)

private theorem leaf1586FlatSound : Sound leaf1586Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1586CertificateValid
    leaf1586InnerLogValid leaf1586CoversExact leaf1586LowerChecked

private noncomputable def leaf1587Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (5/256), chiHi := (3/128) }

private noncomputable def leaf1587Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217803/134217728) }, vSqrt := { lower := (65527/65536), upper := (104858/104857) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (144342347/134217728) }, upper := { exponent := 0, mantissa := (35/32) } }, logOuter := sk156LogOuterCertificate, logK := sk156LogKCertificate, logChi := chi142LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (209715/209714) } }, logDArg := sk156LogDArgCertificate }

private noncomputable def leaf1587InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf1587LocalValidity :
    LeafFacts leaf1587Box leaf1587Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1587Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (104858/104857) }) = true
      norm_num [leaf1587Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1587CertificateValid :
    WideCertificateValid leaf1587Box leaf1587Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk156ValidityFacts chi142ValidityFacts
    leaf1587LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1587CoverageChecked :
    coverageCheck (innerAD leaf1587Box) leaf1587InnerLog = true := by
  rfl'

private theorem leaf1587InnerLogValid :
    leaf1587InnerLog.Valid 8 (innerAD leaf1587Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf1587CoverageChecked

private noncomputable def leaf1587InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629161/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1587InputLogOnePlusV_eq :
    leaf1587InputLogOnePlusV = outerEnclosure 24
      (leaf1587Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1587RoundedFacts : LeafRoundedFacts 8
    leaf1587Certificate.logOnePlusV leaf1587InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1587InputLogOnePlusV_eq }

private noncomputable def leaf1587Inputs : Inputs :=
  inputsOfCaches globalInput sk156RoundedInputs
    chi142InputQChi innerPair5Input
    leaf1587InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1587LowerChecked :
    lowerCheck 24 leaf1587Box leaf1587Inputs = true := by
  rfl'

private theorem leaf1587CoversExact : CoversExact 8
    leaf1587Box leaf1587Certificate leaf1587InnerLog leaf1587Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk156RoundedFacts chi142RoundedFacts
    innerPair5RoundedFacts leaf1587RoundedFacts (by rfl)

private theorem leaf1587FlatSound : Sound leaf1587Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1587CertificateValid
    leaf1587InnerLogValid leaf1587CoversExact leaf1587LowerChecked

private noncomputable def leaf1588Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (3/128), chiHi := (7/256) }

private noncomputable def leaf1588Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435591/268435456) }, vSqrt := { lower := (8191/8192), upper := (22369664/22369479) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (291994075/268435456) }, upper := { exponent := 0, mantissa := (4523/4096) } }, logOuter := sk157LogOuterCertificate, logK := sk157LogKCertificate, logChi := chi123LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (44739143/44738958) } }, logDArg := sk157LogDArgCertificate }

private noncomputable def leaf1588InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf1588LocalValidity :
    LeafFacts leaf1588Box leaf1588Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1588Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22369664/22369479) }) = true
      norm_num [leaf1588Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1588CertificateValid :
    WideCertificateValid leaf1588Box leaf1588Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk157ValidityFacts chi123ValidityFacts
    leaf1588LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1588CoverageChecked :
    coverageCheck (innerAD leaf1588Box) leaf1588InnerLog = true := by
  rfl'

private theorem leaf1588InnerLogValid :
    leaf1588InnerLog.Valid 8 (innerAD leaf1588Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf1588CoverageChecked

private noncomputable def leaf1588InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814575/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1588InputLogOnePlusV_eq :
    leaf1588InputLogOnePlusV = outerEnclosure 24
      (leaf1588Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1588RoundedFacts : LeafRoundedFacts 8
    leaf1588Certificate.logOnePlusV leaf1588InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1588InputLogOnePlusV_eq }

private noncomputable def leaf1588Inputs : Inputs :=
  inputsOfCaches globalInput sk157RoundedInputs
    chi123InputQChi innerPair5Input
    leaf1588InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1588LowerChecked :
    lowerCheck 24 leaf1588Box leaf1588Inputs = true := by
  rfl'

private theorem leaf1588CoversExact : CoversExact 8
    leaf1588Box leaf1588Certificate leaf1588InnerLog leaf1588Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk157RoundedFacts chi123RoundedFacts
    innerPair5RoundedFacts leaf1588RoundedFacts (by rfl)

private theorem leaf1588FlatSound : Sound leaf1588Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1588CertificateValid
    leaf1588InnerLogValid leaf1588CoversExact leaf1588LowerChecked

private noncomputable def leaf1589Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (3/128), chiHi := (7/256) }

private noncomputable def leaf1589Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435593/268435456) }, vSqrt := { lower := (8191/8192), upper := (33554496/33554215) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (292387265/268435456) }, upper := { exponent := 0, mantissa := (2265/2048) } }, logOuter := sk158LogOuterCertificate, logK := sk158LogKCertificate, logChi := chi123LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67108711/67108430) } }, logDArg := sk158LogDArgCertificate }

private noncomputable def leaf1589InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf1589LocalValidity :
    LeafFacts leaf1589Box leaf1589Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1589Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554496/33554215) }) = true
      norm_num [leaf1589Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1589CertificateValid :
    WideCertificateValid leaf1589Box leaf1589Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk158ValidityFacts chi123ValidityFacts
    leaf1589LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1589CoverageChecked :
    coverageCheck (innerAD leaf1589Box) leaf1589InnerLog = true := by
  rfl'

private theorem leaf1589InnerLogValid :
    leaf1589InnerLog.Valid 8 (innerAD leaf1589Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf1589CoverageChecked

private noncomputable def leaf1589InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629151/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1589InputLogOnePlusV_eq :
    leaf1589InputLogOnePlusV = outerEnclosure 24
      (leaf1589Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1589RoundedFacts : LeafRoundedFacts 8
    leaf1589Certificate.logOnePlusV leaf1589InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1589InputLogOnePlusV_eq }

private noncomputable def leaf1589Inputs : Inputs :=
  inputsOfCaches globalInput sk158RoundedInputs
    chi123InputQChi innerPair5Input
    leaf1589InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1589LowerChecked :
    lowerCheck 24 leaf1589Box leaf1589Inputs = true := by
  rfl'

private theorem leaf1589CoversExact : CoversExact 8
    leaf1589Box leaf1589Certificate leaf1589InnerLog leaf1589Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk158RoundedFacts chi123RoundedFacts
    innerPair5RoundedFacts leaf1589RoundedFacts (by rfl)

private theorem leaf1589FlatSound : Sound leaf1589Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1589CertificateValid
    leaf1589InnerLogValid leaf1589CoversExact leaf1589LowerChecked

private noncomputable def leaf1590Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (7/256), chiHi := (1/32) }

private noncomputable def leaf1590Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435593/268435456) }, vSqrt := { lower := (8191/8192), upper := (8388624/8388547) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (295925993/268435456) }, upper := { exponent := 0, mantissa := (573/512) } }, logOuter := sk157LogOuterCertificate, logK := sk157LogKCertificate, logChi := chi124LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16777171/16777094) } }, logDArg := sk157LogDArgCertificate }

private noncomputable def leaf1590InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf1590LocalValidity :
    LeafFacts leaf1590Box leaf1590Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1590Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8388624/8388547) }) = true
      norm_num [leaf1590Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1590CertificateValid :
    WideCertificateValid leaf1590Box leaf1590Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk157ValidityFacts chi124ValidityFacts
    leaf1590LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1590CoverageChecked :
    coverageCheck (innerAD leaf1590Box) leaf1590InnerLog = true := by
  rfl'

private theorem leaf1590InnerLogValid :
    leaf1590InnerLog.Valid 8 (innerAD leaf1590Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf1590CoverageChecked

private noncomputable def leaf1590InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814579/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1590InputLogOnePlusV_eq :
    leaf1590InputLogOnePlusV = outerEnclosure 24
      (leaf1590Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1590RoundedFacts : LeafRoundedFacts 8
    leaf1590Certificate.logOnePlusV leaf1590InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1590InputLogOnePlusV_eq }

private noncomputable def leaf1590Inputs : Inputs :=
  inputsOfCaches globalInput sk157RoundedInputs
    chi124InputQChi innerPair5Input
    leaf1590InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1590LowerChecked :
    lowerCheck 24 leaf1590Box leaf1590Inputs = true := by
  rfl'

private theorem leaf1590CoversExact : CoversExact 8
    leaf1590Box leaf1590Certificate leaf1590InnerLog leaf1590Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk157RoundedFacts chi124RoundedFacts
    innerPair5RoundedFacts leaf1590RoundedFacts (by rfl)

private theorem leaf1590FlatSound : Sound leaf1590Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1590CertificateValid
    leaf1590InnerLogValid leaf1590CoversExact leaf1590LowerChecked

private noncomputable def leaf1591Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (7/256), chiHi := (1/32) }

private noncomputable def leaf1591Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435595/268435456) }, vSqrt := { lower := (8191/8192), upper := (1398104/1398091) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (296384715/268435456) }, upper := { exponent := 0, mantissa := (287/256) } }, logOuter := sk158LogOuterCertificate, logK := sk158LogKCertificate, logChi := chi124LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (2796195/2796182) } }, logDArg := sk158LogDArgCertificate }

private noncomputable def leaf1591InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf1591LocalValidity :
    LeafFacts leaf1591Box leaf1591Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1591Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (1398104/1398091) }) = true
      norm_num [leaf1591Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1591CertificateValid :
    WideCertificateValid leaf1591Box leaf1591Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk158ValidityFacts chi124ValidityFacts
    leaf1591LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1591CoverageChecked :
    coverageCheck (innerAD leaf1591Box) leaf1591InnerLog = true := by
  rfl'

private theorem leaf1591InnerLogValid :
    leaf1591InnerLog.Valid 8 (innerAD leaf1591Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf1591CoverageChecked

private noncomputable def leaf1591InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629159/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1591InputLogOnePlusV_eq :
    leaf1591InputLogOnePlusV = outerEnclosure 24
      (leaf1591Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1591RoundedFacts : LeafRoundedFacts 8
    leaf1591Certificate.logOnePlusV leaf1591InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1591InputLogOnePlusV_eq }

private noncomputable def leaf1591Inputs : Inputs :=
  inputsOfCaches globalInput sk158RoundedInputs
    chi124InputQChi innerPair5Input
    leaf1591InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1591LowerChecked :
    lowerCheck 24 leaf1591Box leaf1591Inputs = true := by
  rfl'

private theorem leaf1591CoversExact : CoversExact 8
    leaf1591Box leaf1591Certificate leaf1591InnerLog leaf1591Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk158RoundedFacts chi124RoundedFacts
    innerPair5RoundedFacts leaf1591RoundedFacts (by rfl)

private theorem leaf1591FlatSound : Sound leaf1591Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1591CertificateValid
    leaf1591InnerLogValid leaf1591CoversExact leaf1591LowerChecked

private noncomputable def leaf1592Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (3/128), chiHi := (7/256) }

private noncomputable def leaf1592Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435595/268435456) }, vSqrt := { lower := (8191/8192), upper := (67108992/67108423) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (292780455/268435456) }, upper := { exponent := 0, mantissa := (4537/4096) } }, logOuter := sk159LogOuterCertificate, logK := sk159LogKCertificate, logChi := chi123LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134217415/134216846) } }, logDArg := sk159LogDArgCertificate }

private noncomputable def leaf1592InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf1592LocalValidity :
    LeafFacts leaf1592Box leaf1592Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1592Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108992/67108423) }) = true
      norm_num [leaf1592Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1592CertificateValid :
    WideCertificateValid leaf1592Box leaf1592Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk159ValidityFacts chi123ValidityFacts
    leaf1592LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1592CoverageChecked :
    coverageCheck (innerAD leaf1592Box) leaf1592InnerLog = true := by
  rfl'

private theorem leaf1592InnerLogValid :
    leaf1592InnerLog.Valid 8 (innerAD leaf1592Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf1592CoverageChecked

private noncomputable def leaf1592InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (363411/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf1592InputLogOnePlusV_eq :
    leaf1592InputLogOnePlusV = outerEnclosure 24
      (leaf1592Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1592RoundedFacts : LeafRoundedFacts 8
    leaf1592Certificate.logOnePlusV leaf1592InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1592InputLogOnePlusV_eq }

private noncomputable def leaf1592Inputs : Inputs :=
  inputsOfCaches globalInput sk159RoundedInputs
    chi123InputQChi innerPair5Input
    leaf1592InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1592LowerChecked :
    lowerCheck 24 leaf1592Box leaf1592Inputs = true := by
  rfl'

private theorem leaf1592CoversExact : CoversExact 8
    leaf1592Box leaf1592Certificate leaf1592InnerLog leaf1592Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk159RoundedFacts chi123RoundedFacts
    innerPair5RoundedFacts leaf1592RoundedFacts (by rfl)

private theorem leaf1592FlatSound : Sound leaf1592Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1592CertificateValid
    leaf1592InnerLogValid leaf1592CoversExact leaf1592LowerChecked

private noncomputable def leaf1593Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (3/128), chiHi := (7/256) }

private noncomputable def leaf1593Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435597/268435456) }, vSqrt := { lower := (65527/65536), upper := (349526/349523) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (293173645/268435456) }, upper := { exponent := 0, mantissa := (71/64) } }, logOuter := sk160LogOuterCertificate, logK := sk160LogKCertificate, logChi := chi123LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (699049/699046) } }, logDArg := sk160LogDArgCertificate }

private noncomputable def leaf1593InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf1593LocalValidity :
    LeafFacts leaf1593Box leaf1593Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1593Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (349526/349523) }) = true
      norm_num [leaf1593Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1593CertificateValid :
    WideCertificateValid leaf1593Box leaf1593Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk160ValidityFacts chi123ValidityFacts
    leaf1593LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1593CoverageChecked :
    coverageCheck (innerAD leaf1593Box) leaf1593InnerLog = true := by
  rfl'

private theorem leaf1593InnerLogValid :
    leaf1593InnerLog.Valid 8 (innerAD leaf1593Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf1593CoverageChecked

private noncomputable def leaf1593InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629153/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1593InputLogOnePlusV_eq :
    leaf1593InputLogOnePlusV = outerEnclosure 24
      (leaf1593Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1593RoundedFacts : LeafRoundedFacts 8
    leaf1593Certificate.logOnePlusV leaf1593InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1593InputLogOnePlusV_eq }

private noncomputable def leaf1593Inputs : Inputs :=
  inputsOfCaches globalInput sk160RoundedInputs
    chi123InputQChi innerPair5Input
    leaf1593InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1593LowerChecked :
    lowerCheck 24 leaf1593Box leaf1593Inputs = true := by
  rfl'

private theorem leaf1593CoversExact : CoversExact 8
    leaf1593Box leaf1593Certificate leaf1593InnerLog leaf1593Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk160RoundedFacts chi123RoundedFacts
    innerPair5RoundedFacts leaf1593RoundedFacts (by rfl)

private theorem leaf1593FlatSound : Sound leaf1593Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1593CertificateValid
    leaf1593InnerLogValid leaf1593CoversExact leaf1593LowerChecked

private noncomputable def leaf1594Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (7/256), chiHi := (1/32) }

private noncomputable def leaf1594Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435597/268435456) }, vSqrt := { lower := (8191/8192), upper := (8388624/8388545) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (296843437/268435456) }, upper := { exponent := 0, mantissa := (575/512) } }, logOuter := sk159LogOuterCertificate, logK := sk159LogKCertificate, logChi := chi124LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16777169/16777090) } }, logDArg := sk159LogDArgCertificate }

private noncomputable def leaf1594InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf1594LocalValidity :
    LeafFacts leaf1594Box leaf1594Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1594Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8388624/8388545) }) = true
      norm_num [leaf1594Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1594CertificateValid :
    WideCertificateValid leaf1594Box leaf1594Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk159ValidityFacts chi124ValidityFacts
    leaf1594LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1594CoverageChecked :
    coverageCheck (innerAD leaf1594Box) leaf1594InnerLog = true := by
  rfl'

private theorem leaf1594InnerLogValid :
    leaf1594InnerLog.Valid 8 (innerAD leaf1594Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf1594CoverageChecked

private noncomputable def leaf1594InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453645/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1594InputLogOnePlusV_eq :
    leaf1594InputLogOnePlusV = outerEnclosure 24
      (leaf1594Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1594RoundedFacts : LeafRoundedFacts 8
    leaf1594Certificate.logOnePlusV leaf1594InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1594InputLogOnePlusV_eq }

private noncomputable def leaf1594Inputs : Inputs :=
  inputsOfCaches globalInput sk159RoundedInputs
    chi124InputQChi innerPair5Input
    leaf1594InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1594LowerChecked :
    lowerCheck 24 leaf1594Box leaf1594Inputs = true := by
  rfl'

private theorem leaf1594CoversExact : CoversExact 8
    leaf1594Box leaf1594Certificate leaf1594InnerLog leaf1594Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk159RoundedFacts chi124RoundedFacts
    innerPair5RoundedFacts leaf1594RoundedFacts (by rfl)

private theorem leaf1594FlatSound : Sound leaf1594Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1594CertificateValid
    leaf1594InnerLogValid leaf1594CoversExact leaf1594LowerChecked

private noncomputable def leaf1595Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (7/256), chiHi := (1/32) }

private noncomputable def leaf1595Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435599/268435456) }, vSqrt := { lower := (65527/65536), upper := (524289/524284) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (297302159/268435456) }, upper := { exponent := 0, mantissa := (9/8) } }, logOuter := sk160LogOuterCertificate, logK := sk160LogKCertificate, logChi := chi124LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (1048573/1048568) } }, logDArg := sk160LogDArgCertificate }

private noncomputable def leaf1595InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf1595LocalValidity :
    LeafFacts leaf1595Box leaf1595Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1595Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (524289/524284) }) = true
      norm_num [leaf1595Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1595CertificateValid :
    WideCertificateValid leaf1595Box leaf1595Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk160ValidityFacts chi124ValidityFacts
    leaf1595LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1595CoverageChecked :
    coverageCheck (innerAD leaf1595Box) leaf1595InnerLog = true := by
  rfl'

private theorem leaf1595InnerLogValid :
    leaf1595InnerLog.Valid 8 (innerAD leaf1595Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf1595CoverageChecked

private noncomputable def leaf1595InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629161/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1595InputLogOnePlusV_eq :
    leaf1595InputLogOnePlusV = outerEnclosure 24
      (leaf1595Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1595RoundedFacts : LeafRoundedFacts 8
    leaf1595Certificate.logOnePlusV leaf1595InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1595InputLogOnePlusV_eq }

private noncomputable def leaf1595Inputs : Inputs :=
  inputsOfCaches globalInput sk160RoundedInputs
    chi124InputQChi innerPair5Input
    leaf1595InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1595LowerChecked :
    lowerCheck 24 leaf1595Box leaf1595Inputs = true := by
  rfl'

private theorem leaf1595CoversExact : CoversExact 8
    leaf1595Box leaf1595Certificate leaf1595InnerLog leaf1595Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk160RoundedFacts chi124RoundedFacts
    innerPair5RoundedFacts leaf1595RoundedFacts (by rfl)

private theorem leaf1595FlatSound : Sound leaf1595Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1595CertificateValid
    leaf1595InnerLogValid leaf1595CoversExact leaf1595LowerChecked

private noncomputable def component36Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (15/4), chiLo := (0), chiHi := (1/128) }

set_option maxRecDepth 1000000 in
private theorem component36Node0_sound : Sound component36Node0Box :=
  sound_of_literal_split component36Node0Box leaf1565Box leaf1566Box
    .k (29/8) (by rfl) (by rfl)
    leaf1565FlatSound leaf1566FlatSound

private noncomputable def component36Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (15/4), chiLo := (1/128), chiHi := (1/64) }

set_option maxRecDepth 1000000 in
private theorem component36Node1_sound : Sound component36Node1Box :=
  sound_of_literal_split component36Node1Box leaf1567Box leaf1568Box
    .k (29/8) (by rfl) (by rfl)
    leaf1567FlatSound leaf1568FlatSound

private noncomputable def component36Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (15/4), chiLo := (0), chiHi := (1/64) }

set_option maxRecDepth 1000000 in
private theorem component36Node2_sound : Sound component36Node2Box :=
  sound_of_literal_split component36Node2Box component36Node0Box component36Node1Box
    .chi (1/128) (by rfl) (by rfl)
    component36Node0_sound component36Node1_sound

private noncomputable def component36Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (1/64), chiHi := (3/128) }

set_option maxRecDepth 1000000 in
private theorem component36Node3_sound : Sound component36Node3Box :=
  sound_of_literal_split component36Node3Box leaf1569Box leaf1570Box
    .chi (5/256) (by rfl) (by rfl)
    leaf1569FlatSound leaf1570FlatSound

private noncomputable def component36Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (1/64), chiHi := (3/128) }

set_option maxRecDepth 1000000 in
private theorem component36Node4_sound : Sound component36Node4Box :=
  sound_of_literal_split component36Node4Box leaf1571Box leaf1572Box
    .chi (5/256) (by rfl) (by rfl)
    leaf1571FlatSound leaf1572FlatSound

private noncomputable def component36Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (15/4), chiLo := (1/64), chiHi := (3/128) }

set_option maxRecDepth 1000000 in
private theorem component36Node5_sound : Sound component36Node5Box :=
  sound_of_literal_split component36Node5Box component36Node3Box component36Node4Box
    .k (29/8) (by rfl) (by rfl)
    component36Node3_sound component36Node4_sound

private noncomputable def component36Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (7/256), chiHi := (1/32) }

set_option maxRecDepth 1000000 in
private theorem component36Node6_sound : Sound component36Node6Box :=
  sound_of_literal_split component36Node6Box leaf1574Box leaf1575Box
    .k (57/16) (by rfl) (by rfl)
    leaf1574FlatSound leaf1575FlatSound

private noncomputable def component36Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (3/128), chiHi := (1/32) }

set_option maxRecDepth 1000000 in
private theorem component36Node7_sound : Sound component36Node7Box :=
  sound_of_literal_split component36Node7Box leaf1573Box component36Node6Box
    .chi (7/256) (by rfl) (by rfl)
    leaf1573FlatSound component36Node6_sound

private noncomputable def component36Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (7/256), chiHi := (1/32) }

set_option maxRecDepth 1000000 in
private theorem component36Node8_sound : Sound component36Node8Box :=
  sound_of_literal_split component36Node8Box leaf1577Box leaf1578Box
    .k (59/16) (by rfl) (by rfl)
    leaf1577FlatSound leaf1578FlatSound

private noncomputable def component36Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (3/128), chiHi := (1/32) }

set_option maxRecDepth 1000000 in
private theorem component36Node9_sound : Sound component36Node9Box :=
  sound_of_literal_split component36Node9Box leaf1576Box component36Node8Box
    .chi (7/256) (by rfl) (by rfl)
    leaf1576FlatSound component36Node8_sound

private noncomputable def component36Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (15/4), chiLo := (3/128), chiHi := (1/32) }

set_option maxRecDepth 1000000 in
private theorem component36Node10_sound : Sound component36Node10Box :=
  sound_of_literal_split component36Node10Box component36Node7Box component36Node9Box
    .k (29/8) (by rfl) (by rfl)
    component36Node7_sound component36Node9_sound

private noncomputable def component36Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (15/4), chiLo := (1/64), chiHi := (1/32) }

set_option maxRecDepth 1000000 in
private theorem component36Node11_sound : Sound component36Node11Box :=
  sound_of_literal_split component36Node11Box component36Node5Box component36Node10Box
    .chi (3/128) (by rfl) (by rfl)
    component36Node5_sound component36Node10_sound

private noncomputable def component36Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (15/4), chiLo := (0), chiHi := (1/32) }

set_option maxRecDepth 1000000 in
private theorem component36Node12_sound : Sound component36Node12Box :=
  sound_of_literal_split component36Node12Box component36Node2Box component36Node11Box
    .chi (1/64) (by rfl) (by rfl)
    component36Node2_sound component36Node11_sound

private noncomputable def component36Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (4), chiLo := (0), chiHi := (1/128) }

set_option maxRecDepth 1000000 in
private theorem component36Node13_sound : Sound component36Node13Box :=
  sound_of_literal_split component36Node13Box leaf1579Box leaf1580Box
    .k (31/8) (by rfl) (by rfl)
    leaf1579FlatSound leaf1580FlatSound

private noncomputable def component36Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (1/128), chiHi := (1/64) }

set_option maxRecDepth 1000000 in
private theorem component36Node14_sound : Sound component36Node14Box :=
  sound_of_literal_split component36Node14Box leaf1582Box leaf1583Box
    .chi (3/256) (by rfl) (by rfl)
    leaf1582FlatSound leaf1583FlatSound

private noncomputable def component36Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (4), chiLo := (1/128), chiHi := (1/64) }

set_option maxRecDepth 1000000 in
private theorem component36Node15_sound : Sound component36Node15Box :=
  sound_of_literal_split component36Node15Box leaf1581Box component36Node14Box
    .k (31/8) (by rfl) (by rfl)
    leaf1581FlatSound component36Node14_sound

private noncomputable def component36Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (4), chiLo := (0), chiHi := (1/64) }

set_option maxRecDepth 1000000 in
private theorem component36Node16_sound : Sound component36Node16Box :=
  sound_of_literal_split component36Node16Box component36Node13Box component36Node15Box
    .chi (1/128) (by rfl) (by rfl)
    component36Node13_sound component36Node15_sound

private noncomputable def component36Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (1/64), chiHi := (3/128) }

set_option maxRecDepth 1000000 in
private theorem component36Node17_sound : Sound component36Node17Box :=
  sound_of_literal_split component36Node17Box leaf1584Box leaf1585Box
    .chi (5/256) (by rfl) (by rfl)
    leaf1584FlatSound leaf1585FlatSound

private noncomputable def component36Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (1/64), chiHi := (3/128) }

set_option maxRecDepth 1000000 in
private theorem component36Node18_sound : Sound component36Node18Box :=
  sound_of_literal_split component36Node18Box leaf1586Box leaf1587Box
    .chi (5/256) (by rfl) (by rfl)
    leaf1586FlatSound leaf1587FlatSound

private noncomputable def component36Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (4), chiLo := (1/64), chiHi := (3/128) }

set_option maxRecDepth 1000000 in
private theorem component36Node19_sound : Sound component36Node19Box :=
  sound_of_literal_split component36Node19Box component36Node17Box component36Node18Box
    .k (31/8) (by rfl) (by rfl)
    component36Node17_sound component36Node18_sound

private noncomputable def component36Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (3/128), chiHi := (7/256) }

set_option maxRecDepth 1000000 in
private theorem component36Node20_sound : Sound component36Node20Box :=
  sound_of_literal_split component36Node20Box leaf1588Box leaf1589Box
    .k (61/16) (by rfl) (by rfl)
    leaf1588FlatSound leaf1589FlatSound

private noncomputable def component36Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (7/256), chiHi := (1/32) }

set_option maxRecDepth 1000000 in
private theorem component36Node21_sound : Sound component36Node21Box :=
  sound_of_literal_split component36Node21Box leaf1590Box leaf1591Box
    .k (61/16) (by rfl) (by rfl)
    leaf1590FlatSound leaf1591FlatSound

private noncomputable def component36Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (3/128), chiHi := (1/32) }

set_option maxRecDepth 1000000 in
private theorem component36Node22_sound : Sound component36Node22Box :=
  sound_of_literal_split component36Node22Box component36Node20Box component36Node21Box
    .chi (7/256) (by rfl) (by rfl)
    component36Node20_sound component36Node21_sound

private noncomputable def component36Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (3/128), chiHi := (7/256) }

set_option maxRecDepth 1000000 in
private theorem component36Node23_sound : Sound component36Node23Box :=
  sound_of_literal_split component36Node23Box leaf1592Box leaf1593Box
    .k (63/16) (by rfl) (by rfl)
    leaf1592FlatSound leaf1593FlatSound

private noncomputable def component36Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (7/256), chiHi := (1/32) }

set_option maxRecDepth 1000000 in
private theorem component36Node24_sound : Sound component36Node24Box :=
  sound_of_literal_split component36Node24Box leaf1594Box leaf1595Box
    .k (63/16) (by rfl) (by rfl)
    leaf1594FlatSound leaf1595FlatSound

private noncomputable def component36Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (3/128), chiHi := (1/32) }

set_option maxRecDepth 1000000 in
private theorem component36Node25_sound : Sound component36Node25Box :=
  sound_of_literal_split component36Node25Box component36Node23Box component36Node24Box
    .chi (7/256) (by rfl) (by rfl)
    component36Node23_sound component36Node24_sound

private noncomputable def component36Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (4), chiLo := (3/128), chiHi := (1/32) }

set_option maxRecDepth 1000000 in
private theorem component36Node26_sound : Sound component36Node26Box :=
  sound_of_literal_split component36Node26Box component36Node22Box component36Node25Box
    .k (31/8) (by rfl) (by rfl)
    component36Node22_sound component36Node25_sound

private noncomputable def component36Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (4), chiLo := (1/64), chiHi := (1/32) }

set_option maxRecDepth 1000000 in
private theorem component36Node27_sound : Sound component36Node27Box :=
  sound_of_literal_split component36Node27Box component36Node19Box component36Node26Box
    .chi (3/128) (by rfl) (by rfl)
    component36Node19_sound component36Node26_sound

private noncomputable def component36Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (4), chiLo := (0), chiHi := (1/32) }

set_option maxRecDepth 1000000 in
private theorem component36Node28_sound : Sound component36Node28Box :=
  sound_of_literal_split component36Node28Box component36Node16Box component36Node27Box
    .chi (1/64) (by rfl) (by rfl)
    component36Node16_sound component36Node27_sound

noncomputable def component36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (4), chiLo := (0), chiHi := (1/32) }

set_option maxRecDepth 1000000 in
theorem component36_sound : Sound component36Box :=
  sound_of_literal_split component36Box component36Node12Box component36Node28Box
    .k (15/4) (by rfl) (by rfl)
    component36Node12_sound component36Node28_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
